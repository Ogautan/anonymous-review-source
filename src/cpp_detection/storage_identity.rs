//! Declaration-bound identities for native arrays. An unresolved alias is not
//! a license to join findings by spelling. Build once and query by source site.
use super::{ParsedCppFile, declarator_variable_name, node_text, walk_nodes};
use std::collections::HashMap;

#[derive(Clone)]
struct Declaration {
    file: String,
    line: usize,
    start: usize,
    end: usize,
    local: bool,
    member: bool,
    array: bool,
    external: bool,
    internal: bool,
}

pub(super) struct StorageIndex {
    declarations: HashMap<(String, String), Vec<Declaration>>,
    definitions: HashMap<String, Vec<Declaration>>,
    includes: HashMap<String, Vec<(String, usize)>>,
    accesses: HashMap<(String, usize, String), Option<String>>,
}

impl StorageIndex {
    pub(super) fn new(files: &[ParsedCppFile]) -> Self {
        let mut result = Self {
            declarations: HashMap::new(),
            definitions: HashMap::new(),
            accesses: HashMap::new(),
            includes: HashMap::new(),
        };
        let known_files = files
            .iter()
            .map(|f| f.path.as_str())
            .collect::<std::collections::HashSet<_>>();
        for file in files {
            let Some(tree) = &file.tree else { continue };
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() == "preproc_include"
                    && let Some(path) = node.child_by_field_name("path")
                {
                    let text = node_text(path, &file.source);
                    if let Some(relative) = text.strip_prefix('"').and_then(|s| s.strip_suffix('"'))
                    {
                        let path = std::path::Path::new(&file.path)
                            .parent()
                            .unwrap_or(std::path::Path::new("."))
                            .join(relative);
                        let path = std::fs::canonicalize(&path)
                            .unwrap_or(path)
                            .to_string_lossy()
                            .into_owned();
                        if known_files.contains(path.as_str()) {
                            result
                                .includes
                                .entry(file.path.clone())
                                .or_default()
                                .push((path, node.start_position().row + 1));
                        }
                    }
                }
                if !matches!(
                    node.kind(),
                    "declaration" | "parameter_declaration" | "field_declaration"
                ) {
                    return;
                }
                let mut scope = node.parent();
                let mut range = (0, usize::MAX);
                let mut local = false;
                let mut unsupported = false;
                while let Some(parent) = scope {
                    if matches!(
                        parent.kind(),
                        "compound_statement"
                            | "function_definition"
                            | "lambda_expression"
                            | "class_specifier"
                            | "struct_specifier"
                            | "union_specifier"
                            | "namespace_definition"
                    ) {
                        local = true;
                        range = (
                            parent.start_position().row + 1,
                            parent.end_position().row + 1,
                        );
                        unsupported = matches!(
                            parent.kind(),
                            "namespace_definition"
                                | "class_specifier"
                                | "struct_specifier"
                                | "union_specifier"
                        );
                        break;
                    }
                    scope = parent.parent();
                }
                let text = node_text(node, &file.source);
                let tokens = super::identifier_tokens(text).collect::<Vec<_>>();
                for decl in node.children_by_field_name("declarator", &mut node.walk()) {
                    let Some(name) = declarator_variable_name(decl, &file.source) else {
                        continue;
                    };
                    let mut array = false;
                    walk_nodes(decl, &mut |child| {
                        if child.kind() == "array_declarator"
                            && child
                                .child_by_field_name("declarator")
                                .is_some_and(|n| n.kind() == "identifier")
                        {
                            array = true;
                        }
                    });
                    let declaration = Declaration {
                        file: file.path.clone(),
                        line: node.start_position().row + 1,
                        start: range.0,
                        end: range.1,
                        local,
                        member: node.kind() == "field_declaration",
                        array: array && !unsupported && node.kind() != "parameter_declaration",
                        external: tokens.contains(&"extern"),
                        internal: tokens.contains(&"static") || tokens.contains(&"const"),
                    };
                    if !local && declaration.array && !declaration.external && !declaration.internal
                    {
                        result
                            .definitions
                            .entry(name.clone())
                            .or_default()
                            .push(declaration.clone());
                    }
                    result
                        .declarations
                        .entry((file.path.clone(), name))
                        .or_default()
                        .push(declaration);
                }
            });
        }
        for file in files {
            let Some(tree) = &file.tree else { continue };
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() != "subscript_expression" {
                    return;
                }
                let Some(base) = node.child_by_field_name("argument") else {
                    return;
                };
                if base.kind() != "identifier" {
                    return;
                }
                // Out-of-line member bodies may refer to implicit members;
                // a coincident global spelling is not a receiver binding.
                let mut parent = node.parent();
                while let Some(ancestor) = parent {
                    if ancestor.kind() == "function_definition" {
                        if ancestor
                            .child_by_field_name("declarator")
                            .is_some_and(|d| node_text(d, &file.source).contains("::"))
                        {
                            return;
                        }
                        break;
                    }
                    parent = ancestor.parent();
                }
                let name = node_text(base, &file.source);
                let line = node.start_position().row + 1;
                let identity = result.visible(&file.path, line, name);
                result
                    .accesses
                    .entry((file.path.clone(), line, name.into()))
                    .and_modify(|previous| {
                        if *previous != identity {
                            *previous = None;
                        }
                    })
                    .or_insert(identity);
            });
        }
        result
    }

    pub(super) fn definition(&self, file: &str, name: &str) -> Option<(usize, String)> {
        let declarations = self.declarations.get(&(file.into(), name.into()))?;
        let definitions = declarations
            .iter()
            .filter(|d| d.array && !d.external && !d.local)
            .collect::<Vec<_>>();
        let [decl] = definitions.as_slice() else {
            return None;
        };
        Some((decl.line, format!("{}::{name}@{}", decl.file, decl.line)))
    }

    pub(super) fn access(&self, file: &str, line: usize, name: &str) -> Option<String> {
        self.accesses
            .get(&(file.into(), line, name.into()))
            .cloned()
            .flatten()
    }

    pub(super) fn visible(&self, file: &str, line: usize, name: &str) -> Option<String> {
        let declarations = self
            .declarations
            .get(&(file.into(), name.into()))
            .map(Vec::as_slice)
            .unwrap_or_default();
        let visible = declarations
            .iter()
            .filter(|decl| {
                decl.start <= line && line <= decl.end && (decl.member || decl.line <= line)
            })
            .collect::<Vec<_>>();
        // Shadowing includes parameters, scalars and members, not only arrays.
        let locals = visible.iter().filter(|decl| decl.local).collect::<Vec<_>>();
        if !locals.is_empty() {
            // Ambiguous/nested scopes are left unresolved; do not guess an alias.
            let [decl] = locals.as_slice() else {
                return None;
            };
            return (decl.array && !decl.external)
                .then(|| format!("{}::{name}@{}", decl.file, decl.line));
        }
        let definitions = visible
            .iter()
            .filter(|decl| !decl.external)
            .collect::<Vec<_>>();
        if let [decl] = definitions.as_slice() {
            return decl
                .array
                .then(|| format!("{}::{name}@{}", decl.file, decl.line));
        }
        if !definitions.is_empty() {
            return None;
        }
        let [decl] = self.definitions.get(name)?.as_slice() else {
            return None;
        };
        if !visible.iter().any(|decl| decl.external && decl.array)
            && !self.header_extern(file, line, name)
        {
            return None;
        }
        Some(format!("{}::{name}@{}", decl.file, decl.line))
    }

    fn header_extern(&self, file: &str, line: usize, name: &str) -> bool {
        let mut pending = self
            .includes
            .get(file)
            .into_iter()
            .flatten()
            .filter(|(_, include_line)| *include_line <= line)
            .map(|(file, _)| file.as_str())
            .collect::<Vec<_>>();
        let mut visited = std::collections::HashSet::new();
        let mut found = false;
        while let Some(header) = pending.pop() {
            if !visited.insert(header) {
                continue;
            }
            for decl in self
                .declarations
                .get(&(header.into(), name.into()))
                .into_iter()
                .flatten()
                .filter(|d| !d.local)
            {
                // Header definitions (especially static arrays) have translation
                // unit dependent identity; this resolver only imports externs.
                if !decl.external || !decl.array {
                    return false;
                }
                found = true;
            }
            pending.extend(
                self.includes
                    .get(header)
                    .into_iter()
                    .flatten()
                    .map(|(file, _)| file.as_str()),
            );
        }
        found
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpp_detection::{parser::parse_cpp_files, types::CppFile};

    fn index(sources: &[(&str, &str)]) -> StorageIndex {
        StorageIndex::new(&parse_cpp_files(
            sources
                .iter()
                .map(|(file, source)| CppFile {
                    path: file.to_string(),
                    source: source.to_string(),
                })
                .collect(),
        ))
    }

    #[test]
    fn parameters_members_and_local_scalars_do_not_bind_to_global_arrays() {
        for source in [
            "int slots[8];\nvoid run(int *slots) { slots[1]++; }",
            "int slots[8];\nvoid run(int slots[]) { slots[1]++; }",
            "int slots[8];\nvoid run() { int *slots; slots[1]++; }",
            "int slots[8];\nstruct Owner { void run() { slots[1]++; } int *slots; };",
            "int slots[8];\nvoid Owner::run() { slots[1]++; }",
        ] {
            assert_eq!(
                index(&[("x.cpp", source)]).access("x.cpp", 2, "slots"),
                None,
                "{source}"
            );
        }
    }

    #[test]
    fn extern_requires_one_visible_external_definition() {
        let use_site = "extern int slots[8];\nvoid run() { slots[1]++; }";
        for sources in [
            vec![("use.cpp", use_site), ("a.cpp", "static int slots[8];")],
            vec![
                ("use.cpp", use_site),
                ("a.cpp", "int slots[8];"),
                ("b.cpp", "int slots[8];"),
            ],
            vec![
                ("use.cpp", "void run() { slots[1]++; }"),
                ("a.cpp", "int slots[8];"),
            ],
        ] {
            assert_eq!(index(&sources).access("use.cpp", 2, "slots"), None);
        }
        assert_eq!(
            index(&[("use.cpp", use_site), ("a.cpp", "int slots[8];")])
                .access("use.cpp", 2, "slots"),
            Some("a.cpp::slots@1".into())
        );
    }

    #[test]
    fn different_local_array_declarations_keep_separate_identities() {
        let index = index(&[(
            "a.cpp",
            "void one() { int slots[8]; slots[1]++; }\nvoid two() { int slots[8]; slots[1]++; }",
        )]);
        assert_eq!(
            index.access("a.cpp", 1, "slots"),
            Some("a.cpp::slots@1".into())
        );
        assert_eq!(
            index.access("a.cpp", 2, "slots"),
            Some("a.cpp::slots@2".into())
        );
    }
}
