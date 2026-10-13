//! Bounded source-level type binding, without treating a project-wide spelling
//! match as visibility. Only quoted, uniquely resolved project includes enter
//! the environment; unknown conditional declarations shadow rather than bind.
use crate::cpp_detection::parser::CodeChildren;
use std::collections::{HashMap, HashSet};
use std::path::{Component, Path, PathBuf};

use tree_sitter::Node;

use super::layout::scalar_type_size;
use super::parser::{ParsedCppFile, node_text};

pub(super) type RecordAliases = HashMap<(String, usize), HashMap<String, String>>;

#[derive(Clone)]
struct Binding {
    target: String,
    alias: bool,
}

struct Resolver<'a> {
    files: &'a [ParsedCppFile],
    paths: HashMap<PathBuf, usize>,
    suffixes: HashMap<PathBuf, Option<usize>>,
}

pub(super) fn record_aliases(files: &[ParsedCppFile]) -> RecordAliases {
    let mut resolver = Resolver {
        files,
        paths: HashMap::new(),
        suffixes: HashMap::new(),
    };
    for (i, file) in files.iter().enumerate() {
        let path = normalize(Path::new(&file.path));
        resolver.paths.insert(path.clone(), i);
        let components = path
            .components()
            .filter_map(|c| match c {
                Component::Normal(s) => Some(s),
                _ => None,
            })
            .collect::<Vec<_>>();
        // Avoid quadratic storage for arbitrary absolute directory prefixes.
        for start in components.len().saturating_sub(8)..components.len() {
            let suffix: PathBuf = components[start..].iter().collect();
            resolver
                .suffixes
                .entry(suffix)
                .and_modify(|v| {
                    if *v != Some(i) {
                        *v = None;
                    }
                })
                .or_insert(Some(i));
        }
    }
    let mut result = RecordAliases::new();
    for (i, file) in files.iter().enumerate() {
        let Some(tree) = &file.tree else {
            continue;
        };
        let mut walk = Environment {
            resolver: &resolver,
            root: i,
            types: HashMap::new(),
            visited: HashSet::from([i]),
            snapshots: RecordAliases::new(),
            exhausted: false,
        };
        walk.visit(tree.root_node(), i, "", 0, false);
        // A truncated include traversal may have missed a later shadowing
        // declaration. Keep the legacy local-only analysis in that case.
        if !walk.exhausted {
            result.extend(walk.snapshots);
        }
    }
    result
}

fn normalize(path: &Path) -> PathBuf {
    let mut result = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                result.pop();
            }
            c => result.push(c.as_os_str()),
        }
    }
    result
}

impl Resolver<'_> {
    fn included(&self, file: usize, name: &str) -> Option<usize> {
        let parent = Path::new(&self.files[file].path).parent()?;
        let relative = normalize(&parent.join(name));
        self.paths
            .get(&relative)
            .copied()
            .or_else(|| self.suffixes.get(Path::new(name)).copied().flatten())
    }
}

struct Environment<'a, 'b> {
    resolver: &'a Resolver<'b>,
    root: usize,
    types: HashMap<String, Binding>,
    visited: HashSet<usize>,
    snapshots: RecordAliases,
    exhausted: bool,
}

fn qualified(scope: &str, name: &str) -> String {
    if scope.is_empty() {
        name.trim_start_matches("::").to_string()
    } else {
        format!("{scope}::{name}")
    }
}

fn scopes(scope: &str) -> Vec<&str> {
    let mut result = vec![scope];
    let mut next = scope;
    while let Some((parent, _)) = next.rsplit_once("::") {
        result.push(parent);
        next = parent;
    }
    if !scope.is_empty() {
        result.push("");
    }
    result
}

/// Replace the nominal base only; preserve cv qualifiers, template arguments,
/// pointer/reference layers and the named declarator retained by the parser.
pub(super) fn substitute(ty: &str, lookup: impl Fn(&str) -> Option<String>) -> String {
    let start = ty.char_indices().find_map(|(i, c)| {
        if !c.is_ascii_alphabetic() && c != '_' && c != ':' {
            return None;
        }
        if i > 0 && ty.as_bytes()[i - 1].is_ascii_alphanumeric() {
            return None;
        }
        let word = ty[i..]
            .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .next()
            .unwrap_or("");
        (!matches!(
            word,
            "const" | "volatile" | "mutable" | "struct" | "class" | "typename" | "constexpr"
        ))
        .then_some(i)
    });
    let Some(start) = start else {
        return ty.to_string();
    };
    let end = ty[start..]
        .find(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != ':')
        .map_or(ty.len(), |i| start + i);
    let nominal = &ty[start..end];
    let Some(target) = lookup(nominal) else {
        return ty.to_string();
    };
    // Alias templates need parameter substitution, not concatenation of two
    // argument lists. They are deliberately not bound by this module.
    if target.contains('<') && ty[end..].trim_start().starts_with('<') {
        return ty.to_string();
    }
    format!("{}{}{}", &ty[..start], target, &ty[end..])
}

impl Environment<'_, '_> {
    fn resolve(&self, ty: &str, scope: &str) -> String {
        substitute(ty, |name| {
            if name.starts_with("::") {
                return self
                    .types
                    .get(name.trim_start_matches("::"))
                    .map(|b| b.target.clone());
            }
            scopes(scope).into_iter().find_map(|s| {
                self.types
                    .get(&qualified(s, name))
                    .map(|b| b.target.clone())
            })
        })
    }

    fn visible(&self, scope: &str, text: &str) -> HashMap<String, String> {
        let used = text
            .split(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != ':')
            .collect::<HashSet<_>>();
        let mut visible = self
            .types
            .iter()
            .filter(|(name, b)| {
                b.alias
                    && (used.contains(name.as_str()) || used.contains(format!("::{name}").as_str()))
            })
            .flat_map(|(k, b)| {
                [
                    (k.clone(), b.target.clone()),
                    (format!("::{k}"), b.target.clone()),
                ]
            })
            .collect::<HashMap<_, _>>();
        for prefix in scopes(scope).into_iter().rev() {
            for (key, binding) in &self.types {
                let (parent, name) = key.rsplit_once("::").unwrap_or(("", key));
                if parent == prefix && used.contains(name) {
                    if binding.alias {
                        visible.insert(name.to_string(), binding.target.clone());
                    } else {
                        visible.remove(name);
                    }
                }
            }
        }
        visible
    }

    fn visit(&mut self, node: Node<'_>, file: usize, scope: &str, depth: usize, conditional: bool) {
        let source = &self.resolver.files[file].source;
        match node.kind() {
            "preproc_include" if !conditional => {
                let Some(path) = node.child_by_field_name("path") else {
                    return;
                };
                let text = node_text(path, source);
                let Some(name) = text.strip_prefix('"').and_then(|s| s.strip_suffix('"')) else {
                    return;
                };
                if let Some(included) = self.resolver.included(file, name) {
                    if self.visited.contains(&included) {
                        return;
                    }
                    if depth >= 24 || self.visited.len() >= 256 {
                        self.exhausted = true;
                        return;
                    }
                    self.visited.insert(included);
                    if let Some(tree) = &self.resolver.files[included].tree {
                        self.visit(tree.root_node(), included, scope, depth + 1, false);
                    }
                }
                return;
            }
            "namespace_definition" => {
                let (Some(name), Some(body)) = (
                    node.child_by_field_name("name"),
                    node.child_by_field_name("body"),
                ) else {
                    return;
                };
                self.visit(
                    body,
                    file,
                    &qualified(scope, node_text(name, source)),
                    depth,
                    conditional,
                );
                return;
            }
            "alias_declaration" | "type_definition" => {
                let (Some(name), Some(ty)) = (
                    node.child_by_field_name(if node.kind() == "type_definition" {
                        "declarator"
                    } else {
                        "name"
                    }),
                    node.child_by_field_name("type"),
                ) else {
                    return;
                };
                if !matches!(name.kind(), "identifier" | "type_identifier") {
                    return;
                }
                // typedef struct definitions must register their record first.
                if matches!(ty.kind(), "class_specifier" | "struct_specifier") {
                    self.visit(ty, file, scope, depth, conditional);
                }
                let key = qualified(scope, node_text(name, source));
                let target = if conditional || node.has_error() {
                    key.clone()
                } else if matches!(
                    ty.kind(),
                    "struct_specifier" | "class_specifier" | "union_specifier" | "enum_specifier"
                ) {
                    ty.child_by_field_name("name")
                        .map(|name| self.resolve(node_text(name, source), scope))
                        .unwrap_or_else(|| key.clone())
                } else {
                    self.resolve(node_text(ty, source), scope)
                };
                self.types.insert(
                    key,
                    Binding {
                        target,
                        alias: true,
                    },
                );
                return;
            }
            "enum_specifier" => {
                let Some(name) = node.child_by_field_name("name") else {
                    return;
                };
                let key = qualified(scope, node_text(name, source));
                let text = node_text(node, source);
                let base = node
                    .child_by_field_name("base")
                    .map(|base| self.resolve(node_text(base, source), scope));
                let fixed = base
                    .filter(|base| scalar_type_size(base).is_some())
                    .or_else(|| {
                        (node.child_by_field_name("base").is_none()
                            && (text.starts_with("enum class ")
                                || text.starts_with("enum struct ")))
                        .then(|| "int".to_string())
                    });
                let target = if conditional || node.has_error() {
                    key.clone()
                } else {
                    fixed.unwrap_or_else(|| key.clone())
                };
                self.types.insert(
                    key,
                    Binding {
                        target,
                        alias: true,
                    },
                );
                return;
            }
            "class_specifier" | "struct_specifier" => {
                let Some(name) = node.child_by_field_name("name") else {
                    return;
                };
                let key = qualified(scope, node_text(name, source));
                self.types.insert(
                    key.clone(),
                    Binding {
                        target: key.clone(),
                        alias: false,
                    },
                );
                if let Some(body) = node.child_by_field_name("body") {
                    self.visit(body, file, &key, depth, conditional);
                    if file == self.root && !conditional {
                        self.snapshots.insert(
                            (
                                self.resolver.files[file].path.clone(),
                                node.start_position().row + 1,
                            ),
                            self.visible(&key, node_text(node, source)),
                        );
                    }
                }
                return;
            }
            "preproc_if" | "preproc_ifdef" | "preproc_else" | "preproc_elif" => {
                let guard = !conditional
                    && node.kind() == "preproc_ifdef"
                    && node
                        .parent()
                        .is_some_and(|p| p.kind() == "translation_unit")
                    && node.child_by_field_name("alternative").is_none()
                    && node_text(node, source).trim_start().starts_with("#ifndef")
                    && node.child_by_field_name("name").is_some_and(|name| {
                        let mut cursor = node.walk();
                        node.named_code_children(&mut cursor)
                            .find(|c| c.kind() != "identifier" && c.kind() != "comment")
                            .is_some_and(|first| {
                                first.kind() == "preproc_def"
                                    && first.child_by_field_name("name").is_some_and(|defined| {
                                        node_text(defined, source) == node_text(name, source)
                                    })
                            })
                    });
                let mut cursor = node.walk();
                for child in node.named_code_children(&mut cursor) {
                    self.visit(child, file, scope, depth, conditional || !guard);
                }
                return;
            }
            "template_declaration" => {
                // Class templates contribute nominal owners. Alias templates
                // have dependent substitutions and shadow any outer alias.
                let mut cursor = node.walk();
                for child in node.named_code_children(&mut cursor) {
                    if matches!(child.kind(), "class_specifier" | "struct_specifier") {
                        self.visit(child, file, scope, depth, conditional);
                    } else if child.kind() == "alias_declaration" {
                        self.visit(child, file, scope, depth, true);
                    }
                }
                return;
            }
            "translation_unit"
            | "declaration_list"
            | "field_declaration_list"
            | "declaration"
            | "field_declaration"
            | "linkage_specification" => {}
            _ => return, // Function bodies and sibling local scopes never export types.
        }
        let mut cursor = node.walk();
        for child in node.named_code_children(&mut cursor) {
            self.visit(child, file, scope, depth, conditional);
        }
    }
}
