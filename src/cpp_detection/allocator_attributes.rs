//! Declaration-bound GNU non-aliasing allocation contracts. The argument-taking
//! `malloc(deallocator)` attribute only names a deallocator; it is not this proof.
use super::{
    AllocationMacro, FileFacts, callable_name, callable_scope, macro_visibility, node_text,
    normalized_path, unconditionally_preprocessed, walk_nodes,
};
use crate::cpp_detection::parser::CodeChildren;
use std::collections::{HashMap, HashSet};
use std::path::Path;
use tree_sitter::Node;

pub(super) fn build_overrides(
    commands: &[super::super::types::CppCompileCommand],
) -> (HashSet<String>, bool) {
    let mut names = HashSet::new();
    let mut opaque = false;
    for command in commands {
        let mut arguments = command.arguments.iter();
        while let Some(arg) = arguments.next() {
            opaque |= arg.starts_with('@')
                || arg.starts_with("-include")
                || arg.starts_with("-imacros")
                || arg.starts_with("/FI");
            let value = if matches!(arg.as_str(), "-D" | "-U" | "/D" | "/U") {
                arguments.next().map(String::as_str)
            } else {
                ["-D", "-U", "/D", "/U"]
                    .iter()
                    .find_map(|prefix| arg.strip_prefix(prefix))
            };
            if let Some(value) = value {
                names.insert(value.split(['=', '(']).next().unwrap_or(value).to_owned());
            }
        }
    }
    (names, opaque)
}

fn macro_bit(name: &str, function_like: bool) -> u8 {
    match name {
        "__attribute__" => 1,
        "__attribute" => 2,
        "malloc" if !function_like => 4,
        "__malloc__" if !function_like => 8,
        "gnu" if !function_like => 16,
        _ => 0,
    }
}

/// All source-visible possible quoted includes participate in invalidation,
/// including conditional includes. Positive declaration visibility is stricter.
fn possible_overrides(facts: &[FileFacts<'_>]) -> Vec<u8> {
    let paths = facts
        .iter()
        .enumerate()
        .map(|(i, f)| (normalized_path(Path::new(&f.file.path)), i))
        .collect::<HashMap<_, _>>();
    let mut overrides = vec![0; facts.len()];
    let mut edges = Vec::new();
    for (index, facts) in facts.iter().enumerate() {
        let Some(tree) = &facts.file.tree else {
            continue;
        };
        walk_nodes(tree.root_node(), &mut |node| {
            if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                && let Some(name) = node.child_by_field_name("name")
            {
                overrides[index] |= macro_bit(
                    node_text(name, &facts.file.source),
                    node.kind() == "preproc_function_def",
                );
            }
            if node.kind() == "preproc_include"
                && let Some(path) = node.child_by_field_name("path")
                && let Some(relative) = node_text(path, &facts.file.source)
                    .strip_prefix('"')
                    .and_then(|p| p.strip_suffix('"'))
            {
                let path = Path::new(&facts.file.path)
                    .parent()
                    .unwrap_or(Path::new(""))
                    .join(relative);
                if let Some(target) = paths.get(&normalized_path(&path)) {
                    edges.push((index, *target));
                }
            }
        });
    }
    loop {
        let mut changed = false;
        for (source, target) in &edges {
            let next = overrides[*source] | overrides[*target];
            changed |= overrides[*source] != next;
            overrides[*source] = next;
        }
        if !changed {
            break;
        }
    }
    overrides
}

fn nonalias_attribute(node: Node<'_>, source: &str) -> Option<u8> {
    if node.kind() == "attribute_specifier" {
        let syntax = node_text(node, source).split('(').next()?.trim();
        let syntax_bit = match syntax {
            "__attribute__" => 1,
            "__attribute" => 2,
            _ => return None,
        };
        let args = node.named_code_child(0)?;
        if args.kind() != "argument_list" {
            return None;
        }
        return args.named_code_children(&mut args.walk()).find_map(|arg| {
            if arg.kind() != "identifier" {
                return None;
            }
            match node_text(arg, source) {
                "malloc" => Some(syntax_bit | 4),
                "__malloc__" => Some(syntax_bit | 8),
                _ => None,
            }
        });
    }
    if node.kind() == "attribute"
        && node
            .child_by_field_name("prefix")
            .is_some_and(|n| node_text(n, source) == "gnu")
        && node
            .child_by_field_name("name")
            .is_some_and(|n| node_text(n, source) == "malloc")
        && !node_text(node, source).contains('(')
    {
        return Some(16 | 4);
    }
    None
}

pub(super) fn collect(
    facts: &[FileFacts<'_>],
    include_edges: &[(usize, usize, usize)],
    build_names: &HashSet<String>,
    opaque_build: bool,
) -> HashMap<String, HashMap<String, usize>> {
    if opaque_build {
        return HashMap::new();
    }
    let command_mask = build_names
        .iter()
        .fold(0, |mask, name| mask | macro_bit(name, false));
    let overrides = possible_overrides(facts);
    let by_path = facts
        .iter()
        .enumerate()
        .map(|(i, f)| (f.file.path.as_str(), i))
        .collect::<HashMap<_, _>>();
    let mut contracts = HashMap::<String, HashMap<String, usize>>::new();
    for (index, facts_file) in facts.iter().enumerate() {
        let file = facts_file.file;
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |declaration| {
            if declaration.kind() != "declaration"
                || declaration.has_error()
                || !callable_scope(declaration, &file.source).is_empty()
                || super::enclosing_function(declaration).is_some()
                || !unconditionally_preprocessed(declaration, &file.source)
            {
                return;
            }
            let Some(name) = callable_name(declaration, &file.source) else {
                return;
            };
            // Only direct free functions returning native pointers, not an
            // annotated function-pointer variable, member, or overload family.
            let Some(mut declarator) = declaration.child_by_field_name("declarator") else {
                return;
            };
            let mut pointer_return = false;
            while declarator.kind() == "pointer_declarator" {
                pointer_return = true;
                let Some(inner) = declarator.child_by_field_name("declarator") else {
                    return;
                };
                declarator = inner;
            }
            if !pointer_return
                || declarator.kind() != "function_declarator"
                || declarator
                    .child_by_field_name("declarator")
                    .is_none_or(|n| n.kind() != "identifier")
                || declaration
                    .children_by_field_name("declarator", &mut declaration.walk())
                    .count()
                    != 1
            {
                return;
            }
            let Some(parameters) = declarator.child_by_field_name("parameters") else {
                return;
            };
            let mut attributes = HashSet::new();
            walk_nodes(declaration, &mut |node| {
                // An attribute on a parameter says nothing about the result.
                if node.start_byte() >= parameters.start_byte()
                    && node.end_byte() <= parameters.end_byte()
                {
                    return;
                }
                if let Some(mask) = nonalias_attribute(node, &file.source) {
                    attributes.insert(mask);
                }
            });
            for mask in attributes {
                if (overrides[index] | command_mask) & mask != 0 {
                    continue;
                }
                let binding = AllocationMacro {
                    body: String::new(),
                    parameters: HashSet::new(),
                    file: index,
                    end: declaration.end_byte(),
                    unconditional: true,
                };
                let mut visible = macro_visibility(facts, &[binding], include_edges);
                visible.retain(|path, _| {
                    by_path
                        .get(path.as_str())
                        .is_some_and(|i| overrides[*i] & mask == 0)
                });
                for (path, begin) in visible {
                    contracts
                        .entry(name.clone())
                        .or_default()
                        .entry(path)
                        .and_modify(|old| *old = (*old).min(begin))
                        .or_insert(begin);
                }
            }
        });
    }
    contracts
}
