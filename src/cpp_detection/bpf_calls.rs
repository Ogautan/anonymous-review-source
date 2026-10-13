//! Source-backed summaries for wrappers around the BPF map API.
use crate::cpp_detection::parser::CodeChildren;
use std::collections::{HashMap, HashSet};
use tree_sitter::Node;

use super::super::parser::{ParsedCppFile, node_text, walk_nodes};
use super::super::types::CppAccessKind;

#[derive(Clone)]
pub(super) struct MapWrite {
    pub map_argument: usize,
    pub key_argument: usize,
    pub kind: CppAccessKind,
}

fn name<'a>(node: Node<'_>, source: &'a str) -> Option<&'a str> {
    if node.kind() == "identifier" {
        return Some(node_text(node, source));
    }
    node.child_by_field_name("declarator")
        .and_then(|child| name(child, source))
}

fn parameter_index(node: Node<'_>, source: &str, parameters: &[String]) -> Option<usize> {
    let text = node_text(node, source)
        .trim()
        .trim_start_matches('&')
        .trim();
    parameters.iter().position(|parameter| parameter == text)
}

pub(super) fn collect(file: &ParsedCppFile) -> HashMap<String, MapWrite> {
    let mut writes = HashMap::from([(
        "bpf_map_update_elem".to_string(),
        MapWrite {
            map_argument: 0,
            key_argument: 1,
            kind: CppAccessKind::Write,
        },
    )]);
    let Some(tree) = &file.tree else {
        return writes;
    };
    let mut definitions = Vec::new();
    let mut overridden = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "function_definition" {
            definitions.push(node);
        }
        if matches!(node.kind(), "preproc_def" | "preproc_function_def")
            && let Some(name) = node.child_by_field_name("name")
        {
            writes.remove(node_text(name, &file.source));
            overridden.insert(node_text(name, &file.source).to_owned());
        }
    });
    for node in &definitions {
        if let Some(function) = node
            .child_by_field_name("declarator")
            .and_then(|node| name(node, &file.source))
        {
            writes.remove(function);
            overridden.insert(function.to_owned());
        }
    }
    for _ in 0..4 {
        let previous = writes.clone();
        let mut definition_counts = HashMap::new();
        for definition in &definitions {
            if let Some(function) = definition
                .child_by_field_name("declarator")
                .and_then(|node| name(node, &file.source))
            {
                *definition_counts.entry(function).or_insert(0usize) += 1;
            }
        }
        for definition in &definitions {
            let Some(declarator) = definition.child_by_field_name("declarator") else {
                continue;
            };
            let Some(function) = name(declarator, &file.source) else {
                continue;
            };
            if definition_counts.get(function) != Some(&1) {
                continue;
            }
            let Some(parameters) = declarator.child_by_field_name("parameters") else {
                continue;
            };
            let parameters: Vec<_> = parameters
                .named_code_children(&mut parameters.walk())
                .filter_map(|node| {
                    node.child_by_field_name("declarator")
                        .and_then(|node| name(node, &file.source))
                })
                .map(str::to_owned)
                .collect();
            let Some(body) = definition.child_by_field_name("body") else {
                continue;
            };
            let mut candidates = Vec::new();
            let mut aliases = HashMap::new();
            let mut uncertain = false;
            walk_nodes(body, &mut |node| {
                uncertain |= node.kind() == "function_definition";
                if node.kind() == "init_declarator"
                    && let Some(local) = node
                        .child_by_field_name("declarator")
                        .and_then(|node| name(node, &file.source))
                {
                    aliases.remove(local);
                }
                if node.kind() == "call_expression" {
                    let callee = node
                        .child_by_field_name("function")
                        .map(|node| node_text(node, &file.source))
                        .unwrap_or("");
                    let Some(arguments) = node.child_by_field_name("arguments") else {
                        return;
                    };
                    let arguments: Vec<_> = arguments
                        .named_code_children(&mut arguments.walk())
                        .collect();
                    if let Some(summary) = previous.get(callee) {
                        if let (Some(map), Some(key)) = (
                            arguments.get(summary.map_argument),
                            arguments.get(summary.key_argument),
                        ) && let (Some(map_argument), Some(key_argument)) = (
                            parameter_index(*map, &file.source, &parameters),
                            parameter_index(*key, &file.source, &parameters),
                        ) {
                            candidates.push(MapWrite {
                                map_argument,
                                key_argument,
                                kind: summary.kind.clone(),
                            });
                        } else {
                            uncertain = true;
                        }
                    } else if callee == "bpf_map_lookup_elem"
                        && !overridden.contains(callee)
                        && arguments.len() >= 2
                    {
                        if let (Some(map), Some(key)) = (
                            parameter_index(arguments[0], &file.source, &parameters),
                            parameter_index(arguments[1], &file.source, &parameters),
                        ) && let Some(parent) = node
                            .parent()
                            .filter(|parent| parent.kind() == "init_declarator")
                            .filter(|parent| {
                                parent
                                    .parent()
                                    .and_then(|declaration| declaration.parent())
                                    .is_some_and(|scope| scope.id() == body.id())
                            })
                            && let Some(alias) = parent
                                .child_by_field_name("declarator")
                                .and_then(|node| name(node, &file.source))
                        {
                            aliases.insert(alias.to_owned(), (map, key));
                        } else {
                            uncertain = true;
                        }
                    } else if !overridden.contains(callee)
                        && matches!(
                            callee,
                            "__sync_fetch_and_add"
                                | "__sync_add_and_fetch"
                                | "__atomic_fetch_add"
                                | "__atomic_store_n"
                        )
                    {
                        if let Some(argument) = arguments.first()
                            && let Some((map_argument, key_argument)) =
                                aliases.get(node_text(*argument, &file.source).trim())
                        {
                            candidates.push(MapWrite {
                                map_argument: *map_argument,
                                key_argument: *key_argument,
                                kind: CppAccessKind::ReadModifyWrite,
                            });
                        } else {
                            uncertain = true;
                        }
                    } else {
                        uncertain = true;
                    }
                }
                if matches!(node.kind(), "assignment_expression" | "update_expression") {
                    // A changed map/key no longer binds directly to the caller's partition.
                    let target = node
                        .child_by_field_name("left")
                        .or_else(|| node.child_by_field_name("argument"));
                    if let Some(target) = target {
                        aliases.remove(node_text(target, &file.source).trim());
                    }
                    uncertain |= target.is_some_and(|target| {
                        parameter_index(target, &file.source, &parameters).is_some()
                    });
                }
            });
            if !uncertain
                && !candidates.is_empty()
                && candidates.iter().all(|candidate| {
                    candidate.map_argument == candidates[0].map_argument
                        && candidate.key_argument == candidates[0].key_argument
                })
            {
                writes.insert(function.to_owned(), candidates.remove(0));
            }
        }
        if previous.len() == writes.len() {
            break;
        }
    }
    writes
}
