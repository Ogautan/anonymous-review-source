//! Bounded, positional summaries for free functions writing through array
//! parameters. Neither a parameter's spelling nor a project-wide alias table
//! identifies the caller's storage. Unsupported bindings remain unresolved.

use super::*;
use tree_sitter::Node;

#[derive(Clone)]
struct Summary {
    storage: usize,
    index: usize,
    kind: CppAccessKind,
    path: Vec<String>,
}

struct Function<'a> {
    file: &'a ParsedCppFile,
    node: Node<'a>,
    body: Node<'a>,
    parameters: Vec<String>,
    pointer_parameters: HashSet<usize>,
    local_linkage: bool,
}

fn ancestors_contain(node: Node<'_>, kinds: &[&str]) -> bool {
    let mut parent = node.parent();
    while let Some(node) = parent {
        if kinds.contains(&node.kind()) {
            return true;
        }
        parent = node.parent();
    }
    false
}

fn call_parts<'a>(node: Node<'a>, source: &'a str) -> Option<(&'a str, Vec<Node<'a>>)> {
    let function = node.child_by_field_name("function")?;
    if function.kind() != "identifier" {
        return None;
    }
    let args = node.child_by_field_name("arguments")?;
    let mut cursor = args.walk();
    Some((
        node_text(function, source),
        args.named_children(&mut cursor).collect(),
    ))
}

fn parameter_shapes(declarator: Node<'_>, source: &str) -> Option<Vec<String>> {
    let params = declarator.child_by_field_name("parameters")?;
    let mut cursor = params.walk();
    params
        .named_children(&mut cursor)
        .map(|p| {
            let ty = node_text(p.child_by_field_name("type")?, source);
            let shape = match p.child_by_field_name("declarator").map(|d| d.kind()) {
                Some("identifier") | None => "value",
                Some("pointer_declarator" | "array_declarator") => "pointer",
                _ => return None,
            };
            Some(format!("{ty}:{shape}"))
        })
        .collect()
}

pub(super) fn collect_bound_indexed_calls(
    files: &[ParsedCppFile],
    storage_index: &super::storage_identity::StorageIndex,
) -> Vec<IndexedWriteCandidate> {
    let mut functions: HashMap<String, Vec<Function<'_>>> = HashMap::new();
    // Count all definitions, including member/namespace overloads, before
    // selecting the deliberately narrower set whose calls we can bind.
    let mut definitions = HashMap::<String, usize>::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "function_definition" {
                return;
            }
            let Some(name) = function_definition_name(node, file) else {
                return;
            };
            *definitions.entry(name.clone()).or_default() += 1;
            if ancestors_contain(
                node,
                &[
                    "namespace_definition",
                    "class_specifier",
                    "struct_specifier",
                    "function_definition",
                    "lambda_expression",
                    "template_declaration",
                ],
            ) {
                return;
            }
            let Some(body) = node.child_by_field_name("body") else {
                return;
            };
            let signature = &file.source[node.start_byte()..body.start_byte()];
            if signature.contains("::")
                || identifier_tokens(signature).any(|t| matches!(t, "__device__" | "__global__"))
            {
                return;
            }
            let Some(declarator) = node.child_by_field_name("declarator") else {
                return;
            };
            let Some(params) = declarator.child_by_field_name("parameters") else {
                return;
            };
            let mut parameters = Vec::new();
            let mut pointer_parameters = HashSet::new();
            let mut valid = true;
            let mut cursor = params.walk();
            for parameter in params.named_children(&mut cursor) {
                let Some(declaration) = parameter.child_by_field_name("declarator") else {
                    valid = false;
                    break;
                };
                let Some(name) = declarator_variable_name(declaration, &file.source) else {
                    valid = false;
                    break;
                };
                if matches!(
                    declaration.kind(),
                    "pointer_declarator" | "array_declarator"
                ) && declaration
                    .child_by_field_name("declarator")
                    .is_some_and(|n| n.kind() == "identifier")
                    && parameter.child_by_field_name("type").is_some_and(|n| {
                        matches!(n.kind(), "primitive_type" | "sized_type_specifier")
                    })
                {
                    pointer_parameters.insert(parameters.len());
                }
                parameters.push(name);
            }
            if valid {
                functions.entry(name).or_default().push(Function {
                    file,
                    node,
                    body,
                    parameters,
                    pointer_parameters,
                    local_linkage: identifier_tokens(signature).any(|t| t == "static"),
                });
            }
        });
    }
    functions.retain(|name, entries| entries.len() == 1 && definitions.get(name) == Some(&1));
    let mut functions = functions
        .into_iter()
        .map(|(name, mut f)| (name, f.remove(0)))
        .collect::<HashMap<_, _>>();
    // A definition is not the entire overload set: declarations without a
    // body can introduce alternatives too. Reject incompatible prototypes.
    let mut ambiguous = HashSet::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "function_declarator" {
                return;
            }
            let Some(name_node) = node.child_by_field_name("declarator") else {
                return;
            };
            let name = node_text(name_node, &file.source);
            let Some(target) = functions.get(name) else {
                return;
            };
            let expected = target
                .node
                .child_by_field_name("declarator")
                .and_then(|d| parameter_shapes(d, &target.file.source));
            if expected.is_none() || parameter_shapes(node, &file.source) != expected {
                ambiguous.insert(name.to_string());
            }
        });
    }
    functions.retain(|name, _| !ambiguous.contains(name));
    let mut summaries = HashMap::<String, Summary>::new();
    for (name, function) in &functions {
        // A single expression statement supplies an exact mutation summary,
        // without guessing branch conditions, pointer reassignments or guards.
        if function.body.named_child_count() != 1 {
            continue;
        }
        let statement = function.body.named_child(0).unwrap();
        if statement.kind() != "expression_statement" {
            continue;
        }
        let Some(expression) = statement.named_child(0) else {
            continue;
        };
        let target = match expression.kind() {
            "assignment_expression" => expression.child_by_field_name("left"),
            "update_expression" => expression.child_by_field_name("argument"),
            _ => None,
        };
        let Some(target) = target.filter(|node| node.kind() == "subscript_expression") else {
            continue;
        };
        let mut unsafe_expression = false;
        walk_nodes(statement, &mut |node| {
            if matches!(
                node.kind(),
                "call_expression"
                    | "lambda_expression"
                    | "conditional_expression"
                    | "comma_expression"
            ) {
                unsafe_expression = true;
            }
            if node != expression
                && matches!(node.kind(), "assignment_expression" | "update_expression")
            {
                unsafe_expression = true;
            }
        });
        if unsafe_expression {
            continue;
        }
        let mutations = indexed_mutations(node_text(statement, &function.file.source));
        let [(storage, index, kind)] = mutations.as_slice() else {
            continue;
        };
        let Some(storage) = function.parameters.iter().position(|p| p == storage) else {
            continue;
        };
        let Some(index) = function.parameters.iter().position(|p| p == index.trim()) else {
            continue;
        };
        if !function.pointer_parameters.contains(&storage)
            || function.pointer_parameters.contains(&index)
        {
            continue;
        }
        // The parameter must be the array base, not an object member sharing
        // its spelling or a pointer-to-pointer dereference.
        let mut exact = false;
        walk_nodes(statement, &mut |node| {
            if node == target
                && node.child_by_field_name("argument").is_some_and(|arg| {
                    arg.kind() == "identifier"
                        && node_text(arg, &function.file.source) == function.parameters[storage]
                })
            {
                exact = true;
            }
        });
        if exact {
            summaries.insert(
                name.clone(),
                Summary {
                    storage,
                    index,
                    kind: kind.clone(),
                    path: vec![format!(
                        "{}:{} {name}",
                        function.file.path,
                        function.node.start_position().row + 1
                    )],
                },
            );
        }
    }
    // Compose forwarding wrappers by parameter position, with a fixed depth
    // bound and no recursion. A wrapper must consist solely of that call.
    for _ in 0..3 {
        let previous = summaries.clone();
        for (name, function) in &functions {
            if previous.contains_key(name) || function.body.named_child_count() != 1 {
                continue;
            }
            let Some(call) = function
                .body
                .named_child(0)
                .and_then(|s| s.named_child(0))
                .filter(|n| n.kind() == "call_expression")
            else {
                continue;
            };
            let Some((callee, args)) = call_parts(call, &function.file.source) else {
                continue;
            };
            if function
                .parameters
                .iter()
                .any(|parameter| parameter == callee)
            {
                continue;
            }
            let Some(summary) = previous.get(callee) else {
                continue;
            };
            let target = &functions[callee];
            if target.local_linkage && target.file.path != function.file.path {
                continue;
            }
            if args.len() != target.parameters.len() {
                continue;
            }
            let positions = [summary.storage, summary.index].map(|position| {
                args.get(position)
                    .filter(|n| n.kind() == "identifier")
                    .and_then(|n| {
                        function
                            .parameters
                            .iter()
                            .position(|p| p == node_text(*n, &function.file.source))
                    })
            });
            let [Some(storage), Some(index)] = positions else {
                continue;
            };
            if !function.pointer_parameters.contains(&storage)
                || function.pointer_parameters.contains(&index)
            {
                continue;
            }
            let mut next = summary.clone();
            next.storage = storage;
            next.index = index;
            next.path.insert(
                0,
                format!(
                    "{}:{} {name}",
                    function.file.path,
                    function.node.start_position().row + 1
                ),
            );
            summaries.insert(name.clone(), next);
        }
    }
    let mut candidates = Vec::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        let regions = collect_function_regions(file);
        let origins = collect_index_partition_origins(file, &regions);
        let locksets = collect_scoped_locksets(file);
        let mut arrays = HashSet::new();
        let mut local_names = HashSet::new();
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(node.kind(), "declaration" | "parameter_declaration") {
                return;
            }
            let local = ancestors_contain(node, &["function_definition", "lambda_expression"]);
            let primitive = node
                .child_by_field_name("type")
                .is_some_and(|ty| matches!(ty.kind(), "primitive_type" | "sized_type_specifier"));
            let mut cursor = node.walk();
            for declarator in node.children_by_field_name("declarator", &mut cursor) {
                let Some(name) = declarator_variable_name(declarator, &file.source) else {
                    continue;
                };
                if local {
                    local_names.insert(name);
                } else if primitive
                    && node.kind() == "declaration"
                    && declarator.kind() == "array_declarator"
                    && declarator
                        .child_by_field_name("declarator")
                        .is_some_and(|inner| inner.kind() == "identifier")
                    && !ancestors_contain(
                        node,
                        &[
                            "namespace_definition",
                            "class_specifier",
                            "struct_specifier",
                        ],
                    )
                {
                    arrays.insert(name);
                }
            }
        });
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "call_expression" {
                return;
            }
            let Some((callee, args)) = call_parts(node, &file.source) else {
                return;
            };
            let Some(summary) = summaries.get(callee) else {
                return;
            };
            let target = &functions[callee];
            if local_names.contains(callee)
                || (target.local_linkage && target.file.path != file.path)
                || args.len() != target.parameters.len()
            {
                return;
            }
            let storage = args[summary.storage];
            if storage.kind() != "identifier" {
                return;
            }
            let storage = node_text(storage, &file.source);
            if !arrays.contains(storage) || local_names.contains(storage) {
                return;
            }
            let line = node.start_position().row + 1;
            if device_only_function_at(&regions, line)
                || !origins.supports_runtime_identity(
                    &transparent_partition_value(args[summary.index], &file.source),
                    line,
                )
            {
                return;
            }
            candidates.push(IndexedWriteCandidate {
                file: file.path.clone(),
                line,
                snippet: node_text(node, &file.source).to_string(),
                function_name: enclosing_function_name(&regions, line),
                record_name: None,
                record_line: None,
                record_peer: None,
                record_storage: None,
                field_name: Some(storage.to_string()),
                alias_name: None,
                access_kind: summary.kind.clone(),
                has_direct_partition_evidence: true,
                access_in_concurrent_context: true,
                guard_ids: locksets.get(&line).cloned().unwrap_or_default(),
                evidence: vec![
                    format!(
                        "过程间绑定: {storage} → 参数 {}；CPU runtime index → 参数 {}",
                        summary.storage, summary.index
                    ),
                    format!("写路径: {}", summary.path.join(" → ")),
                    "布局证据: 调用点可见的全局原生连续数组；非项目级同名别名推测".to_string(),
                ],
                storage_identity: storage_index.visible(&file.path, line, storage),
            });
        });
    }
    candidates
}
