//! Seed runtime identity from a concrete pthread launch, not variable spelling.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Seed {
    Scalar,
    Descriptor(HashSet<String>),
}

fn launch_seed(
    call: tree_sitter::Node<'_>,
    argument: tree_sitter::Node<'_>,
    file: &ParsedCppFile,
) -> Option<Seed> {
    let mut parent = call.parent();
    while let Some(node) = parent {
        if node.kind() == "function_definition" {
            break;
        }
        if node.kind() != "for_statement" {
            parent = node.parent();
            continue;
        }
        let update = node.child_by_field_name("update")?;
        if update.kind() != "update_expression" {
            return None;
        }
        let index = node_text(update.child_by_field_name("argument")?, &file.source);
        if node_text(update.child_by_field_name("operator")?, &file.source) != "++" {
            return None;
        }
        let body = node.child_by_field_name("body")?;
        let source = node_text(body, &file.source);
        if source.contains("pthread_join")
            || source.lines().any(|line| {
                simple_assignment_parts(line).is_some_and(|(lhs, _)| lhs.trim() == index)
            })
        {
            return None;
        }
        let value = transparent_partition_value(argument, &file.source);
        if value == index {
            return Some(Seed::Scalar);
        }
        // Each launch must own a distinct descriptor: either &array[index],
        // or a fresh allocation in this launch loop, never a reused singleton.
        let array = indexed_accesses(node_text(argument, &file.source))
            .into_iter()
            .find(|(_, coordinate)| coordinate.trim() == index);
        let mut object = if let Some((name, _)) = array {
            format!("{name}[{index}]")
        } else {
            value.clone()
        };
        object.retain(|c| !c.is_whitespace());
        let indexed = object.contains('[') && node_text(argument, &file.source).contains('&');
        let mut fresh = indexed;
        let mut fields = HashMap::new();
        walk_nodes(body, &mut |n| {
            if n.start_byte() >= call.start_byte() {
                return;
            }
            if n.kind() == "init_declarator"
                && let (Some(lhs), Some(rhs)) = (
                    n.child_by_field_name("declarator"),
                    n.child_by_field_name("value"),
                )
                && declarator_variable_name(lhs, &file.source).as_deref() == Some(&object)
            {
                fresh = node_text(rhs, &file.source).contains("malloc(")
                    || node_text(rhs, &file.source).contains("calloc(");
            }
            if n.kind() != "assignment_expression" {
                return;
            }
            let (Some(lhs), Some(rhs)) = (
                n.child_by_field_name("left"),
                n.child_by_field_name("right"),
            ) else {
                return;
            };
            if node_text(lhs, &file.source).replace(' ', "") == object {
                fresh = false;
            }
            if lhs.kind() == "field_expression"
                && lhs
                    .child_by_field_name("argument")
                    .is_some_and(|a| node_text(a, &file.source).replace(' ', "") == object)
                && let Some(field) = lhs.child_by_field_name("field")
            {
                fields.insert(
                    node_text(field, &file.source).to_owned(),
                    transparent_partition_value(rhs, &file.source) == index,
                );
            }
        });
        let fields = fields
            .into_iter()
            .filter_map(|(name, valid)| valid.then_some(name))
            .collect::<HashSet<_>>();
        return (fresh && !fields.is_empty()).then_some(Seed::Descriptor(fields));
    }
    None
}

pub(super) fn seed(file: &ParsedCppFile, origins: &mut IndexPartitionOrigins) {
    let Some(tree) = &file.tree else { return };
    let mut launches: HashMap<String, Vec<Option<Seed>>> = HashMap::new();
    walk_nodes(tree.root_node(), &mut |call| {
        if call.kind() != "call_expression"
            || call
                .child_by_field_name("function")
                .is_none_or(|f| node_text(f, &file.source) != "pthread_create")
        {
            return;
        }
        let Some(args) = call.child_by_field_name("arguments") else {
            return;
        };
        let args = args.named_children(&mut args.walk()).collect::<Vec<_>>();
        if args.len() != 4 {
            return;
        }
        let Some(worker) = callable_identifier(node_text(args[2], &file.source)) else {
            return;
        };
        launches
            .entry(worker)
            .or_default()
            .push(launch_seed(call, args[3], file));
    });
    // A callback also called ordinarily, or passed through another API, cannot
    // inherit a runtime identity from just one pthread occurrence.
    let mut definitions: HashMap<String, Vec<tree_sitter::Node<'_>>> = HashMap::new();
    let mut invalid = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "function_definition"
            && let Some(name) = function_definition_name(node, file)
            && launches.contains_key(&name)
        {
            definitions.entry(name).or_default().push(node);
        }
        if node.kind() != "identifier" || !launches.contains_key(node_text(node, &file.source)) {
            return;
        }
        let Some(parent) = node.parent() else { return };
        if parent.kind() == "function_declarator" {
            return;
        }
        let launch = parent.kind() == "argument_list"
            && parent.parent().is_some_and(|call| {
                call.child_by_field_name("function")
                    .is_some_and(|f| node_text(f, &file.source) == "pthread_create")
            });
        if !launch {
            invalid.insert(node_text(node, &file.source).to_owned());
        }
    });
    for (worker, launches) in launches {
        let Some(Some(seed)) = launches.first() else {
            continue;
        };
        if invalid.contains(&worker) || !launches.iter().all(|v| v.as_ref() == Some(seed)) {
            continue;
        }
        let Some(defs) = definitions.get(&worker) else {
            continue;
        };
        let [function] = defs.as_slice() else {
            continue;
        };
        let (Some(decl), Some(body)) = (
            function.child_by_field_name("declarator"),
            function.child_by_field_name("body"),
        ) else {
            continue;
        };
        let mut params = Vec::new();
        walk_nodes(decl, &mut |n| {
            if n.kind() == "parameter_declaration"
                && let Some(d) = n.child_by_field_name("declarator")
                && let Some(name) = declarator_variable_name(d, &file.source)
            {
                params.push(name);
            }
        });
        let [parameter] = params.as_slice() else {
            continue;
        };
        let begin = body.start_position().row + 1;
        let end = body.end_position().row + 1;
        match seed {
            Seed::Scalar => {
                origins
                    .runtime_parameters
                    .insert((begin, end, parameter.clone()));
            }
            Seed::Descriptor(fields) => {
                walk_nodes(body, &mut |node| {
                    if node.kind() != "init_declarator" {
                        return;
                    }
                    let (Some(lhs), Some(rhs)) = (
                        node.child_by_field_name("declarator"),
                        node.child_by_field_name("value"),
                    ) else {
                        return;
                    };
                    if transparent_partition_value(rhs, &file.source) != *parameter {
                        return;
                    }
                    if let Some(receiver) = declarator_variable_name(lhs, &file.source) {
                        for field in fields {
                            let member = format!("{receiver}->{field}");
                            let mut rebound = false;
                            walk_nodes(body, &mut |use_node| {
                                let target = match use_node.kind() {
                                    "assignment_expression" => use_node.child_by_field_name("left"),
                                    "update_expression" => use_node.child_by_field_name("argument"),
                                    _ => None,
                                };
                                rebound |= target.is_some_and(|target| {
                                    let text = node_text(target, &file.source).replace(' ', "");
                                    text == receiver || text == member
                                });
                                rebound |= use_node.kind() == "init_declarator"
                                    && use_node != node
                                    && use_node
                                        .child_by_field_name("declarator")
                                        .and_then(|d| declarator_variable_name(d, &file.source))
                                        .as_deref()
                                        == Some(&receiver);
                            });
                            if rebound {
                                continue;
                            }
                            origins.runtime_parameters.insert((begin, end, member));
                        }
                    }
                });
            }
        }
    }
}
