//! Source-backed callback contracts. Names locate declarations; only the
//! selected parameter's uses in a unique definition establish synchrony.
use super::*;
use crate::cpp_detection::parser::CodeChildren;
use tree_sitter::Node;

#[derive(Default)]
pub(super) struct Contracts {
    positions: HashMap<String, HashSet<(usize, usize)>>,
    deduced_positions: HashSet<(String, usize, usize)>,
    owners: HashMap<String, HashSet<String>>,
    aliases: HashSet<String>,
    direct_members: HashSet<String>,
    macros: HashSet<String>,
}

pub(super) fn preserves_callback_target(
    parameter: Node<'_>,
    definition: Node<'_>,
    file: &ParsedCppFile,
) -> bool {
    let Some(ty) = parameter.child_by_field_name("type") else {
        return false;
    };
    let ty_text = node_text(ty, &file.source);
    if field_access::without_template_arguments(ty_text).trim() == "std::function" {
        return true;
    }
    let Some(template) = definition
        .parent()
        .filter(|n| n.kind() == "template_declaration")
    else {
        return false;
    };
    let Some(parameters) = template.child_by_field_name("parameters") else {
        return false;
    };
    if ty.kind() != "type_identifier" {
        return false;
    }
    let mut declared_type_parameter = false;
    walk_nodes(parameters, &mut |node| {
        if node.kind() == "type_parameter_declaration"
            && identifier_tokens(node_text(node, &file.source)).last() == Some(ty_text)
        {
            declared_type_parameter = true;
        }
    });
    declared_type_parameter
        && parameter
            .child_by_field_name("declarator")
            .is_some_and(|n| !node_text(n, &file.source).contains(['*', '[']))
}

fn declaration_name(node: Node<'_>, file: &ParsedCppFile) -> Option<String> {
    let name = node.child_by_field_name("declarator")?;
    if !matches!(
        name.kind(),
        "identifier" | "field_identifier" | "qualified_identifier"
    ) {
        return None;
    }
    let mut parts = vec![node_text(name, &file.source).to_owned()];
    let mut ancestor = node.parent();
    while let Some(scope) = ancestor {
        if matches!(
            scope.kind(),
            "class_specifier" | "struct_specifier" | "namespace_definition"
        ) {
            parts.push(node_text(scope.child_by_field_name("name")?, &file.source).to_owned());
        }
        if scope.kind() == "lambda_expression"
            || (scope.kind() == "template_declaration"
                && !scope
                    .named_code_children(&mut scope.walk())
                    .any(|child| matches!(child.kind(), "function_definition" | "declaration")))
        {
            return None;
        }
        ancestor = scope.parent();
    }
    parts.reverse();
    Some(parts.join("::"))
}

fn parameter_shape(
    parameter: Node<'_>,
    file: &ParsedCppFile,
    contracts: &Contracts,
) -> Option<String> {
    let declarator = parameter.child_by_field_name("declarator")?;
    let name = declarator_variable_name(declarator, &file.source)?;
    let mut shape = node_text(parameter, &file.source).to_owned();
    let start = shape.rfind(&name)?;
    shape.replace_range(start..start + name.len(), "");
    if let Some(ty) = parameter.child_by_field_name("type") {
        let spelling = node_text(ty, &file.source).trim_start_matches("::");
        let short = spelling.rsplit("::").next()?;
        if matches!(ty.kind(), "type_identifier" | "qualified_identifier")
            && !contracts.aliases.contains(short)
            && let Some(owners) = contracts
                .owners
                .get(short)
                .filter(|owners| owners.len() == 1)
        {
            let namespace = callback_lexical_namespace(parameter, &file.source)?;
            let expected = if spelling.contains("::") || namespace.is_empty() {
                spelling.to_owned()
            } else {
                format!("{namespace}::{spelling}")
            };
            if owners.contains(&expected) {
                shape.replace_range(
                    ty.start_byte() - parameter.start_byte()
                        ..ty.end_byte() - parameter.start_byte(),
                    &expected,
                );
            }
        }
    }
    Some(shape.chars().filter(|c| !c.is_whitespace()).collect())
}

pub(super) fn collect(files: &[ParsedCppFile]) -> Contracts {
    let mut result = Contracts::default();
    let mut declarations: HashMap<String, Vec<(&ParsedCppFile, Node<'_>)>> = HashMap::new();
    for file in files {
        let Some(tree) = &file.tree else {
            continue;
        };
        walk_nodes(tree.root_node(), &mut |node| {
            if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                && let Some(name) = node.child_by_field_name("name")
            {
                result
                    .macros
                    .insert(node_text(name, &file.source).to_owned());
            }
            if matches!(
                node.kind(),
                "namespace_definition" | "class_specifier" | "struct_specifier"
            ) && let Some(name) = node.child_by_field_name("name")
            {
                let spelling = node_text(name, &file.source);
                let mut parts = vec![spelling];
                let mut ancestor = node.parent();
                let mut complete = true;
                while let Some(scope) = ancestor {
                    if matches!(
                        scope.kind(),
                        "namespace_definition" | "class_specifier" | "struct_specifier"
                    ) {
                        if let Some(name) = scope.child_by_field_name("name") {
                            parts.push(node_text(name, &file.source));
                        } else {
                            complete = false;
                        }
                    }
                    ancestor = scope.parent();
                }
                if complete {
                    parts.reverse();
                    result
                        .owners
                        .entry(spelling.rsplit("::").next().unwrap_or(spelling).to_owned())
                        .or_default()
                        .insert(parts.join("::"));
                }
            }
            if matches!(
                node.kind(),
                "alias_declaration" | "namespace_alias_definition"
            ) && let Some(name) = node.child_by_field_name("name")
            {
                result
                    .aliases
                    .insert(node_text(name, &file.source).to_owned());
            }
            if node.kind() == "type_definition"
                && let Some(name) = node.child_by_field_name("declarator").and_then(|n| {
                    if n.kind() == "type_identifier" {
                        Some(node_text(n, &file.source).to_owned())
                    } else {
                        declarator_variable_name(n, &file.source)
                    }
                })
            {
                result.aliases.insert(name);
            }
            if node.kind() == "function_declarator"
                && let Some(name) = declaration_name(node, file)
            {
                declarations.entry(name).or_default().push((file, node));
            }
        });
    }
    for (name, declarations) in declarations {
        let definitions = declarations
            .iter()
            .filter(|(_, node)| {
                node.parent()
                    .is_some_and(|n| n.kind() == "function_definition")
            })
            .collect::<Vec<_>>();
        let [(file, declarator)] = definitions.as_slice() else {
            continue;
        };
        let Some(parameters) = declarator.child_by_field_name("parameters") else {
            continue;
        };
        let definition = declarator.parent().unwrap();
        if !parameters
            .named_code_children(&mut parameters.walk())
            .any(|parameter| preserves_callback_target(parameter, definition, file))
        {
            continue;
        }
        let Some(body) = declarator
            .parent()
            .and_then(|n| n.child_by_field_name("body"))
        else {
            continue;
        };
        if body.has_error()
            || identifier_tokens(node_text(body, &file.source))
                .any(|token| result.macros.contains(token))
            || identifier_tokens(node_text(body, &file.source))
                .any(|n| matches!(n, "co_await" | "co_yield" | "co_return"))
        {
            continue;
        }
        let Some(parameters) = declarator.child_by_field_name("parameters") else {
            continue;
        };
        let shapes = parameters
            .named_code_children(&mut parameters.walk())
            .map(|n| parameter_shape(n, file, &result))
            .collect::<Option<Vec<_>>>();
        let Some(shapes) = shapes else {
            continue;
        };
        // Reject differing overloads, not merely differing arity. Missing or
        // inconsistent declarations cannot be repaired by choosing one body.
        if declarations.iter().any(|(other_file, node)| {
            node.has_error()
                || node.child_by_field_name("parameters").is_none_or(|params| {
                    params
                        .named_code_children(&mut params.walk())
                        .map(|p| parameter_shape(p, other_file, &result))
                        .collect::<Option<Vec<_>>>()
                        .as_ref()
                        != Some(&shapes)
                })
        }) {
            continue;
        }
        // Explicit this dispatch may use a body only when no base/virtual
        // dispatch can replace it. Qualified calls already suppress virtual
        // dispatch and keep their existing resolution path.
        let direct_member = declarations.iter().all(|(file, method)| {
            let Some(declaration) = method.parent() else {
                return false;
            };
            let signature = &file.source[declaration.start_byte()..method.end_byte()];
            if identifier_tokens(signature)
                .any(|token| matches!(token, "virtual" | "override" | "final"))
            {
                return false;
            }
            let mut ancestor = declaration.parent();
            while let Some(scope) = ancestor {
                if matches!(scope.kind(), "class_specifier" | "struct_specifier") {
                    return !scope.has_error()
                        && !scope
                            .named_code_children(&mut scope.walk())
                            .any(|child| child.kind() == "base_class_clause")
                        && scope
                            .parent()
                            .is_none_or(|parent| parent.kind() != "template_declaration");
                }
                ancestor = scope.parent();
            }
            false
        });
        if direct_member {
            result.direct_members.insert(name.clone());
        }
        let concurrent = concurrent_context_lines(file);
        for (position, parameter) in parameters
            .named_code_children(&mut parameters.walk())
            .enumerate()
        {
            // Unknown user-defined callback conversions/operators can publish
            // the closure before invocation. std::function's direct call
            // invokes the stored target in this execution domain.
            let standard_function = parameter.child_by_field_name("type").is_some_and(|ty| {
                field_access::without_template_arguments(node_text(ty, &file.source)).trim()
                    == "std::function"
            });
            if !preserves_callback_target(parameter, definition, file) {
                continue;
            }
            let Some(parameter) = parameter
                .child_by_field_name("declarator")
                .and_then(|n| declarator_variable_name(n, &file.source))
            else {
                continue;
            };
            let mut safe = true;
            let mut calls = 0;
            walk_nodes(body, &mut |node| {
                if !safe
                    || node.kind() != "identifier"
                    || node_text(node, &file.source) != parameter
                {
                    return;
                }
                let call = node
                    .parent()
                    .filter(|n| {
                        n.kind() == "call_expression"
                            && n.child_by_field_name("function") == Some(node)
                    })
                    .or_else(|| direct_static_callback_wrapper_call(node, file, &concurrent));
                let Some(call) = call else {
                    safe = false;
                    return;
                };
                let mut ancestor = call.parent();
                while let Some(scope) = ancestor {
                    if scope == body {
                        break;
                    }
                    if scope.kind() == "lambda_expression" {
                        if direct_static_callback_wrapper_call(scope, file, &concurrent).is_none() {
                            safe = false;
                            return;
                        }
                    } else if matches!(
                        scope.kind(),
                        "function_definition" | "class_specifier" | "struct_specifier"
                    ) {
                        safe = false;
                        return;
                    }
                    ancestor = scope.parent();
                }
                if concurrent.contains(&(node.start_position().row + 1)) {
                    safe = false;
                }
                calls += 1;
            });
            if safe && calls > 0 {
                if !standard_function {
                    result.deduced_positions.insert((
                        name.clone(),
                        parameters.named_code_child_count(),
                        position,
                    ));
                }
                result
                    .positions
                    .entry(name.clone())
                    .or_default()
                    .insert((parameters.named_code_child_count(), position));
            }
        }
    }
    result
}

impl Contracts {
    pub(super) fn call_consuming<'a>(
        &self,
        argument: Node<'a>,
        file: &ParsedCppFile,
        deduced_lambda: bool,
    ) -> Option<Node<'a>> {
        let arguments = argument.parent().filter(|n| n.kind() == "argument_list")?;
        let call = arguments
            .parent()
            .filter(|n| n.kind() == "call_expression")?;
        let function = call.child_by_field_name("function")?;
        let spelling = node_text(function, &file.source);
        if identifier_tokens(spelling).any(|token| self.macros.contains(token)) {
            return None;
        }
        let resolved;
        let name = if function.kind() == "field_expression" {
            if function.child_by_field_name("argument")?.kind() != "this" {
                return None;
            }
            let member = function.child_by_field_name("field")?;
            if member.kind() != "field_identifier" {
                return None;
            }
            let mut enclosing = call.parent();
            let mut owner = None;
            while let Some(scope) = enclosing {
                if scope.kind() == "function_definition" {
                    let method = scope.child_by_field_name("declarator")?;
                    let qualified = declaration_name(method, file)?;
                    owner = qualified
                        .rsplit_once("::")
                        .map(|(owner, _)| owner.to_owned());
                    break;
                }
                enclosing = scope.parent();
            }
            resolved = format!("{}::{}", owner?, node_text(member, &file.source));
            if !self.direct_members.contains(&resolved) {
                return None;
            }
            &resolved
        } else if function.kind() != "qualified_identifier" {
            return None;
        } else if let Some(name) = spelling.strip_prefix("::") {
            name
        } else {
            let (owner, member) = spelling.split_once("::")?;
            if self.aliases.contains(owner) {
                return None;
            }
            let owners = self.owners.get(owner)?;
            if owners.len() != 1 {
                return None;
            }
            let namespace = callback_lexical_namespace(call, &file.source)?;
            let expected = if namespace.is_empty() {
                owner.to_owned()
            } else {
                format!("{namespace}::{owner}")
            };
            // No suffix fallback to another namespace or same-named record.
            if !owners.contains(&expected) {
                return None;
            }
            resolved = format!("{expected}::{member}");
            &resolved
        };
        let position = arguments
            .named_code_children(&mut arguments.walk())
            .position(|n| n == argument)?;
        // Only `auto value = [..] {..}` guarantees template deduction preserves
        // this closure. A user-defined converting wrapper may publish it.
        if !deduced_lambda
            && self.deduced_positions.contains(&(
                name.to_owned(),
                arguments.named_code_child_count(),
                position,
            ))
        {
            return None;
        }
        self.positions
            .get(name)?
            .contains(&(arguments.named_code_child_count(), position))
            .then_some(call)
    }
}
