//! Bounded nonescape contracts for visible scalar-only function-like macros.
//! No macro name is assigned semantics; ambiguous or opaque bodies fail closed.
use super::*;

/// Object macros consisting solely of a decimal integer (optionally wrapped
/// in parentheses). No identifiers, type substitutions or token pasting can
/// hide an access. Redefinitions, undefinitions and conditional definitions
/// are deliberately unresolved.
pub(in crate::cpp_detection) fn literal_objects(file: &ParsedCppFile) -> HashMap<String, usize> {
    let Some(tree) = &file.tree else {
        return HashMap::new();
    };
    let mut result = HashMap::new();
    let mut seen = HashSet::new();
    let mut blocked = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "preproc_call"
            && node_text(node, &file.source)
                .trim_start()
                .starts_with("#undef")
        {
            blocked.extend(
                identifier_tokens(node_text(node, &file.source))
                    .skip(1)
                    .map(str::to_owned),
            );
        }
        if !matches!(node.kind(), "preproc_def" | "preproc_function_def") {
            return;
        }
        let Some(name) = node.child_by_field_name("name") else {
            return;
        };
        let name = node_text(name, &file.source).to_owned();
        if !seen.insert(name.clone()) {
            blocked.insert(name.clone());
        }
        if node.kind() != "preproc_def"
            || node.parent().is_none_or(|p| p.kind() != "translation_unit")
        {
            return;
        }
        let Some(value) = node.child_by_field_name("value") else {
            return;
        };
        let mut value = node_text(value, &file.source).trim();
        if value.len() > 128 {
            return;
        }
        while let Some(inner) = value.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
            value = inner.trim();
        }
        if !value.is_empty()
            && value.bytes().all(|c| c.is_ascii_digit())
            && value.parse::<u64>().is_ok()
        {
            result.insert(name, node.end_byte());
        }
    });
    result.retain(|name, _| !blocked.contains(name));
    result
}

pub(in crate::cpp_detection) struct Contract {
    end_byte: usize,
    undef_byte: usize,
    arity: usize,
    size_query: bool,
}

pub(in crate::cpp_detection) fn collect(file: &ParsedCppFile) -> HashMap<String, Contract> {
    let Some(tree) = &file.tree else {
        return HashMap::new();
    };
    let mut definitions = HashMap::<String, Vec<tree_sitter::Node<'_>>>::new();
    let mut undefinitions = HashMap::<String, Vec<usize>>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if matches!(node.kind(), "preproc_def" | "preproc_function_def")
            && let Some(name) = node.child_by_field_name("name")
        {
            definitions
                .entry(node_text(name, &file.source).to_owned())
                .or_default()
                .push(node);
        }
        if node.kind() == "preproc_call"
            && node_text(node, &file.source)
                .trim_start()
                .starts_with("#undef")
        {
            for name in identifier_tokens(node_text(node, &file.source)).skip(1) {
                undefinitions
                    .entry(name.to_owned())
                    .or_default()
                    .push(node.start_byte());
            }
        }
    });
    let mut result = HashMap::new();
    for (name, nodes) in &definitions {
        let [node] = nodes.as_slice() else { continue };
        if node.kind() != "preproc_function_def" {
            continue;
        }
        let mut parent = node.parent();
        let mut conditional = false;
        while let Some(scope) = parent {
            conditional |= matches!(
                scope.kind(),
                "preproc_if" | "preproc_ifdef" | "preproc_else" | "preproc_elif"
            );
            parent = scope.parent();
        }
        if conditional {
            continue;
        }
        let (Some(parameters), Some(value)) = (
            node.child_by_field_name("parameters"),
            node.child_by_field_name("value"),
        ) else {
            continue;
        };
        let parameter_text = node_text(parameters, &file.source);
        if parameter_text.contains("...") {
            continue;
        }
        let params = identifier_tokens(parameter_text)
            .map(str::to_owned)
            .collect::<HashSet<_>>();
        let body = node_text(value, &file.source).replace("\\\n", " ");
        if body.len() > 8192 || params.is_empty() || params.len() > 8 {
            continue;
        }
        // Another macro can transform even a seemingly harmless local name.
        if identifier_tokens(&body).any(|word| definitions.contains_key(word)) {
            continue;
        }
        let size_query = size_query_body(&body, &params);
        if size_query || scalar_body(&body, params.clone()) {
            result.insert(
                name.clone(),
                Contract {
                    end_byte: node.end_byte(),
                    undef_byte: undefinitions
                        .get(name)
                        .into_iter()
                        .flatten()
                        .copied()
                        .filter(|position| *position >= node.end_byte())
                        .min()
                        .unwrap_or(usize::MAX),
                    arity: params.len(),
                    size_query,
                },
            );
        }
    }
    result
}

fn size_query_body(body: &str, params: &HashSet<String>) -> bool {
    if !body.contains("sizeof") {
        return false;
    }
    fn operand(node: tree_sitter::Node<'_>, source: &str, params: &HashSet<String>) -> bool {
        match node.kind() {
            "identifier" => params.contains(node_text(node, source)),
            "parenthesized_expression" => node
                .named_child(0)
                .is_some_and(|n| operand(n, source, params)),
            "subscript_expression" => {
                node.child_by_field_name("argument")
                    .is_some_and(|n| operand(n, source, params))
                    && node.child_by_field_name("indices").is_some_and(|indices| {
                        indices.named_child_count() == 1
                            && indices
                                .named_child(0)
                                .is_some_and(|n| n.kind() == "number_literal")
                    })
            }
            _ => false,
        }
    }
    fn expression(node: tree_sitter::Node<'_>, source: &str, params: &HashSet<String>) -> bool {
        match node.kind() {
            "number_literal" => true,
            "parenthesized_expression" => node
                .named_child(0)
                .is_some_and(|n| expression(n, source, params)),
            "sizeof_expression" => node
                .child_by_field_name("value")
                .is_some_and(|n| operand(n, source, params)),
            "binary_expression" => ["left", "right"].iter().all(|side| {
                node.child_by_field_name(side)
                    .is_some_and(|n| expression(n, source, params))
            }),
            _ => false,
        }
    }
    let source = format!("void contract() {{ {body}; }}");
    let mut parser = tree_sitter::Parser::new();
    if parser
        .set_language(&tree_sitter_cpp::LANGUAGE.into())
        .is_err()
    {
        return false;
    }
    let Some(tree) = parser.parse(&source, None) else {
        return false;
    };
    if tree.root_node().has_error() {
        return false;
    }
    tree.root_node()
        .named_child(0)
        .and_then(|f| f.child_by_field_name("body"))
        .filter(|b| b.named_child_count() == 1)
        .and_then(|b| b.named_child(0))
        .filter(|s| s.kind() == "expression_statement")
        .and_then(|s| s.named_child(0))
        .is_some_and(|n| expression(n, &source, params))
}

pub(super) fn queries_array_size(
    contracts: &HashMap<String, Contract>,
    usage: tree_sitter::Node<'_>,
    source: &str,
) -> bool {
    let Some(arguments) = usage.parent().filter(|n| n.kind() == "argument_list") else {
        return false;
    };
    let Some(call) = arguments.parent() else {
        return false;
    };
    if !call.child_by_field_name("function").is_some_and(|n| {
        contracts
            .get(node_text(n, source))
            .is_some_and(|c| c.size_query)
    }) {
        return false;
    }
    let mut ancestor = call.parent();
    while let Some(node) = ancestor {
        if matches!(node.kind(), "argument_list" | "call_expression") {
            return false;
        }
        if matches!(node.kind(), "declaration" | "expression_statement") {
            break;
        }
        ancestor = node.parent();
    }
    preserves_array(contracts, arguments, source, node_text(usage, source), 0)
}

fn scalar_body(body: &str, mut names: HashSet<String>) -> bool {
    let source = format!("void contract() {{ {body}; }}");
    let mut parser = tree_sitter::Parser::new();
    if parser
        .set_language(&tree_sitter_cpp::LANGUAGE.into())
        .is_err()
    {
        return false;
    }
    let Some(tree) = parser.parse(&source, None) else {
        return false;
    };
    if tree.root_node().has_error() {
        return false;
    }
    let Some(body) = tree
        .root_node()
        .named_child(0)
        .and_then(|f| f.child_by_field_name("body"))
    else {
        return false;
    };
    let mut safe = true;
    walk_nodes(body, &mut |node| {
        if node.kind() != "declaration" {
            return;
        }
        if !node
            .child_by_field_name("type")
            .is_some_and(|ty| matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
        {
            safe = false;
        }
        for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
            let name = if declarator.kind() == "init_declarator" {
                declarator.child_by_field_name("declarator")
            } else {
                Some(declarator)
            };
            if let Some(name) = name.filter(|n| n.kind() == "identifier") {
                names.insert(node_text(name, &source).to_owned());
            } else {
                safe = false;
            }
        }
    });
    walk_nodes(body, &mut |node| {
        if !node.is_named() {
            return;
        }
        safe &= match node.kind() {
            "identifier" => names.contains(node_text(node, &source)),
            "compound_statement"
            | "expression_statement"
            | "declaration"
            | "init_declarator"
            | "primitive_type"
            | "sized_type_specifier"
            | "type_qualifier"
            | "parenthesized_expression"
            | "assignment_expression"
            | "binary_expression"
            | "update_expression"
            | "conditional_expression"
            | "number_literal"
            | "char_literal"
            | "true"
            | "false"
            | "do_statement"
            | "while_statement"
            | "if_statement"
            | "else_clause"
            | "condition_clause"
            | "comment" => true,
            _ => false,
        };
    });
    safe
}

pub(in crate::cpp_detection) fn is_scalar_call(
    contracts: &HashMap<String, Contract>,
    call: tree_sitter::Node<'_>,
    source: &str,
) -> bool {
    call.child_by_field_name("function")
        .filter(|n| n.kind() == "identifier")
        .and_then(|n| contracts.get(node_text(n, source)))
        .is_some_and(|contract| {
            !contract.size_query
                && call.start_byte() >= contract.end_byte
                && call.start_byte() < contract.undef_byte
                && call
                    .child_by_field_name("arguments")
                    .is_some_and(|args| args.named_child_count() == contract.arity)
        })
}

pub(in crate::cpp_detection) fn preserves_array(
    contracts: &HashMap<String, Contract>,
    arguments: tree_sitter::Node<'_>,
    source: &str,
    array: &str,
    rank: usize,
) -> bool {
    let Some(call) = arguments.parent().filter(|n| n.kind() == "call_expression") else {
        return false;
    };
    let Some(callee) = call
        .child_by_field_name("function")
        .filter(|n| n.kind() == "identifier")
    else {
        return false;
    };
    let Some(contract) = contracts.get(node_text(callee, source)) else {
        return false;
    };
    if call.start_byte() < contract.end_byte
        || call.start_byte() >= contract.undef_byte
        || arguments.named_child_count() != contract.arity
    {
        return false;
    }
    arguments
        .named_children(&mut arguments.walk())
        .all(|mut arg| {
            while arg.kind() == "parenthesized_expression" {
                let Some(inner) = arg.named_child(0) else {
                    return false;
                };
                arg = inner;
            }
            if matches!(
                arg.kind(),
                "number_literal" | "char_literal" | "true" | "false"
            ) {
                return true;
            }
            let mut dimensions = 0;
            while arg.kind() == "subscript_expression" {
                dimensions += 1;
                let Some(inner) = arg.child_by_field_name("argument") else {
                    return false;
                };
                arg = inner;
            }
            dimensions == rank && arg.kind() == "identifier" && node_text(arg, source) == array
        })
}
