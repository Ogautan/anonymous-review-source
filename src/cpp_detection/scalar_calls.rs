//! Source-declared value parameters: C prototypes and unique C++ static definitions.
use super::*;

pub(in crate::cpp_detection) struct Contract {
    start: usize,
    scalar: Vec<bool>,
}

pub(in crate::cpp_detection) fn collect(file: &ParsedCppFile) -> HashMap<String, Contract> {
    let Some(tree) = &file.tree else {
        return HashMap::new();
    };
    let mut declarations = HashMap::<String, Vec<tree_sitter::Node<'_>>>::new();
    let mut blocked = HashSet::new();
    let mut imported_overloads = false;
    let mut math_header_start = None;
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "preproc_include"
            && node
                .parent()
                .is_some_and(|p| p.kind() == "translation_unit")
            && node
                .child_by_field_name("path")
                .is_some_and(|path| node_text(path, &file.source) == "<math.h>")
        {
            math_header_start.get_or_insert(node.end_byte());
        }
        imported_overloads |= matches!(
            node.kind(),
            "preproc_include"
                | "using_declaration"
                | "namespace_alias_definition"
                | "import_declaration"
        );
        if node.kind() == "function_declarator" {
            if let Some(name) = node.child_by_field_name("declarator") {
                declarations
                    .entry(node_text(name, &file.source).to_owned())
                    .or_default()
                    .push(node);
            }
        } else if matches!(node.kind(), "preproc_def" | "preproc_function_def") {
            if let Some(name) = node.child_by_field_name("name") {
                blocked.insert(node_text(name, &file.source).to_owned());
            }
        } else if matches!(
            node.kind(),
            "init_declarator" | "parameter_declaration" | "declaration" | "field_declaration"
        ) && let Some(name) = node
            .child_by_field_name("declarator")
            .and_then(|d| declarator_variable_name(d, &file.source))
        {
            blocked.insert(name);
        }
    });
    // C cannot overload a declared function. In C++, unseen header/import
    // declarations could select a reference overload instead of this copy.
    if !file.is_c && imported_overloads {
        return HashMap::new();
    }
    let mut result = HashMap::new();
    if file.is_c
        && let Some(start) = math_header_start
    {
        // Standard C real-math functions take scalar values. Do not borrow
        // this contract for a project macro/declaration or a C++ overload.
        // Pointer-output functions (frexp/modf/remquo) and nan's string
        // argument are deliberately absent from this scalar-only catalog.
        for (names, arity) in [
            (
                "acos asin atan acosh asinh atanh cos sin tan cosh sinh tanh exp exp2 expm1 log log10 log1p log2 logb ilogb cbrt fabs sqrt erf erfc lgamma tgamma ceil floor nearbyint rint lrint llrint round lround llround trunc",
                1,
            ),
            (
                "atan2 ldexp scalbn scalbln pow hypot fmod remainder copysign nextafter nexttoward fdim fmax fmin",
                2,
            ),
            ("fma", 3),
        ] {
            for base in names.split_whitespace() {
                for suffix in ["", "f", "l"] {
                    let name = format!("{base}{suffix}");
                    if !blocked.contains(&name) && !declarations.contains_key(&name) {
                        result.insert(
                            name,
                            Contract {
                                start,
                                scalar: vec![true; arity],
                            },
                        );
                    }
                }
            }
        }
    }
    for (name, decls) in declarations {
        if file.is_c && !blocked.contains(&name) {
            let mut signatures = Vec::new();
            let mut start = usize::MAX;
            let mut supported = true;
            for declarator in &decls {
                let Some(declaration) = declarator.parent().filter(|node| {
                    matches!(node.kind(), "declaration" | "function_definition")
                        && node
                            .parent()
                            .is_some_and(|parent| parent.kind() == "translation_unit")
                        && !declarator.has_error()
                }) else {
                    supported = false;
                    break;
                };
                let Some(parameters) = declarator.child_by_field_name("parameters") else {
                    supported = false;
                    break;
                };
                if node_text(parameters, &file.source).contains("...") {
                    supported = false;
                    break;
                }
                let scalar = parameters
                    .named_children(&mut parameters.walk())
                    .map(|parameter| {
                        parameter.kind() == "parameter_declaration"
                            && parameter.child_by_field_name("type").is_some_and(|ty| {
                                matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                            })
                            && parameter
                                .child_by_field_name("declarator")
                                .is_none_or(|shape| shape.kind() == "identifier")
                    })
                    .collect::<Vec<_>>();
                start = start.min(declaration.start_byte());
                signatures.push(scalar);
            }
            if supported && let Some(first) = signatures.first() {
                // All visible declarations must agree about each position.
                // C has no overload selection that could bind an lvalue to
                // a different reference-taking function in another header.
                if signatures.iter().all(|signature| signature == first) {
                    result.insert(
                        name,
                        Contract {
                            start,
                            scalar: first.clone(),
                        },
                    );
                }
            }
            continue;
        }
        let [declarator] = decls.as_slice() else {
            continue;
        };
        if blocked.contains(&name) || declarator.has_error() {
            continue;
        }
        let Some(definition) = declarator
            .parent()
            .filter(|n| n.kind() == "function_definition")
        else {
            continue;
        };
        if definition
            .parent()
            .is_none_or(|n| n.kind() != "translation_unit")
        {
            continue;
        }
        let Some(body) = definition.child_by_field_name("body") else {
            continue;
        };
        if !identifier_tokens(&file.source[definition.start_byte()..body.start_byte()])
            .any(|t| t == "static")
        {
            continue;
        }
        let Some(parameters) = declarator.child_by_field_name("parameters") else {
            continue;
        };
        if node_text(parameters, &file.source).contains("...") {
            continue;
        }
        let scalar = parameters
            .named_children(&mut parameters.walk())
            .map(|parameter| {
                parameter.kind() == "parameter_declaration"
                    && parameter.child_by_field_name("type").is_some_and(|ty| {
                        matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                    })
                    && parameter
                        .child_by_field_name("declarator")
                        .is_some_and(|d| d.kind() == "identifier")
            })
            .collect();
        result.insert(
            name,
            Contract {
                start: definition.start_byte(),
                scalar,
            },
        );
    }
    result
}

/// A bound ordinary C call cannot reach automatic scalar locals unless their
/// address escaped. The caller must separately track address-taking and effects.
pub(in crate::cpp_detection) fn declared_c_call(
    contracts: &HashMap<String, Contract>,
    call: tree_sitter::Node<'_>,
    source: &str,
) -> bool {
    call.child_by_field_name("function")
        .filter(|callee| callee.kind() == "identifier")
        .and_then(|callee| contracts.get(node_text(callee, source)))
        .is_some_and(|contract| {
            call.start_byte() >= contract.start
                && call
                    .child_by_field_name("arguments")
                    .is_some_and(|args| args.named_child_count() == contract.scalar.len())
        })
}

pub(in crate::cpp_detection) fn consumes_value(
    contracts: &HashMap<String, Contract>,
    arguments: tree_sitter::Node<'_>,
    element: tree_sitter::Node<'_>,
    source: &str,
) -> bool {
    let Some(call) = arguments.parent().filter(|n| n.kind() == "call_expression") else {
        return false;
    };
    let Some(function) = call
        .child_by_field_name("function")
        .filter(|n| n.kind() == "identifier")
    else {
        return false;
    };
    let Some(contract) = contracts.get(node_text(function, source)) else {
        return false;
    };
    if call.start_byte() < contract.start || arguments.named_child_count() != contract.scalar.len()
    {
        return false;
    }
    let mut scope = call.parent();
    while let Some(node) = scope {
        // An outer macro can inspect or duplicate the original argument
        // tokens, including taking their address. A scalar inner call alone
        // does not prove that the complete enclosing expression consumes a
        // value; require a declared ordinary call at each enclosing call.
        if node.kind() == "call_expression"
            && node.child_by_field_name("function").is_none_or(|callee| {
                callee.kind() != "identifier" || !contracts.contains_key(node_text(callee, source))
            })
        {
            return false;
        }
        if matches!(
            node.kind(),
            "class_specifier"
                | "struct_specifier"
                | "namespace_definition"
                | "lambda_expression"
                | "ERROR"
        ) {
            return false;
        }
        if node.kind() == "function_definition"
            && node
                .child_by_field_name("declarator")
                .and_then(|d| d.child_by_field_name("declarator"))
                .is_some_and(|n| n.kind() == "qualified_identifier")
        {
            return false;
        }
        scope = node.parent();
    }
    arguments
        .named_children(&mut arguments.walk())
        .enumerate()
        .any(|(index, mut argument)| {
            while argument.kind() == "parenthesized_expression" {
                let Some(inner) = argument.named_child(0) else {
                    return false;
                };
                argument = inner;
            }
            argument == element && contract.scalar[index]
        })
}
