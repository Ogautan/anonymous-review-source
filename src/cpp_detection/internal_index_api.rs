//! Internal free functions are not externally callable partition APIs. Their
//! scalar formals need provenance from a bound caller, unless the callable
//! escapes (for example as a thread entry point) or lookup is ambiguous.
use super::*;
use std::borrow::Cow;
use tree_sitter::Node;

struct Function {
    name: String,
    scope: Vec<String>,
    body: (usize, usize),
    parameters: Vec<Option<String>>,
    signature: Vec<String>,
    pointer_overload_signatures: Vec<Vec<String>>,
    internal: bool,
}

fn closed_body(body: Node<'_>) -> bool {
    body.child(0)
        .is_some_and(|n| n.kind() == "{" && !n.is_missing())
        && body
            .child(body.child_count().saturating_sub(1) as u32)
            .is_some_and(|n| n.kind() == "}" && !n.is_missing())
}

fn namespace_scope(mut node: Node<'_>, source: &str) -> Option<Vec<String>> {
    let mut scope = Vec::new();
    while let Some(parent) = node.parent() {
        match parent.kind() {
            "namespace_definition" => {
                if !closed_body(parent.child_by_field_name("body")?) {
                    return None;
                }
                scope.push(
                    parent
                        .child_by_field_name("name")
                        .map(|name| node_text(name, source).to_owned())
                        .unwrap_or_default(),
                );
            }
            "class_specifier" | "struct_specifier" | "union_specifier" => return None,
            "function_definition" => {
                let mut declarator = parent.child_by_field_name("declarator")?;
                while declarator.kind() != "function_declarator" {
                    declarator = declarator.child_by_field_name("declarator")?;
                }
                if declarator.child_by_field_name("declarator")?.kind() != "identifier" {
                    // An out-of-line member may resolve an unqualified call to
                    // a member declared in another file, not this free function.
                    return None;
                }
            }
            _ => {}
        }
        node = parent;
    }
    scope.reverse();
    Some(scope)
}

fn scalar_parameter(parameter: Node<'_>, source: &str) -> Option<String> {
    let declarator = parameter.child_by_field_name("declarator")?;
    if declarator.kind() != "identifier" {
        return None;
    }
    let ty = parameter.child_by_field_name("type")?;
    let spelling = node_text(ty, source).trim_start_matches("std::");
    if !matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
        && !matches!(
            spelling,
            "size_t"
                | "ptrdiff_t"
                | "intptr_t"
                | "uintptr_t"
                | "int8_t"
                | "int16_t"
                | "int32_t"
                | "int64_t"
                | "uint8_t"
                | "uint16_t"
                | "uint32_t"
                | "uint64_t"
        )
    {
        return None;
    }
    Some(node_text(declarator, source).to_owned())
}

fn signature(parameters: Node<'_>, source: &str) -> Vec<String> {
    parameters
        .named_children(&mut parameters.walk())
        .filter(|p| p.kind() != "comment")
        .map(|p| {
            let ty = p
                .child_by_field_name("type")
                .map(|t| node_text(t, source).split_whitespace().collect::<String>())
                .unwrap_or_default();
            let shape = p
                .child_by_field_name("declarator")
                .map(|d| d.kind())
                .unwrap_or("");
            format!("{ty}:{shape}")
        })
        .collect()
}

fn integral_argument(mut node: Node<'_>, source: &str) -> bool {
    while node.kind() == "parenthesized_expression" {
        let Some(inner) = node.named_child(0) else {
            return false;
        };
        node = inner;
    }
    if primitive_local_operand(node, source) {
        return true;
    }
    if node.kind() == "call_expression" {
        return is_thread_index_expression(&transparent_partition_value(node, source));
    }
    if node.kind() != "identifier" {
        return false;
    }
    let name = node_text(node, source);
    let mut parent = node.parent();
    while let Some(scope) = parent {
        if scope.kind() == "compound_statement" {
            for declaration in scope
                .named_children(&mut scope.walk())
                .filter(|n| n.kind() == "declaration" && n.end_byte() < node.start_byte())
            {
                for declarator in
                    declaration.children_by_field_name("declarator", &mut declaration.walk())
                {
                    if declarator_variable_name(declarator, source).as_deref() == Some(name) {
                        return false;
                    }
                }
            }
        }
        if matches!(scope.kind(), "function_definition" | "lambda_expression") {
            let Some(declarator) = scope.child_by_field_name("declarator") else {
                return false;
            };
            let Some(parameters) = declarator.child_by_field_name("parameters") else {
                return false;
            };
            return parameters
                .named_children(&mut parameters.walk())
                .any(|p| scalar_parameter(p, source).as_deref() == Some(name));
        }
        parent = scope.parent();
    }
    false
}

pub(super) struct Graph {
    functions: HashMap<String, Function>,
    ambiguous: HashSet<String>,
    calls: Vec<(String, usize, Vec<String>)>,
}

pub(super) fn prepare(file: &ParsedCppFile, origins: &mut IndexPartitionOrigins) -> Option<Graph> {
    if !file.allow_internal_linkage_proof {
        return None;
    }
    // A static/anonymous function in a header can be a deliberate API for each
    // including translation unit. Do not close that source boundary here.
    if !Path::new(&file.path)
        .extension()
        .is_some_and(|ext| matches!(ext.to_str(), Some("c" | "cc" | "cpp" | "cxx" | "c++")))
    {
        return None;
    }
    let tree = file.tree.as_ref()?;
    let mut definitions = HashMap::<String, Vec<Function>>::new();
    let mut ambiguous = HashSet::new();
    let mut counts = HashMap::<String, usize>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "function_definition" {
            return;
        }
        let Some(declarator) = node.child_by_field_name("declarator") else {
            return;
        };
        let Some(name) = index_method_name(declarator, &file.source) else {
            return;
        };
        *counts.entry(name.clone()).or_default() += 1;
        let Some(scope) = namespace_scope(node, &file.source) else {
            ambiguous.insert(name);
            return;
        };
        let (Some(identifier), Some(params), Some(body)) = (
            declarator.child_by_field_name("declarator"),
            declarator.child_by_field_name("parameters"),
            node.child_by_field_name("body"),
        ) else {
            return;
        };
        if declarator.has_error() || !closed_body(body) || identifier.kind() != "identifier" {
            ambiguous.insert(name);
            return;
        }
        let parameters = params
            .named_children(&mut params.walk())
            .filter(|p| p.kind() != "comment")
            .map(|p| scalar_parameter(p, &file.source))
            .collect::<Vec<_>>();
        let explicit_static = node.named_children(&mut node.walk()).any(|child| {
            child.kind() == "storage_class_specifier" && node_text(child, &file.source) == "static"
        });
        definitions.entry(name.clone()).or_default().push(Function {
            name,
            scope: scope.clone(),
            body: (body.start_position().row + 1, body.end_position().row + 1),
            parameters,
            signature: signature(params, &file.source),
            pointer_overload_signatures: Vec::new(),
            internal: explicit_static || scope.iter().any(String::is_empty),
        });
    });
    let mut functions = HashMap::new();
    for (name, mut group) in definitions {
        let scalar = group
            .iter()
            .enumerate()
            .filter(|(_, f)| f.parameters.len() == 1 && f.parameters[0].is_some())
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        let separable_overloads = group.len() > 1
            && scalar.len() == 1
            && group
                .iter()
                .all(|f| f.internal && f.scope == group[0].scope)
            && group.iter().enumerate().all(|(i, f)| {
                i == scalar[0]
                    || (f.signature.len() == 1 && f.signature[0].ends_with(":pointer_declarator"))
            });
        if counts.get(&name) != Some(&group.len()) || (group.len() != 1 && !separable_overloads) {
            ambiguous.insert(name.clone());
        }
        let mut selected = group.swap_remove(if separable_overloads { scalar[0] } else { 0 });
        if separable_overloads {
            selected.pointer_overload_signatures = group.into_iter().map(|f| f.signature).collect();
        }
        functions.insert(name, selected);
    }
    if !functions.values().any(|f| f.internal) {
        return None;
    }
    for function in functions.values() {
        if origins
            .regions
            .iter()
            .filter(|(a, b, _)| (*a, *b) == function.body)
            .count()
            != 1
        {
            // Existing origins use line ranges. Same-line functions/lambdas
            // cannot safely share an API-seed removal or caller projection.
            ambiguous.insert(function.name.clone());
        }
    }
    let mut calls = Vec::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(node.kind(), "identifier" | "field_identifier") {
            return;
        }
        let name = node_text(node, &file.source);
        let Some(function) = functions.get(name) else {
            return;
        };
        let Some(parent) = node.parent() else { return };
        if parent.kind() == "function_declarator"
            && parent.child_by_field_name("declarator") == Some(node)
        {
            // A prototype with a different shape may denote another overload.
            if namespace_scope(parent, &file.source).as_ref() != Some(&function.scope)
                || parent
                    .child_by_field_name("parameters")
                    .is_none_or(|params| {
                        let signature = signature(params, &file.source);
                        signature != function.signature
                            && !function.pointer_overload_signatures.contains(&signature)
                    })
            {
                ambiguous.insert(name.to_owned());
            }
            return;
        }
        if parent.kind() != "call_expression"
            || parent.child_by_field_name("function") != Some(node)
        {
            // Includes address-taking, callback registration, qualified/indirect
            // lookup, local shadows, exports, and unexpanded syntax.
            ambiguous.insert(name.to_owned());
            return;
        }
        let Some(scope) = namespace_scope(parent, &file.source) else {
            ambiguous.insert(name.to_owned());
            return;
        };
        if !scope.starts_with(&function.scope) {
            ambiguous.insert(name.to_owned());
            return;
        }
        let Some(arguments) = parent.child_by_field_name("arguments") else {
            return;
        };
        let arguments = arguments
            .named_children(&mut arguments.walk())
            .filter(|a| a.kind() != "comment")
            .map(|a| {
                if !function.pointer_overload_signatures.is_empty()
                    && !integral_argument(a, &file.source)
                {
                    String::new()
                } else {
                    transparent_partition_value(a, &file.source)
                }
            })
            .collect::<Vec<_>>();
        if arguments.len() != function.parameters.len() || parent.has_error() {
            ambiguous.insert(name.to_owned());
            return;
        }
        calls.push((name.to_owned(), parent.start_position().row + 1, arguments));
    });
    // Separate entry paths can pass different fixed slots (e.g. two thread
    // lambdas call update(0)/update(1)). Those callers need a pair/phase model;
    // lack of a variable partition expression is not a seriality proof.
    let mut literal_arguments = HashMap::<(String, usize), HashSet<i128>>::new();
    for (name, _, arguments) in &calls {
        for (position, argument) in arguments.iter().enumerate() {
            if let Ok(value) = argument
                .trim()
                .trim_end_matches(['u', 'U', 'l', 'L'])
                .parse::<i128>()
            {
                literal_arguments
                    .entry((name.clone(), position))
                    .or_default()
                    .insert(value);
            }
        }
    }
    ambiguous.extend(
        literal_arguments
            .into_iter()
            .filter_map(|((name, _), values)| (values.len() > 1).then_some(name)),
    );
    // Do not close a callable whose identity is mentioned by preprocessing.
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "ERROR"
            || (node.kind().starts_with("preproc_")
                && !matches!(
                    node.kind(),
                    "preproc_if" | "preproc_ifdef" | "preproc_elif" | "preproc_else"
                ))
        {
            for name in identifier_tokens(node_text(node, &file.source)) {
                if functions.contains_key(name) {
                    ambiguous.insert(name.to_owned());
                }
            }
        }
    });
    for function in functions
        .values()
        .filter(|f| f.internal && !ambiguous.contains(&f.name))
    {
        if let Some((_, _, parameters)) = origins
            .regions
            .iter_mut()
            .find(|(a, b, _)| (*a, *b) == function.body)
        {
            // Unknown descriptor/custom scalar formals retain their existing
            // treatment. Only these bound integral API-name seeds are removed.
            for parameter in function.parameters.iter().flatten() {
                parameters.remove(parameter);
            }
        }
    }
    Some(Graph {
        functions,
        ambiguous,
        calls,
    })
}

impl Graph {
    pub(super) fn propagate(&self, origins: &mut IndexPartitionOrigins) {
        let Self {
            functions,
            ambiguous,
            calls,
        } = self;
        // Recompute from surviving API/runtime roots, including anonymous namespace
        // helpers. Recursive internal calls cannot manufacture an API root.
        for _ in 0..4 {
            let mut additions = Vec::new();
            for (name, line, arguments) in calls {
                if ambiguous.contains(name) {
                    continue;
                }
                let function = &functions[name];
                if !function.internal {
                    continue;
                }
                for (argument, parameter) in arguments.iter().zip(&function.parameters) {
                    if let Some(parameter) = parameter
                        && origins.supports_parallel_argument(argument, *line)
                    {
                        additions.push((
                            function.body,
                            parameter.clone(),
                            origins.supports_runtime_identity(argument, *line),
                        ));
                    }
                }
            }
            let mut changed = false;
            for ((begin, end), parameter, runtime) in additions {
                if runtime {
                    changed |= origins
                        .runtime_parameters
                        .insert((begin, end, parameter.clone()));
                }
                if let Some((_, _, parameters)) = origins
                    .regions
                    .iter_mut()
                    .find(|(a, b, _)| (*a, *b) == (begin, end))
                {
                    changed |= parameters.insert(parameter);
                }
            }
            if !changed {
                break;
            }
        }
    }
}

/// Linkage proofs require the source spelling to survive preprocessing. Keep
/// unknown forced headers/response files and keyword overrides conservative.
pub(super) fn views<'a>(
    files: &'a [ParsedCppFile],
    commands: &[super::super::types::CppCompileCommand],
) -> Cow<'a, [ParsedCppFile]> {
    let keyword = |value: &str| {
        let name = value.split(['=', '(']).next().unwrap_or("");
        matches!(name, "static" | "namespace") || name.contains('\\')
    };
    let mut opaque = commands.iter().any(|command| {
        command.arguments.iter().enumerate().any(|(index, arg)| {
            arg.starts_with('@')
                || arg.starts_with("-include")
                || arg.starts_with("-imacros")
                || arg.starts_with("/FI")
                || ["-D", "-U", "/D", "/U"].iter().any(|prefix| {
                    arg.strip_prefix(prefix).is_some_and(|value| {
                        if value.is_empty() {
                            command
                                .arguments
                                .get(index + 1)
                                .is_some_and(|value| keyword(value))
                        } else {
                            keyword(value)
                        }
                    })
                })
        })
    });
    if !opaque {
        for file in files {
            if !file.source.contains('#') {
                continue;
            }
            let Some(tree) = &file.tree else { continue };
            walk_nodes(tree.root_node(), &mut |node| {
                if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                    && let Some(name) = node.child_by_field_name("name")
                {
                    opaque |= keyword(node_text(name, &file.source))
                        || file.source[name.end_byte()..].starts_with("\\\n")
                        || file.source[name.end_byte()..].starts_with("\\\r\n");
                }
                if node.kind() == "preproc_call" {
                    let logical = node_text(node, &file.source)
                        .replace("\\\n", "")
                        .replace("\\\r\n", "");
                    opaque |= logical
                        .trim_start()
                        .strip_prefix('#')
                        .is_some_and(|directive| directive.trim_start().starts_with("define"));
                }
            });
            if opaque {
                break;
            }
        }
    }
    if !opaque || files.iter().all(|f| !f.allow_internal_linkage_proof) {
        return Cow::Borrowed(files);
    }
    let mut views = files.to_vec();
    for file in &mut views {
        file.allow_internal_linkage_proof = false;
    }
    Cow::Owned(views)
}
