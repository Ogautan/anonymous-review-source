//! Positive source proofs for accesses to freshly allocated C storage and
//! source-proved automatic value storage. Ranges end at the first possible alias, publication, handoff or
//! lifetime change; they do not claim that an object stays immutable afterward.

use std::collections::{HashMap, HashSet};
use std::path::{Component, Path, PathBuf};

use tree_sitter::{Node, Parser};

use super::parser::{ParsedCppFile, node_text, walk_nodes};

#[path = "allocator_attributes.rs"]
mod allocator_attributes;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FreshInitializationRange {
    pub receiver: String,
    /// Start byte of the lexical declaration, matching the access binding.
    pub declaration: usize,
    pub begin: usize,
    pub end: usize,
}

impl FreshInitializationRange {
    pub fn contains(&self, receiver: &str, declaration: usize, access: usize) -> bool {
        self.receiver == receiver
            && self.declaration == declaration
            && self.begin <= access
            && access < self.end
    }
}

struct Variable<'a> {
    name: String,
    declaration: usize,
    begin: usize,
    scope: Node<'a>,
    pointer: bool,
    local: bool,
    declaration_node: Node<'a>,
    declarator: Node<'a>,
}

struct FileFacts<'a> {
    file: &'a ParsedCppFile,
    variables: HashMap<String, Vec<Variable<'a>>>,
    occurrences: HashMap<String, Vec<Node<'a>>>,
    jumping_functions: HashSet<usize>,
    syntax_errors: Vec<Node<'a>>,
    scalar_parameters:
        std::cell::OnceCell<HashMap<String, super::evidence::scalar_calls::Contract>>,
    element_effects: std::cell::OnceCell<ElementEffectIndex>,
}

#[derive(Default)]
struct Allocators {
    fresh: HashSet<String>,
    synchronous_memory: HashSet<String>,
    /// Restricted summaries (macros/static functions) require a visible source
    /// definition. A missing file or too-early use means unresolved scope.
    availability: HashMap<String, HashMap<String, usize>>,
}

impl Allocators {
    fn available(&self, name: &str, file: &str, offset: usize) -> bool {
        self.availability
            .get(name)
            .is_none_or(|files| files.get(file).is_some_and(|begin| *begin <= offset))
    }
}

struct AllocationMacro {
    body: String,
    parameters: HashSet<String>,
    file: usize,
    end: usize,
    unconditional: bool,
}

#[derive(Clone)]
struct ElementEffect {
    start: usize,
    end: usize,
    undef: usize,
    safe: Vec<bool>,
}

#[derive(Default)]
struct ElementEffectIndex {
    functions: HashMap<String, ElementEffect>,
    macros: HashMap<String, ElementEffect>,
    macro_names: HashSet<String>,
    value_functions: HashSet<String>,
    declared_functions: HashSet<String>,
    intrinsic_header: bool,
    math_header: bool,
}

/// Declaration-only alignment macros may be erased for an ownership parse,
/// never for layout calculation. Require a visible definition and agreement
/// across every source definition; unknown include paths remain unresolved.
pub(super) fn alignment_macro_visibility(
    files: &[ParsedCppFile],
) -> HashMap<String, HashMap<String, usize>> {
    let facts = files
        .iter()
        .map(|file| FileFacts {
            file,
            variables: HashMap::new(),
            occurrences: HashMap::new(),
            jumping_functions: HashSet::new(),
            syntax_errors: Vec::new(),
            scalar_parameters: std::cell::OnceCell::new(),
            element_effects: std::cell::OnceCell::new(),
        })
        .collect::<Vec<_>>();
    let mut definitions: HashMap<String, Vec<AllocationMacro>> = HashMap::new();
    let mut blocked = HashSet::new();
    for (index, facts) in facts.iter().enumerate() {
        let Some(tree) = &facts.file.tree else {
            continue;
        };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() == "preproc_call"
                && let Some(directive) = node_text(node, &facts.file.source)
                    .trim_start()
                    .strip_prefix('#')
            {
                let mut tokens = directive.split_whitespace();
                if tokens.next() == Some("undef")
                    && let Some(name) = tokens.next()
                {
                    blocked.insert(name.to_owned());
                }
            }
            if !matches!(node.kind(), "preproc_def" | "preproc_function_def") {
                return;
            }
            let Some(name) = node.child_by_field_name("name") else {
                return;
            };
            let name = node_text(name, &facts.file.source).to_owned();
            let body = node
                .child_by_field_name("value")
                .map(|n| node_text(n, &facts.file.source))
                .unwrap_or("");
            let compact = body.split_whitespace().collect::<String>();
            let alignment = compact
                .strip_prefix("__attribute__((aligned(")
                .and_then(|s| s.strip_suffix(")))"));
            let valid =
                alignment.is_some_and(|s| s.parse::<usize>().is_ok_and(|n| n.is_power_of_two()));
            if node.kind() != "preproc_def" || !valid {
                blocked.insert(name);
                return;
            }
            definitions.entry(name).or_default().push(AllocationMacro {
                body: body.to_owned(),
                parameters: HashSet::new(),
                file: index,
                end: node.end_byte(),
                unconditional: unconditionally_preprocessed(node, &facts.file.source),
            });
        });
    }
    let edges = macro_include_edges(&facts);
    let mut result = HashMap::<String, HashMap<String, usize>>::new();
    for (name, variants) in definitions {
        if blocked.contains(&name) {
            continue;
        }
        for (path, begin) in macro_visibility(&facts, &variants, &edges) {
            result.entry(path).or_default().insert(name.clone(), begin);
        }
    }
    result
}

/// Static C helpers whose native pointer parameters are used only as scalar
/// elements. Declared C calls may consume scalar copies; opaque calls/names,
/// aliases and address-taking fail closed.
fn local_c_element_helpers(facts: &FileFacts<'_>) -> HashMap<String, Vec<bool>> {
    let mut result = HashMap::new();
    if !facts.file.is_c {
        return result;
    }
    let Some(tree) = &facts.file.tree else {
        return result;
    };
    let source = &facts.file.source;
    let scalar_calls = facts
        .scalar_parameters
        .get_or_init(|| super::evidence::scalar_calls::collect(facts.file));
    let scalar_macros = super::evidence::scalar_macros::collect(facts.file);
    let literal_macros = super::evidence::scalar_macros::literal_objects(facts.file);
    let mut macros = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if matches!(node.kind(), "preproc_def" | "preproc_function_def")
            && let Some(name) = node.child_by_field_name("name")
        {
            macros.insert(node_text(name, source));
        }
    });
    walk_nodes(tree.root_node(), &mut |function| {
        if function.kind() != "function_definition"
            || function.has_error()
            || function
                .parent()
                .is_none_or(|n| n.kind() != "translation_unit")
        {
            return;
        }
        let Some(body) = function.child_by_field_name("body") else {
            return;
        };
        if super::evidence::automatic_storage_scope_may_fork(node_text(body, source)) {
            return;
        }
        if !source[function.start_byte()..body.start_byte()]
            .split_whitespace()
            .any(|s| s == "static")
        {
            return;
        }
        let Some(name) = callable_name(function, source) else {
            return;
        };
        let Some(parameters) = function
            .child_by_field_name("declarator")
            .and_then(|n| n.child_by_field_name("parameters"))
        else {
            return;
        };
        let mut opaque = source[function.start_byte()..body.start_byte()]
            .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
            .any(|name| {
                macros.contains(name)
                    && literal_macros
                        .get(name)
                        .is_none_or(|end| *end > function.start_byte())
            });
        // A macro may occupy a type/keyword position, or syntax the parser
        // does not expose as an identifier. Only subtract verified call-site
        // tokens; every other macro occurrence keeps the body unresolved.
        let mut unresolved_macros = HashMap::<&str, usize>::new();
        for name in node_text(body, source)
            .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
            .filter(|name| macros.contains(name))
        {
            *unresolved_macros.entry(name).or_default() += 1;
        }
        // Bounds and type expressions of other parameters may execute at
        // function entry and publish this parameter before the body starts.
        walk_nodes(parameters, &mut |node| {
            opaque |= matches!(
                node.kind(),
                "call_expression" | "assignment_expression" | "update_expression"
            );
            if node.kind() == "array_declarator" {
                opaque |= node
                    .child_by_field_name("size")
                    .is_some_and(|n| !constant_c_array_bound(n, source, &literal_macros));
            }
        });
        walk_nodes(body, &mut |node| {
            opaque |= matches!(
                node.kind(),
                "field_expression"
                    | "function_definition"
                    | "goto_statement"
                    | "gnu_asm_expression"
            );
            if node.kind() == "call_expression" {
                if super::evidence::scalar_macros::is_scalar_call(&scalar_macros, node, source)
                    && let Some(callee) = node.child_by_field_name("function")
                    && let Some(count) = unresolved_macros.get_mut(node_text(callee, source))
                {
                    *count = count.saturating_sub(1);
                }
                opaque |=
                    !super::evidence::scalar_calls::declared_c_call(scalar_calls, node, source)
                        && !super::evidence::scalar_macros::is_scalar_call(
                            &scalar_macros,
                            node,
                            source,
                        );
            }
            if node.kind() == "identifier" {
                let name = node_text(node, source);
                let literal_macro = literal_macros
                    .get(name)
                    .is_some_and(|end| *end <= node.start_byte());
                if literal_macro && let Some(count) = unresolved_macros.get_mut(name) {
                    *count = count.saturating_sub(1);
                }
                let ordinary_callee = node.parent().is_some_and(|call| {
                    call.kind() == "call_expression"
                        && call.child_by_field_name("function") == Some(node)
                        && super::evidence::scalar_calls::declared_c_call(
                            scalar_calls,
                            call,
                            source,
                        )
                });
                let scalar_macro_callee = node.parent().is_some_and(|call| {
                    call.kind() == "call_expression"
                        && call.child_by_field_name("function") == Some(node)
                        && super::evidence::scalar_macros::is_scalar_call(
                            &scalar_macros,
                            call,
                            source,
                        )
                });
                opaque |= (macros.contains(name) && !scalar_macro_callee && !literal_macro)
                    || (!ordinary_callee
                        && !scalar_macro_callee
                        && !literal_macro
                        && binding(facts, name, node.start_byte()).is_none());
            }
        });
        opaque |= unresolved_macros.values().any(|count| *count != 0);
        if opaque {
            return;
        }
        let mut mask = Vec::new();
        for parameter in parameters.named_children(&mut parameters.walk()) {
            let variable = parameter
                .child_by_field_name("declarator")
                .and_then(variable_name)
                .and_then(|name| facts.variables.get(node_text(name, source)))
                .into_iter()
                .flatten()
                .find(|v| v.declaration == parameter.start_byte());
            let safe = variable.is_some_and(|variable| {
                if !primitive_c_element_parameter(variable, source, &literal_macros) {
                    return false;
                }
                facts
                    .occurrences
                    .get(&variable.name)
                    .into_iter()
                    .flatten()
                    .filter(|usage| {
                        body.start_byte() < usage.start_byte() && usage.end_byte() < body.end_byte()
                    })
                    .filter(|usage| {
                        binding(facts, &variable.name, usage.start_byte())
                            .is_some_and(|v| v.declaration == variable.declaration)
                    })
                    .all(|usage| {
                        let mut operand = *usage;
                        while let Some(parent) = operand.parent() {
                            if parent.kind() != "parenthesized_expression" {
                                break;
                            }
                            operand = parent;
                        }
                        let Some(mut element) = operand.parent().filter(|p| {
                            (p.kind() == "subscript_expression"
                                || (p.kind() == "pointer_expression"
                                    && p.child_by_field_name("operator")
                                        .is_some_and(|op| node_text(op, source) == "*")))
                                && p.child_by_field_name("argument") == Some(operand)
                        }) else {
                            return false;
                        };
                        while let Some(parent) = element.parent() {
                            if parent.kind() == "argument_list" {
                                if super::evidence::scalar_macros::preserves_array(
                                    &scalar_macros,
                                    parent,
                                    source,
                                    &variable.name,
                                    1,
                                ) {
                                    // Unlike a C value-returning function, an
                                    // identity macro may preserve the lvalue.
                                    // Check enclosing address-taking as well.
                                    element = parent.parent().unwrap();
                                    continue;
                                }
                                return super::evidence::scalar_calls::consumes_value(
                                    scalar_calls,
                                    parent,
                                    element,
                                    source,
                                );
                            }
                            if matches!(
                                parent.kind(),
                                "pointer_expression" | "subscript_expression"
                            ) {
                                return false;
                            }
                            if matches!(
                                parent.kind(),
                                "expression_statement"
                                    | "return_statement"
                                    | "declaration"
                                    | "condition_clause"
                            ) {
                                return true;
                            }
                            element = parent;
                        }
                        false
                    })
            });
            mask.push(safe);
        }
        if mask.iter().any(|v| *v) {
            result.insert(name, mask);
        }
    });
    result
}

fn constant_c_array_bound(node: Node<'_>, source: &str, literals: &HashMap<String, usize>) -> bool {
    match node.kind() {
        "number_literal" => true,
        "identifier" => literals
            .get(node_text(node, source))
            .is_some_and(|end| *end <= node.start_byte()),
        "parenthesized_expression" => node
            .named_child(0)
            .is_some_and(|n| constant_c_array_bound(n, source, literals)),
        "binary_expression" => {
            node.child_by_field_name("operator").is_some_and(|op| {
                matches!(
                    node_text(op, source),
                    "+" | "-" | "*" | "/" | "%" | "<<" | ">>" | "&" | "|" | "^"
                )
            }) && node
                .child_by_field_name("left")
                .is_some_and(|n| constant_c_array_bound(n, source, literals))
                && node
                    .child_by_field_name("right")
                    .is_some_and(|n| constant_c_array_bound(n, source, literals))
        }
        _ => false,
    }
}

// C adjusts a one-dimensional array parameter to a pointer. Only constant
// or omitted bounds are accepted: VLA bounds can evaluate and publish p.
fn primitive_c_element_parameter(
    variable: &Variable<'_>,
    source: &str,
    literals: &HashMap<String, usize>,
) -> bool {
    primitive_pointer(variable)
        || (variable.declaration_node.kind() == "parameter_declaration"
            && variable
                .declaration_node
                .child_by_field_name("type")
                .is_some_and(|ty| matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
            && variable.declarator.kind() == "array_declarator"
            && variable
                .declarator
                .child_by_field_name("declarator")
                .is_some_and(|n| n.kind() == "identifier")
            && variable
                .declarator
                .child_by_field_name("size")
                .is_none_or(|n| constant_c_array_bound(n, source, literals)))
}

/// Pointer arguments to standard memory operations or verified local C element
/// helpers whose return value is discarded. Saving a returned pointer can publish it.
pub(super) fn discarded_memory_arguments(
    files: &[ParsedCppFile],
    commands: &[super::types::CppCompileCommand],
) -> HashMap<String, HashSet<usize>> {
    let facts = files.iter().map(prepare_file).collect::<Vec<_>>();
    let allocators = allocator_summaries(&facts, commands);
    // A visible C++ prototype may add an overload selected by this array.
    // Until its full signature is resolved, do not borrow the builtin contract.
    let mut declared_cpp = HashSet::new();
    for facts in &facts {
        if !facts.file.is_c
            && let Some(tree) = &facts.file.tree
        {
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() == "function_declarator"
                    && let Some(name) = callable_name(node, &facts.file.source)
                {
                    declared_cpp.insert(name);
                }
            });
        }
    }
    let mut result = HashMap::new();
    for facts in &facts {
        let helpers = local_c_element_helpers(facts);
        let contracts = facts
            .scalar_parameters
            .get_or_init(|| super::evidence::scalar_calls::collect(facts.file));
        let mut uses = HashSet::new();
        if let Some(tree) = &facts.file.tree {
            walk_nodes(tree.root_node(), &mut |call| {
                if call.kind() != "call_expression"
                    || call
                        .parent()
                        .is_none_or(|p| p.kind() != "expression_statement")
                {
                    return;
                }
                let Some(callee) = call.child_by_field_name("function") else {
                    return;
                };
                let text = node_text(callee, &facts.file.source);
                let name = short_name(text);
                if facts.file.is_c
                    && let Some(mask) = helpers.get(name)
                    && super::evidence::scalar_calls::declared_c_call(
                        contracts,
                        call,
                        &facts.file.source,
                    )
                    && let Some(arguments) = call.child_by_field_name("arguments")
                    && arguments.named_child_count() == mask.len()
                {
                    for (index, safe) in mask.iter().enumerate() {
                        if *safe
                            && let Some(argument) = arguments.named_child(index as u32)
                            && let Some(base) = memory_argument_base(facts, argument, &allocators)
                        {
                            uses.insert(base.start_byte());
                        }
                    }
                    return;
                }
                if !matches!(
                    text,
                    "memset"
                        | "memcpy"
                        | "memmove"
                        | "::memset"
                        | "::memcpy"
                        | "::memmove"
                        | "std::memset"
                        | "std::memcpy"
                        | "std::memmove"
                ) || declared_cpp.contains(name)
                    || !allocators.synchronous_memory.contains(name)
                    || binding(facts, name, call.start_byte()).is_some()
                {
                    return;
                }
                let Some(arguments) = call.child_by_field_name("arguments") else {
                    return;
                };
                if arguments.named_child_count() != 3 {
                    return;
                }
                for index in 0..if name == "memset" { 1 } else { 2 } {
                    if let Some(argument) = arguments.named_child(index)
                        && let Some(base) = memory_argument_base(facts, argument, &allocators)
                    {
                        uses.insert(base.start_byte());
                    }
                }
            });
        }
        result.insert(facts.file.path.clone(), uses);
    }
    result
}

/// Effects for visible helpers and function-like macros that consume a scalar
/// element without retaining its address.  The summary is deliberately small:
/// pointer/reference parameters are admitted only when every use reaches a
/// visible value helper or a compiler intrinsic with a visible SIMD header.
/// Unknown calls, returns, pointer rebinding and nested captures stay opaque.
fn element_effects<'a, 'tree>(facts: &'a FileFacts<'tree>) -> &'a ElementEffectIndex {
    facts
        .element_effects
        .get_or_init(|| collect_element_effects(facts))
}

struct ElementParameter {
    name: String,
    declaration: usize,
    by_value: bool,
    scalar_reference: bool,
}

struct ElementFunction<'tree> {
    name: String,
    start: usize,
    body: Node<'tree>,
    parameters: Vec<ElementParameter>,
    return_by_value: bool,
}

fn collect_element_effects(facts: &FileFacts<'_>) -> ElementEffectIndex {
    let source = &facts.file.source;
    let Some(tree) = &facts.file.tree else {
        return ElementEffectIndex::default();
    };
    let intrinsic_header = walk_has_intrinsic_header(tree.root_node(), source);
    let math_header = walk_has_math_header(tree.root_node(), source);
    let mut definitions: HashMap<String, Vec<Node<'_>>> = HashMap::new();
    let mut declared_functions = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "function_declarator"
            && let Some(name) = node.child_by_field_name("declarator")
        {
            declared_functions.insert(short_name(node_text(name, source)).to_owned());
        }
        if node.kind() == "function_definition"
            && top_level_preprocessed_definition(node)
            && node
                .child_by_field_name("body")
                .is_some_and(|body| !body.has_error())
            && let Some(name) = callable_name(node, source)
        {
            definitions.entry(name).or_default().push(node);
        }
    });

    let mut functions = Vec::new();
    let mut index = ElementEffectIndex {
        macro_names: HashSet::new(),
        declared_functions,
        intrinsic_header,
        math_header,
        ..ElementEffectIndex::default()
    };
    for (name, nodes) in definitions {
        let [function] = nodes.as_slice() else {
            continue;
        };
        let Some(body) = function.child_by_field_name("body") else {
            continue;
        };
        let header = &source[function.start_byte()..body.start_byte()];
        if !header
            .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
            .any(|word| word == "static")
        {
            continue;
        }
        let Some(parameters) = function
            .child_by_field_name("declarator")
            .and_then(|declarator| declarator.child_by_field_name("parameters"))
        else {
            continue;
        };
        let mut parameter_facts = Vec::new();
        let mut supported = true;
        for parameter in parameters.named_children(&mut parameters.walk()) {
            if parameter.kind() != "parameter_declaration" {
                supported = false;
                break;
            }
            let Some(name_node) = parameter
                .child_by_field_name("declarator")
                .and_then(variable_name)
            else {
                supported = false;
                break;
            };
            let declarator_text = parameter
                .child_by_field_name("declarator")
                .map(|declarator| node_text(declarator, source))
                .unwrap_or("");
            let by_value = !declarator_text.contains(['*', '&', '[', ']']);
            let scalar_reference = parameter
                .child_by_field_name("type")
                .is_some_and(|ty| matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
                && !by_value
                && !declarator_text.contains('[');
            parameter_facts.push(ElementParameter {
                name: node_text(name_node, source).to_owned(),
                declaration: parameter.start_byte(),
                by_value,
                scalar_reference,
            });
        }
        if !supported {
            continue;
        }
        let return_by_value = function
            .child_by_field_name("type")
            .is_none_or(|ty| !node_text(ty, source).contains(['*', '&']));
        let all_by_value = parameter_facts.iter().all(|parameter| parameter.by_value);
        if all_by_value {
            index.value_functions.insert(name.clone());
        }
        functions.push(ElementFunction {
            name,
            start: function.start_byte(),
            body,
            parameters: parameter_facts,
            return_by_value,
        });
    }

    // Seed all unique visible definitions. Value-only functions are safe for
    // scalar copies immediately; pointer/reference effects are induced below.
    for function in &functions {
        index.functions.insert(
            function.name.clone(),
            ElementEffect {
                start: function.start,
                end: function.body.end_byte(),
                undef: usize::MAX,
                safe: function
                    .parameters
                    .iter()
                    .map(|parameter| parameter.by_value)
                    .collect(),
            },
        );
    }
    for _ in 0..8 {
        let mut changed = false;
        for function in &functions {
            let safe = function
                .parameters
                .iter()
                .map(|parameter| {
                    parameter.by_value
                        || (parameter.scalar_reference
                            && element_function_parameter_safe(facts, function, parameter, &index))
                })
                .collect::<Vec<_>>();
            let effect = index.functions.get_mut(&function.name);
            if let Some(effect) = effect
                && effect.safe != safe
            {
                effect.safe = safe;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut macro_definitions: HashMap<String, Vec<Node<'_>>> = HashMap::new();
    let mut undefinitions: HashMap<String, usize> = HashMap::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "preproc_function_def"
            && let Some(name) = node.child_by_field_name("name")
        {
            macro_definitions
                .entry(node_text(name, source).to_owned())
                .or_default()
                .push(node);
        }
        if node.kind() == "preproc_call"
            && let Some(name) = node_text(node, source)
                .trim_start()
                .strip_prefix("#undef")
                .and_then(|rest| rest.split_whitespace().next())
        {
            undefinitions
                .entry(name.to_owned())
                .and_modify(|position| *position = (*position).min(node.start_byte()))
                .or_insert(node.start_byte());
        }
    });
    let macro_names = macro_definitions.keys().cloned().collect::<HashSet<_>>();
    index.macro_names = macro_names.clone();
    for (name, nodes) in macro_definitions {
        let Some(first) = nodes.first() else {
            continue;
        };
        let Some(parameters) = first.child_by_field_name("parameters") else {
            continue;
        };
        let parameter_names = identifier_tokens(node_text(parameters, source))
            .map(str::to_owned)
            .collect::<Vec<_>>();
        if parameter_names.is_empty() || parameter_names.iter().any(|name| name == "...") {
            continue;
        }
        let Some(value) = first.child_by_field_name("value") else {
            continue;
        };
        let normalized = normalize_macro_body(node_text(value, source));
        if nodes.iter().any(|node| {
            node.child_by_field_name("parameters")
                .is_none_or(|parameters| {
                    identifier_tokens(node_text(parameters, source))
                        .map(str::to_owned)
                        .collect::<Vec<_>>()
                        != parameter_names
                })
                || node.child_by_field_name("value").is_none_or(|value| {
                    normalize_macro_body(node_text(value, source)) != normalized
                })
        }) || undefinitions.contains_key(&name)
            || macro_names.iter().any(|other| {
                other != &name && identifier_tokens(&normalized).any(|token| token == other)
            })
        {
            continue;
        }
        let Some(safe) = macro_parameter_effects(&normalized, &parameter_names, &index) else {
            continue;
        };
        let definition_name = first
            .child_by_field_name("name")
            .map(|node| node_text(node, source).to_owned())
            .unwrap_or(name.clone());
        index.macros.insert(
            name,
            ElementEffect {
                start: first.start_byte(),
                end: first.end_byte(),
                undef: undefinitions
                    .get(&definition_name)
                    .copied()
                    .unwrap_or(usize::MAX),
                safe,
            },
        );
    }
    index
}

fn walk_has_intrinsic_header(root: Node<'_>, source: &str) -> bool {
    let mut found = false;
    walk_nodes(root, &mut |node| {
        if node.kind() != "preproc_include" {
            return;
        }
        let text = node_text(node, source).to_ascii_lowercase();
        found |= [
            "intrin",
            "xmmintrin",
            "emmintrin",
            "smmintrin",
            "avxintrin",
            "immintrin",
            "arm_neon",
            "simd",
        ]
        .iter()
        .any(|needle| text.contains(needle));
    });
    found
}

fn walk_has_math_header(root: Node<'_>, source: &str) -> bool {
    let mut found = false;
    walk_nodes(root, &mut |node| {
        if node.kind() != "preproc_include" {
            return;
        }
        let text = node_text(node, source).to_ascii_lowercase();
        found |= text.contains("<math.h>") || text.contains("<cmath>");
    });
    found
}

fn top_level_preprocessed_definition(mut node: Node<'_>) -> bool {
    while let Some(parent) = node.parent() {
        if parent.kind() == "translation_unit" {
            return true;
        }
        if parent.kind().starts_with("preproc_") {
            node = parent;
            continue;
        }
        return false;
    }
    false
}

fn normalize_macro_body(body: &str) -> String {
    body.replace("\\\r\n", " ")
        .replace("\\\n", " ")
        .split_whitespace()
        .collect::<String>()
}

fn identifier_tokens(source: &str) -> impl Iterator<Item = &str> {
    source
        .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
        .filter(|token| !token.is_empty())
}

fn macro_parameter_effects(
    body: &str,
    parameters: &[String],
    index: &ElementEffectIndex,
) -> Option<Vec<bool>> {
    if body.contains('#') || body.contains("##") {
        return None;
    }
    let declarations = parameters
        .iter()
        .map(|name| format!("float {name}"))
        .collect::<Vec<_>>()
        .join(", ");
    let synthetic = format!("void __element_macro({declarations}) {{ {body}; }}");
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_cpp::LANGUAGE.into())
        .ok()?;
    let tree = parser.parse(&synthetic, None)?;
    if tree.root_node().has_error() {
        return None;
    }
    let body_node = tree
        .root_node()
        .named_child(0)?
        .child_by_field_name("body")?;
    Some(
        parameters
            .iter()
            .map(|parameter| {
                let declaration =
                    !walk_has_unsafe_macro_declaration(body_node, parameter, &synthetic);
                let uses = walk_parameter_uses(body_node, parameter, &synthetic, |occurrence| {
                    element_identifier_use_safe(
                        occurrence,
                        &synthetic,
                        true,
                        true,
                        usize::MAX,
                        index,
                    )
                });
                declaration && uses
            })
            .collect(),
    )
}

fn walk_has_unsafe_macro_declaration(node: Node<'_>, name: &str, source: &str) -> bool {
    let mut found = false;
    walk_nodes(node, &mut |child| {
        if child.kind() == "declaration"
            && node_text(child, source)
                .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                .any(|token| token == name)
        {
            found = true;
        }
    });
    found
}

fn walk_parameter_uses(
    node: Node<'_>,
    name: &str,
    source: &str,
    mut predicate: impl FnMut(Node<'_>) -> bool,
) -> bool {
    let mut safe = true;
    walk_nodes(node, &mut |child| {
        if child.kind() == "identifier" && node_text(child, source) == name {
            safe &= predicate(child);
        }
    });
    safe
}

fn element_function_parameter_safe(
    facts: &FileFacts<'_>,
    function: &ElementFunction<'_>,
    parameter: &ElementParameter,
    index: &ElementEffectIndex,
) -> bool {
    facts
        .occurrences
        .get(&parameter.name)
        .into_iter()
        .flatten()
        .filter(|occurrence| {
            function.body.start_byte() < occurrence.start_byte()
                && occurrence.end_byte() < function.body.end_byte()
                && binding(facts, &parameter.name, occurrence.start_byte())
                    .is_some_and(|variable| variable.declaration == parameter.declaration)
        })
        .all(|occurrence| {
            element_identifier_use_safe(
                *occurrence,
                &facts.file.source,
                parameter.scalar_reference,
                function.return_by_value,
                occurrence.start_byte(),
                index,
            )
        })
}

fn element_identifier_use_safe(
    occurrence: Node<'_>,
    source: &str,
    scalar_parameter: bool,
    return_by_value: bool,
    visibility: usize,
    index: &ElementEffectIndex,
) -> bool {
    let mut current = occurrence;
    let mut addressed = false;
    let mut scalarized = scalar_parameter;
    loop {
        let Some(parent) = current.parent() else {
            return false;
        };
        match parent.kind() {
            "parenthesized_expression" => current = parent,
            "pointer_expression"
                if parent.child_by_field_name("argument") == Some(current)
                    && parent
                        .child_by_field_name("operator")
                        .is_some_and(|operator| node_text(operator, source) == "&") =>
            {
                if !scalarized {
                    return false;
                }
                addressed = true;
                current = parent;
            }
            "pointer_expression" => return false,
            "subscript_expression" if parent.child_by_field_name("argument") == Some(current) => {
                if addressed
                    || parent.child_by_field_name("indices").is_none_or(|indices| {
                        indices.named_child_count() != 1
                            || !indices.named_child(0).is_some_and(|index| {
                                super::evidence::primitive_local_operand(index, source)
                            })
                    })
                {
                    return false;
                }
                scalarized = true;
                current = parent;
            }
            "field_expression" if parent.child_by_field_name("argument") == Some(current) => {
                return false;
            }
            "argument_list" => {
                let Some(call) = parent
                    .parent()
                    .filter(|node| node.kind() == "call_expression")
                else {
                    return false;
                };
                let Some(arguments) = call.child_by_field_name("arguments") else {
                    return false;
                };
                let Some(argument_index) = arguments
                    .named_children(&mut arguments.walk())
                    .position(|argument| argument == current)
                else {
                    return false;
                };
                let Some(callee) = call.child_by_field_name("function") else {
                    return false;
                };
                return element_call_argument_safe(
                    index,
                    node_text(callee, source),
                    argument_index,
                    addressed,
                    visibility,
                );
            }
            "call_expression" if parent.child_by_field_name("function") == Some(current) => {
                return false;
            }
            "cast_expression" => {
                if addressed
                    || parent
                        .child_by_field_name("type")
                        .is_some_and(|ty| node_text(ty, source).contains(['*', '&']))
                {
                    return false;
                }
                current = parent;
            }
            "binary_expression" => {
                if addressed
                    && parent
                        .child_by_field_name("operator")
                        .is_none_or(|operator| !matches!(node_text(operator, source), "+" | "-"))
                {
                    return false;
                }
                current = parent;
            }
            "unary_expression"
            | "conditional_expression"
            | "assignment_expression"
            | "update_expression" => {
                if addressed {
                    return false;
                }
                if parent.kind() == "assignment_expression"
                    && parent.child_by_field_name("left") == Some(current)
                    && !scalarized
                {
                    return false;
                }
                current = parent;
            }
            "init_declarator" => {
                if addressed
                    || parent
                        .child_by_field_name("declarator")
                        .is_some_and(|declarator| {
                            node_text(declarator, source).contains(['*', '&', '['])
                        })
                {
                    return false;
                }
                current = parent;
            }
            "return_statement" => return return_by_value && !addressed,
            "lambda_expression" | "ERROR" => return false,
            "expression_statement"
            | "condition_clause"
            | "if_statement"
            | "while_statement"
            | "for_statement"
            | "do_statement"
            | "compound_statement" => return !addressed,
            _ => {
                if addressed {
                    return false;
                }
                current = parent;
            }
        }
    }
}

fn element_call_argument_safe(
    index: &ElementEffectIndex,
    callee: &str,
    argument: usize,
    addressed: bool,
    visibility: usize,
) -> bool {
    let callee = short_name(callee);
    if let Some(effect) = index.functions.get(callee)
        && (visibility == usize::MAX || effect.start <= visibility)
        && effect.safe.get(argument).copied().unwrap_or(false)
    {
        return true;
    }
    if let Some(effect) = index.macros.get(callee)
        && effect.end <= visibility
        && visibility < effect.undef
        && effect.safe.get(argument).copied().unwrap_or(false)
    {
        return true;
    }
    !addressed
        && index.value_functions.contains(callee)
        && index
            .functions
            .get(callee)
            .is_some_and(|effect| visibility == usize::MAX || effect.start <= visibility)
        || index.intrinsic_header
            && is_compiler_intrinsic(callee)
            && !index.functions.contains_key(callee)
            && !index.macro_names.contains(callee)
        || !addressed
            && index.math_header
            && is_standard_math_value(callee)
            && !index.declared_functions.contains(callee)
            && !index.macro_names.contains(callee)
}

fn element_call_consumes(facts: &FileFacts<'_>, arguments: Node<'_>, element: Node<'_>) -> bool {
    let Some(call) = arguments
        .parent()
        .filter(|node| node.kind() == "call_expression")
    else {
        return false;
    };
    let Some(argument_index) = arguments
        .named_children(&mut arguments.walk())
        .position(|argument| argument == element)
    else {
        return false;
    };
    let Some(callee) = call.child_by_field_name("function") else {
        return false;
    };
    element_call_argument_safe(
        element_effects(facts),
        node_text(callee, &facts.file.source),
        argument_index,
        false,
        call.start_byte(),
    )
}

fn is_compiler_intrinsic(name: &str) -> bool {
    name.starts_with("_mm_")
        || name.starts_with("_mm256_")
        || name.starts_with("_mm512_")
        || name.starts_with("__builtin_")
}

fn is_standard_math_value(name: &str) -> bool {
    matches!(
        name,
        "acos"
            | "acosf"
            | "acosl"
            | "asin"
            | "asinf"
            | "asinl"
            | "atan"
            | "atanf"
            | "atanl"
            | "atan2"
            | "atan2f"
            | "atan2l"
            | "ceil"
            | "ceilf"
            | "ceill"
            | "cos"
            | "cosf"
            | "cosl"
            | "exp"
            | "expf"
            | "expl"
            | "fabs"
            | "fabsf"
            | "fabsl"
            | "floor"
            | "floorf"
            | "floorl"
            | "fmax"
            | "fmaxf"
            | "fmaxl"
            | "fmin"
            | "fminf"
            | "fminl"
            | "fmod"
            | "fmodf"
            | "fmodl"
            | "log"
            | "logf"
            | "logl"
            | "pow"
            | "powf"
            | "powl"
            | "round"
            | "roundf"
            | "roundl"
            | "sqrt"
            | "sqrtf"
            | "sqrtl"
            | "tan"
            | "tanf"
            | "tanl"
            | "trunc"
            | "truncf"
            | "truncl"
    )
}

// Restrict argument recovery to native pointer expressions; arbitrary calls
// and overloaded conversions are not an alias or non-retention proof.
fn memory_argument_base<'tree>(
    facts: &FileFacts<'tree>,
    mut value: Node<'tree>,
    allocators: &Allocators,
) -> Option<Node<'tree>> {
    let source = &facts.file.source;
    while value.kind() == "parenthesized_expression" {
        value = value.named_child(0)?;
    }
    if value.kind() == "pointer_expression"
        && value
            .child_by_field_name("operator")
            .is_some_and(|op| node_text(op, source) == "&")
    {
        value = value.child_by_field_name("argument")?;
        if value.kind() != "subscript_expression" {
            return None;
        }
        while value.kind() == "subscript_expression" {
            let indices = value.child_by_field_name("indices")?;
            if indices.named_child_count() != 1 {
                return None;
            }
            let index = indices.named_child(0)?;
            if !super::evidence::primitive_local_operand(index, source) {
                return None;
            }
            value = value.child_by_field_name("argument")?;
        }
    }
    proven_allocation_alias_base(facts, value, allocators)
}

pub fn collect_initialization_facts(
    files: &[ParsedCppFile],
) -> HashMap<String, Vec<FreshInitializationRange>> {
    collect_initialization_facts_with_commands(files, &[])
}

pub(super) fn collect_initialization_facts_with_commands(
    files: &[ParsedCppFile],
    commands: &[super::types::CppCompileCommand],
) -> HashMap<String, Vec<FreshInitializationRange>> {
    let facts = files.iter().map(prepare_file).collect::<Vec<_>>();
    let allocators = allocator_summaries(&facts, commands);
    let automatic_records = automatic_record_summaries(&facts);
    facts
        .iter()
        .map(|facts| {
            let mut ranges = fresh_ranges(facts, &allocators);
            ranges.extend(automatic_ranges(facts, &allocators, &automatic_records));
            (facts.file.path.clone(), ranges)
        })
        .collect()
}

/// Exact indexed uses of a fresh allocation before any possible handoff.
/// Keep allocation/use offsets so the caller can reject a parallel construct
/// entered after allocation (OpenMP captures are not C++ lambda captures).
pub fn collect_fresh_indexed_accesses(
    files: &[ParsedCppFile],
) -> HashMap<String, Vec<(String, usize, usize, usize)>> {
    collect_fresh_indexed_accesses_with_commands(files, &[])
}

pub(super) fn collect_fresh_indexed_accesses_with_commands(
    files: &[ParsedCppFile],
    commands: &[super::types::CppCompileCommand],
) -> HashMap<String, Vec<(String, usize, usize, usize)>> {
    let facts = files.iter().map(prepare_file).collect::<Vec<_>>();
    let allocators = allocator_summaries(&facts, commands);
    facts
        .iter()
        .map(|facts| {
            let ranges = fresh_ranges(facts, &allocators);
            let mut accesses = Vec::new();
            for range in &ranges {
                for usage in facts.occurrences.get(&range.receiver).into_iter().flatten() {
                    if !usage.parent().is_some_and(|parent| {
                        parent.kind() == "subscript_expression"
                            && parent.child_by_field_name("argument") == Some(*usage)
                    }) {
                        continue;
                    }
                    let Some(variable) = binding(facts, &range.receiver, usage.start_byte()) else {
                        continue;
                    };
                    if range.contains(&range.receiver, variable.declaration, usage.start_byte()) {
                        accesses.push((
                            range.receiver.clone(),
                            usage.start_position().row + 1,
                            range.begin,
                            usage.end_byte(),
                        ));
                    }
                }
            }
            // Candidates are line-based: a same-line shadow or second use
            // must not borrow the first binding's ownership proof.
            accesses.retain(|(name, line, _, _)| {
                facts.occurrences[name]
                    .iter()
                    .filter(|usage| {
                        usage.start_position().row + 1 == *line
                            && usage.parent().is_some_and(|parent| {
                                parent.kind() == "subscript_expression"
                                    && parent.child_by_field_name("argument") == Some(**usage)
                            })
                    })
                    .all(|usage| {
                        binding(facts, name, usage.start_byte()).is_some_and(|variable| {
                            ranges.iter().any(|range| {
                                range.contains(name, variable.declaration, usage.start_byte())
                            })
                        })
                    })
            });
            (facts.file.path.clone(), accesses)
        })
        .collect()
}

fn prepare_file(file: &ParsedCppFile) -> FileFacts<'_> {
    let mut facts = FileFacts {
        file,
        variables: HashMap::new(),
        occurrences: HashMap::new(),
        jumping_functions: HashSet::new(),
        syntax_errors: Vec::new(),
        scalar_parameters: std::cell::OnceCell::new(),
        element_effects: std::cell::OnceCell::new(),
    };
    let Some(tree) = &file.tree else { return facts };
    walk_nodes(tree.root_node(), &mut |node| {
        if node.is_error() || node.is_missing() {
            facts.syntax_errors.push(node);
        }
        if matches!(
            node.kind(),
            "goto_statement" | "labeled_statement" | "case_statement"
        ) && let Some(function) = enclosing_function(node)
        {
            facts.jumping_functions.insert(function.start_byte());
        }
        if node.kind() == "call_expression"
            && node.child_by_field_name("function").is_some_and(|callee| {
                matches!(
                    short_name(node_text(callee, &file.source)),
                    "setjmp" | "_setjmp" | "sigsetjmp"
                )
            })
            && let Some(function) = enclosing_function(node)
        {
            facts.jumping_functions.insert(function.start_byte());
        }
        if node.kind() == "identifier" {
            facts
                .occurrences
                .entry(node_text(node, &file.source).to_string())
                .or_default()
                .push(node);
        }
        if !matches!(
            node.kind(),
            "declaration" | "parameter_declaration" | "optional_parameter_declaration"
        ) {
            return;
        }
        let scope = variable_scope(node);
        let local = enclosing_function(node).is_some()
            && node.kind() == "declaration"
            && !node_text(node, &file.source)
                .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                .any(|token| matches!(token, "static" | "thread_local" | "extern"));
        let auto_type = node
            .child_by_field_name("type")
            .is_some_and(|ty| node_text(ty, &file.source) == "auto");
        let mut cursor = node.walk();
        for declarator in node.children_by_field_name("declarator", &mut cursor) {
            let Some(name_node) = variable_name(declarator) else {
                continue;
            };
            let mut pointer = auto_type;
            let mut array = false;
            let mut part = declarator;
            loop {
                pointer |= part.kind() == "pointer_declarator";
                array |= part.kind() == "array_declarator";
                let Some(child) = part.child_by_field_name("declarator") else {
                    break;
                };
                part = child;
            }
            let name = node_text(name_node, &file.source).to_string();
            facts
                .variables
                .entry(name.clone())
                .or_default()
                .push(Variable {
                    name,
                    declaration: node.start_byte(),
                    begin: if node.kind().contains("parameter") {
                        scope.start_byte()
                    } else {
                        declarator.start_byte()
                    },
                    scope,
                    pointer: pointer && !array,
                    local,
                    declaration_node: node,
                    declarator,
                });
        }
    });
    facts
}

fn variable_name(mut node: Node<'_>) -> Option<Node<'_>> {
    loop {
        if matches!(
            node.kind(),
            "identifier" | "type_identifier" | "primitive_type"
        ) {
            return Some(node);
        }
        if node.kind() == "function_declarator" {
            let child = node.child_by_field_name("declarator")?;
            if matches!(child.kind(), "identifier" | "qualified_identifier") {
                return None;
            }
            node = child;
        } else if matches!(
            node.kind(),
            "parenthesized_declarator" | "reference_declarator"
        ) {
            node = node.named_child(0)?;
        } else {
            node = node.child_by_field_name("declarator")?;
        }
    }
}

fn variable_scope(mut node: Node<'_>) -> Node<'_> {
    let parameter = node.kind().contains("parameter");
    while let Some(parent) = node.parent() {
        node = parent;
        if matches!(
            node.kind(),
            "function_definition" | "lambda_expression" | "translation_unit"
        ) || (!parameter
            && matches!(
                node.kind(),
                "compound_statement" | "for_statement" | "for_range_loop" | "if_statement"
            ))
        {
            break;
        }
    }
    node
}

fn enclosing_function(mut node: Node<'_>) -> Option<Node<'_>> {
    while let Some(parent) = node.parent() {
        if matches!(parent.kind(), "function_definition" | "lambda_expression") {
            return Some(parent);
        }
        node = parent;
    }
    None
}

fn binding<'a>(facts: &'a FileFacts<'_>, name: &str, offset: usize) -> Option<&'a Variable<'a>> {
    facts
        .variables
        .get(name)?
        .iter()
        .filter(|variable| variable.begin <= offset && offset < variable.scope.end_byte())
        .max_by_key(|variable| variable.begin)
}

fn callable_name(mut node: Node<'_>, source: &str) -> Option<String> {
    while node.kind() != "function_declarator" {
        node = node.child_by_field_name("declarator")?;
    }
    let name = node.child_by_field_name("declarator")?;
    matches!(name.kind(), "identifier" | "qualified_identifier")
        .then(|| short_name(node_text(name, source)).to_string())
}

fn short_name(name: &str) -> &str {
    name.trim().rsplit("::").next().unwrap_or(name)
}

fn callable_scope(mut node: Node<'_>, source: &str) -> String {
    let mut scopes = Vec::new();
    let mut declarator = node.child_by_field_name("declarator");
    while declarator.is_some_and(|part| part.kind() != "function_declarator") {
        declarator = declarator.and_then(|part| part.child_by_field_name("declarator"));
    }
    if let Some(name) = declarator.and_then(|part| part.child_by_field_name("declarator"))
        && let Some((scope, _)) = node_text(name, source).rsplit_once("::")
    {
        scopes.push(scope.to_string());
    }
    while let Some(parent) = node.parent() {
        if matches!(
            parent.kind(),
            "namespace_definition" | "class_specifier" | "struct_specifier"
        ) {
            scopes.push(
                parent
                    .child_by_field_name("name")
                    .map(|name| node_text(name, source).to_string())
                    .unwrap_or_else(|| format!("anonymous:{}", parent.start_byte())),
            );
        }
        node = parent;
    }
    scopes.reverse();
    scopes.join("::")
}

fn canonical_header_guard<'a>(node: Node<'_>, source: &'a str) -> Option<(&'a str, usize)> {
    if node.kind() != "preproc_ifdef"
        || node.child(0)?.kind() != "#ifndef"
        || node.child_by_field_name("alternative").is_some()
    {
        return None;
    }
    let root = node
        .parent()
        .filter(|parent| parent.kind() == "translation_unit")?;
    if root.named_children(&mut root.walk()).any(|sibling| {
        sibling != node
            && sibling.kind() != "comment"
            && !(sibling.kind() == "preproc_call"
                && node_text(sibling, source).trim() == "#pragma once")
    }) {
        return None;
    }
    let name = node.child_by_field_name("name")?;
    let definition = node
        .named_children(&mut node.walk())
        .find(|child| *child != name && child.kind() != "comment")?;
    if definition.kind() != "preproc_def"
        || node_text(definition.child_by_field_name("name")?, source) != node_text(name, source)
        || definition
            .child_by_field_name("value")
            .is_some_and(|value| !matches!(node_text(value, source).trim(), "" | "1"))
    {
        return None;
    }
    Some((node_text(name, source), definition.start_byte()))
}

pub(super) fn unconditionally_preprocessed(mut node: Node<'_>, source: &str) -> bool {
    while let Some(parent) = node.parent() {
        if matches!(
            parent.kind(),
            "preproc_if" | "preproc_ifdef" | "preproc_elif" | "preproc_else"
        ) && canonical_header_guard(parent, source).is_none()
        {
            return false;
        }
        node = parent;
    }
    true
}

fn normalized_path(path: &Path) -> String {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => match normalized.components().next_back() {
                Some(Component::Normal(_)) => {
                    normalized.pop();
                }
                Some(Component::RootDir | Component::Prefix(_)) => {}
                _ => normalized.push(".."),
            },
            other => normalized.push(other.as_os_str()),
        }
    }
    normalized.to_string_lossy().into_owned()
}

fn macro_include_edges(facts: &[FileFacts<'_>]) -> Vec<(usize, usize, usize)> {
    let guards = facts
        .iter()
        .enumerate()
        .filter_map(|(index, facts)| {
            let root = facts.file.tree.as_ref()?.root_node();
            root.named_children(&mut root.walk()).find_map(|node| {
                canonical_header_guard(node, &facts.file.source)
                    .map(|(name, offset)| (index, (name, offset)))
            })
        })
        .collect::<HashMap<_, _>>();
    let mut guard_names = HashSet::new();
    let mut changed_guards = HashSet::new();
    for (name, _) in guards.values() {
        if !guard_names.insert(*name) {
            changed_guards.insert(*name);
        }
    }
    for (index, facts) in facts.iter().enumerate() {
        let Some(tree) = &facts.file.tree else {
            continue;
        };
        walk_nodes(tree.root_node(), &mut |node| {
            if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                && let Some(name) = node
                    .child_by_field_name("name")
                    .map(|name| node_text(name, &facts.file.source))
                && guard_names.contains(name)
                && guards
                    .get(&index)
                    .is_none_or(|(guard, offset)| *guard != name || *offset != node.start_byte())
            {
                changed_guards.insert(name);
            }
            if node.kind() == "preproc_call"
                && let Some(directive) = node_text(node, &facts.file.source)
                    .trim_start()
                    .strip_prefix('#')
            {
                let mut words = directive.split_whitespace();
                if words.next() == Some("undef")
                    && let Some(name) = words.next()
                    && guard_names.contains(name)
                {
                    changed_guards.insert(name);
                }
            }
        });
    }
    let paths = facts.iter().enumerate().fold(
        HashMap::<String, Vec<usize>>::new(),
        |mut paths, (index, facts)| {
            paths
                .entry(normalized_path(Path::new(&facts.file.path)))
                .or_default()
                .push(index);
            paths
        },
    );
    let mut includes = vec![Vec::<(usize, usize)>::new(); facts.len()];
    for (index, facts) in facts.iter().enumerate() {
        let Some(tree) = &facts.file.tree else {
            continue;
        };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "preproc_include"
                || !unconditionally_preprocessed(node, &facts.file.source)
            {
                return;
            }
            let Some(path) = node.child_by_field_name("path") else {
                return;
            };
            let spelling = node_text(path, &facts.file.source);
            // Without build include paths, only a quoted path resolving
            // relative to the including file is a positive include witness.
            let Some(relative) = spelling
                .strip_prefix('"')
                .and_then(|path| path.strip_suffix('"'))
            else {
                return;
            };
            let resolved = normalized_path(
                &Path::new(&facts.file.path)
                    .parent()
                    .unwrap_or(Path::new(""))
                    .join(relative),
            );
            let Some(targets) = paths.get(&resolved).filter(|targets| targets.len() == 1) else {
                return;
            };
            if guards
                .get(&targets[0])
                .is_some_and(|(name, _)| changed_guards.contains(name))
            {
                return;
            }
            includes[index].push((targets[0], node.end_byte()));
        });
    }
    includes
        .iter()
        .enumerate()
        .flat_map(|(source, targets)| {
            targets
                .iter()
                .map(move |(target, offset)| (source, *target, *offset))
        })
        .filter(|(source, target, _)| !include_reaches(&includes, *target, *source))
        .collect()
}

fn macro_visibility(
    facts: &[FileFacts<'_>],
    variants: &[AllocationMacro],
    edges: &[(usize, usize, usize)],
) -> HashMap<String, usize> {
    let mut visible = variants
        .iter()
        .filter(|definition| definition.unconditional)
        .fold(HashMap::<usize, usize>::new(), |mut visible, definition| {
            visible
                .entry(definition.file)
                .and_modify(|offset| *offset = (*offset).min(definition.end))
                .or_insert(definition.end);
            visible
        });
    for _ in 0..facts.len() {
        let mut changed = false;
        for (source, target, offset) in edges {
            if visible.contains_key(target)
                && visible
                    .get(source)
                    .is_none_or(|existing| *offset < *existing)
            {
                visible.insert(*source, *offset);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    visible
        .into_iter()
        .map(|(file, offset)| (facts[file].file.path.clone(), offset))
        .collect()
}

fn include_reaches(includes: &[Vec<(usize, usize)>], start: usize, target: usize) -> bool {
    let mut pending = vec![start];
    let mut visited = HashSet::new();
    while let Some(node) = pending.pop() {
        if node == target {
            return true;
        }
        if !visited.insert(node) {
            continue;
        }
        // Excessive or cyclic include recovery is not an availability proof.
        if visited.len() > 100_000 {
            return true;
        }
        pending.extend(includes[node].iter().map(|(next, _)| *next));
    }
    false
}

fn allocator_summaries(
    facts: &[FileFacts<'_>],
    commands: &[super::types::CppCompileCommand],
) -> Allocators {
    let mut definitions: HashMap<String, Vec<(usize, Node<'_>)>> = HashMap::new();
    let mut macros: HashMap<String, Vec<AllocationMacro>> = HashMap::new();
    let mut signatures: HashMap<String, HashSet<String>> = HashMap::new();
    let mut scopes: HashMap<String, HashSet<String>> = HashMap::new();
    let (build_names, opaque_build) = allocator_attributes::build_overrides(commands);
    let mut blocked_names = build_names.clone();
    for (file_index, facts) in facts.iter().enumerate() {
        let Some(tree) = &facts.file.tree else {
            continue;
        };
        for line in facts.file.source.lines() {
            if let Some(undef) = line.trim_start().strip_prefix("#undef")
                && let Some(name) = undef.split_whitespace().next()
            {
                blocked_names.insert(name.to_string());
            }
        }
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() == "function_definition"
                && let Some(name) = callable_name(node, &facts.file.source)
            {
                definitions
                    .entry(name)
                    .or_default()
                    .push((file_index, node));
            }
            if node.kind() == "function_declarator"
                && let Some(name) = callable_name(node, &facts.file.source)
            {
                scopes
                    .entry(name.clone())
                    .or_default()
                    .insert(callable_scope(node, &facts.file.source));
                let mut parameter_shapes = Vec::new();
                if let Some(parameters) = node.child_by_field_name("parameters") {
                    let mut cursor = parameters.walk();
                    for parameter in parameters.named_children(&mut cursor) {
                        let ty = parameter
                            .child_by_field_name("type")
                            .map(|ty| node_text(ty, &facts.file.source))
                            .unwrap_or("");
                        let mut shape = ty.to_string();
                        if let Some(declarator) = parameter.child_by_field_name("declarator") {
                            walk_nodes(declarator, &mut |part| {
                                if matches!(
                                    part.kind(),
                                    "pointer_declarator"
                                        | "reference_declarator"
                                        | "array_declarator"
                                ) {
                                    shape.push_str(part.kind());
                                }
                            });
                        }
                        parameter_shapes.push(shape);
                    }
                }
                signatures
                    .entry(name)
                    .or_default()
                    .insert(parameter_shapes.join(","));
            }
            if node.kind() == "preproc_def"
                && let Some(name) = node.child_by_field_name("name")
            {
                blocked_names.insert(node_text(name, &facts.file.source).to_string());
            }
            if node.kind() == "preproc_function_def"
                && let (Some(name), Some(value)) = (
                    node.child_by_field_name("name"),
                    node.child_by_field_name("value"),
                )
            {
                let parameters = node
                    .child_by_field_name("parameters")
                    .map(|parameters| {
                        node_text(parameters, &facts.file.source)
                            .split(|ch: char| !ch.is_alphanumeric() && ch != '_')
                            .filter(|token| !token.is_empty())
                            .map(str::to_string)
                            .collect()
                    })
                    .unwrap_or_default();
                macros
                    .entry(node_text(name, &facts.file.source).to_string())
                    .or_default()
                    .push(AllocationMacro {
                        body: node_text(value, &facts.file.source).to_string(),
                        parameters,
                        file: file_index,
                        end: node.end_byte(),
                        unconditional: unconditionally_preprocessed(node, &facts.file.source),
                    });
            }
        });
    }
    let overridden = |name: &&str| {
        definitions.contains_key(*name)
            || macros.contains_key(*name)
            || blocked_names.contains(*name)
            || scopes.get(*name).is_some_and(|scopes| {
                scopes
                    .iter()
                    .any(|scope| !matches!(scope.as_str(), "" | "std"))
            })
    };
    let mut allocators = Allocators {
        fresh: ["malloc", "calloc", "aligned_alloc"]
            .into_iter()
            .filter(|name| !overridden(name))
            .map(str::to_string)
            .collect(),
        synchronous_memory: ["memset", "memcpy", "memmove"]
            .into_iter()
            .filter(|name| !overridden(name))
            .map(str::to_string)
            .collect(),
        availability: macros
            .keys()
            .map(|name| (name.clone(), HashMap::new()))
            .collect(),
    };
    for (name, variants) in &definitions {
        let static_variants = variants
            .iter()
            .filter(|(file, function)| {
                let body = function
                    .child_by_field_name("body")
                    .map_or(function.end_byte(), |body| body.start_byte());
                facts[*file].file.source[function.start_byte()..body]
                    .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                    .any(|token| token == "static")
            })
            .collect::<Vec<_>>();
        if !static_variants.is_empty() {
            if static_variants.len() != variants.len() {
                blocked_names.insert(name.clone());
            }
            allocators.availability.insert(
                name.clone(),
                static_variants
                    .into_iter()
                    .map(|(file, _)| (facts[*file].file.path.clone(), 0))
                    .collect(),
            );
        }
    }
    let include_edges = macro_include_edges(facts);
    for (name, availability) in
        allocator_attributes::collect(facts, &include_edges, &build_names, opaque_build)
    {
        // A source annotation adds a contract; it must not narrow an existing
        // builtin allocation contract to the annotation's include scope.
        if !allocators.fresh.contains(&name)
            && !blocked_names.contains(&name)
            && !macros.contains_key(&name)
            && signatures.get(&name).is_none_or(|shapes| shapes.len() <= 1)
            && !scopes.get(&name).is_some_and(|scopes| {
                scopes.len() > 1 || scopes.iter().any(|scope| !scope.is_empty())
            })
        {
            allocators.availability.insert(name.clone(), availability);
            allocators.fresh.insert(name);
        }
    }
    // Monotonic source summaries. Unresolved recursion and excessive wrapper
    // depth remain unknown; they cannot justify an initialization exclusion.
    for _ in 0..8 {
        let mut discovered = Vec::new();
        for (name, variants) in &macros {
            if !allocators.fresh.contains(name)
                && !blocked_names.contains(name)
                && !definitions.contains_key(name)
                && !signatures.contains_key(name)
                && variants
                    .iter()
                    .all(|definition| fresh_macro(definition, facts, &allocators))
            {
                allocators.availability.insert(
                    name.clone(),
                    macro_visibility(facts, variants, &include_edges),
                );
                discovered.push(name.clone());
            }
        }
        for (name, variants) in &definitions {
            if allocators.fresh.contains(name)
                || blocked_names.contains(name)
                || macros.contains_key(name)
                || signatures.get(name).is_some_and(|shapes| shapes.len() > 1)
                || scopes.get(name).is_some_and(|scopes| {
                    scopes.len() > 1 || scopes.iter().any(|scope| !scope.is_empty())
                })
            {
                continue;
            }
            if variants.iter().all(|(file_index, function)| {
                fresh_returning_function(*function, &facts[*file_index], &allocators)
            }) {
                discovered.push(name.clone());
            }
        }
        if discovered.is_empty() {
            break;
        }
        allocators.fresh.extend(discovered);
    }
    allocators
}

fn fresh_macro(
    definition: &AllocationMacro,
    facts: &[FileFacts<'_>],
    allocators: &Allocators,
) -> bool {
    let body = &definition.body;
    let parameters = &definition.parameters;
    if !mentions_known_allocator(body, allocators) {
        return false;
    }
    let source = format!("void __allocation_summary() {{ return {body}; }}");
    let mut parser = Parser::new();
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
        .and_then(|function| function.child_by_field_name("body"))
    else {
        return false;
    };
    if body.named_child_count() != 1 {
        return false;
    }
    let Some(statement) = body
        .named_child(0)
        .filter(|statement| statement.kind() == "return_statement")
    else {
        return false;
    };
    statement.named_child(0).is_some_and(|value| {
        fresh_expression(value, &source, allocators, &|name| {
            parameters.contains(name)
                || !allocators.available(name, &facts[definition.file].file.path, definition.end)
        })
    })
}

fn mentions_known_allocator(source: &str, allocators: &Allocators) -> bool {
    source
        .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
        .any(|token| allocators.fresh.contains(token))
}

fn unwrap_cast<'a>(mut node: Node<'a>, source: &str) -> Node<'a> {
    loop {
        match node.kind() {
            "parenthesized_expression" => {
                if let Some(child) = node.named_child(0) {
                    node = child;
                } else {
                    return node;
                }
            }
            "cast_expression" => {
                if let Some(child) = node.child_by_field_name("value") {
                    node = child;
                } else {
                    return node;
                }
            }
            "call_expression" => {
                let cast = node.child_by_field_name("function").is_some_and(|callee| {
                    let text = node_text(callee, source);
                    text.starts_with("static_cast<")
                        || text.starts_with("reinterpret_cast<")
                        || text.starts_with("const_cast<")
                });
                if cast
                    && let Some(argument) = node
                        .child_by_field_name("arguments")
                        .and_then(|arguments| arguments.named_child(0))
                {
                    node = argument;
                } else {
                    return node;
                }
            }
            _ => return node,
        }
    }
}

fn fresh_expression(
    node: Node<'_>,
    source: &str,
    allocators: &Allocators,
    shadowed: &dyn Fn(&str) -> bool,
) -> bool {
    let node = unwrap_cast(node, source);
    if node.kind() != "call_expression" {
        return false;
    }
    let Some(callee) = node.child_by_field_name("function") else {
        return false;
    };
    if !matches!(callee.kind(), "identifier" | "qualified_identifier") {
        return false;
    }
    let text = node_text(callee, source);
    if text.contains("::") && !text.starts_with("std::") && !text.starts_with("::") {
        return false;
    }
    let name = short_name(text);
    allocators.fresh.contains(name) && !shadowed(name)
}

struct AutomaticRecord {
    qualified: String,
    scope: String,
    file: String,
    definition: usize,
    local_scope: Option<(usize, usize)>,
    safe: bool,
}

#[derive(Default)]
struct AutomaticRecords {
    definitions: HashMap<String, Vec<AutomaticRecord>>,
    aliased_names: HashSet<String>,
    /// Reverse macro dependencies excluding formal parameters: a replacement
    /// can capture a local without an explicit argument at the invocation.
    macro_users: HashMap<String, HashSet<String>>,
}

fn automatic_record_summaries(facts: &[FileFacts<'_>]) -> AutomaticRecords {
    let mut records = AutomaticRecords::default();
    let mut scalar_aliases: HashMap<String, Option<HashSet<String>>> = HashMap::new();
    let mut macro_names = HashSet::new();
    // A syntactic spelling is not a type proof when a typedef/using/macro can
    // redirect it. Collect all blockers before inspecting any record, including
    // declarations that occur later or in another source file.
    for facts in facts {
        let Some(tree) = &facts.file.tree else {
            continue;
        };
        walk_nodes(tree.root_node(), &mut |node| {
            if matches!(node.kind(), "class_specifier" | "struct_specifier")
                && let Some(name) = node.child_by_field_name("name")
                && standard_scalar_alias(node_text(name, &facts.file.source))
            {
                let name = node_text(name, &facts.file.source).to_string();
                records.aliased_names.insert(name.clone());
                scalar_aliases.insert(name, None);
            }
            if matches!(
                node.kind(),
                "alias_declaration" | "type_definition" | "preproc_def" | "preproc_function_def"
            ) && let Some(name) = node.child_by_field_name("name").or_else(|| {
                node.child_by_field_name("declarator")
                    .and_then(variable_name)
            }) {
                let alias = short_name(node_text(name, &facts.file.source)).to_string();
                if matches!(node.kind(), "alias_declaration" | "type_definition") {
                    let plain = node.kind() == "alias_declaration"
                        || node.child_by_field_name("declarator") == Some(name);
                    let builtin = node
                        .child_by_field_name("type")
                        .filter(|ty| {
                            plain
                                && node_text(*ty, &facts.file.source).chars().all(|ch| {
                                    ch.is_ascii_alphanumeric() || ch == '_' || ch.is_whitespace()
                                })
                        })
                        .map(|ty| identifier_set(node_text(ty, &facts.file.source)))
                        .filter(|tokens| {
                            !tokens.is_empty()
                                && tokens.iter().all(|token| builtin_scalar_word(token))
                        });
                    scalar_aliases
                        .entry(alias.clone())
                        .and_modify(|existing| {
                            if let (Some(existing), Some(additional)) = (&mut *existing, &builtin) {
                                existing.extend(additional.iter().cloned());
                            } else {
                                *existing = None;
                            }
                        })
                        .or_insert(builtin);
                } else {
                    macro_names.insert(alias);
                }
                if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                    && let Some(value) = node.child_by_field_name("value")
                {
                    let parameters = node
                        .child_by_field_name("parameters")
                        .map(|parameters| identifier_set(node_text(parameters, &facts.file.source)))
                        .unwrap_or_default();
                    for captured in
                        identifier_set(node_text(value, &facts.file.source)).difference(&parameters)
                    {
                        records
                            .macro_users
                            .entry(captured.to_string())
                            .or_default()
                            .insert(node_text(name, &facts.file.source).to_string());
                    }
                }
                records
                    .aliased_names
                    .insert(short_name(node_text(name, &facts.file.source)).to_string());
            }
        });
    }
    for (alias, underlying) in scalar_aliases {
        if !macro_names.contains(&alias)
            && underlying.is_some_and(|tokens| tokens.is_disjoint(&macro_names))
        {
            // Every source definition resolves directly to fundamental scalar
            // tokens; vendor stdint typedefs do not introduce a constructor.
            records.aliased_names.remove(&alias);
        }
    }
    for facts in facts {
        let Some(tree) = &facts.file.tree else {
            continue;
        };
        walk_nodes(tree.root_node(), &mut |node| {
            let source = &facts.file.source;
            if !matches!(node.kind(), "class_specifier" | "struct_specifier")
                || node.child_by_field_name("body").is_none()
            {
                return;
            }
            let Some(name) = node.child_by_field_name("name") else {
                return;
            };
            let name = node_text(name, source);
            if name.contains('<') || name.contains("::") {
                return;
            }
            let scope = callable_scope(node, source);
            let qualified = if scope.is_empty() {
                name.to_string()
            } else {
                format!("{scope}::{name}")
            };
            records
                .definitions
                .entry(name.to_string())
                .or_default()
                .push(AutomaticRecord {
                    qualified,
                    scope,
                    file: facts.file.path.clone(),
                    definition: node.start_byte(),
                    local_scope: enclosing_function(node)
                        .map(|function| (function.start_byte(), function.end_byte())),
                    safe: automatic_record_is_safe(
                        node,
                        source,
                        name,
                        &records.aliased_names,
                        &macro_names,
                    ),
                });
        });
    }
    records
}

fn identifier_set(source: &str) -> HashSet<String> {
    source
        .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
        .filter(|token| !token.is_empty())
        .map(str::to_string)
        .collect()
}

fn builtin_scalar_word(word: &str) -> bool {
    matches!(
        word,
        "bool"
            | "char"
            | "char8_t"
            | "char16_t"
            | "char32_t"
            | "wchar_t"
            | "signed"
            | "unsigned"
            | "short"
            | "int"
            | "long"
            | "float"
            | "double"
            | "__int8"
            | "__int16"
            | "__int32"
            | "__int64"
            | "__int128"
    )
}

fn scalar_type(
    node: Node<'_>,
    source: &str,
    enums: &HashSet<String>,
    aliased_names: &HashSet<String>,
) -> bool {
    if node_text(node, source)
        .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
        .any(|token| aliased_names.contains(token))
    {
        return false;
    }
    if matches!(
        node.kind(),
        "primitive_type" | "sized_type_specifier" | "enum_specifier"
    ) {
        return node_text(node, source) != "void";
    }
    let text = node_text(node, source);
    let name = text.strip_prefix("std::").unwrap_or(text);
    enums.contains(text) || standard_scalar_alias(name)
}

fn standard_scalar_alias(name: &str) -> bool {
    matches!(
        name,
        "int8_t"
            | "int16_t"
            | "int32_t"
            | "int64_t"
            | "uint8_t"
            | "uint16_t"
            | "uint32_t"
            | "uint64_t"
            | "intptr_t"
            | "uintptr_t"
            | "size_t"
            | "ptrdiff_t"
    )
}

fn literal_initializer(node: Node<'_>, source: &str) -> bool {
    match node.kind() {
        "number_literal" | "char_literal" | "true" | "false" | "null" => true,
        "argument_list" | "initializer_list" | "parenthesized_expression" => {
            let mut cursor = node.walk();
            node.named_children(&mut cursor)
                .all(|child| literal_initializer(child, source))
        }
        "unary_expression" => {
            node.child_by_field_name("operator")
                .is_some_and(|op| matches!(node_text(op, source), "+" | "-" | "!" | "~"))
                && node
                    .child_by_field_name("argument")
                    .is_some_and(|value| literal_initializer(value, source))
        }
        _ => false,
    }
}

/// This deliberately does not infer triviality from a class name or absence of
/// thread calls. Only builtin scalar/pointer fields and complete zero-argument
/// constructors with empty bodies and literal own-field initializers qualify.
fn automatic_record_is_safe(
    record: Node<'_>,
    source: &str,
    name: &str,
    aliased_names: &HashSet<String>,
    macro_names: &HashSet<String>,
) -> bool {
    if record.has_error() {
        return false;
    }
    let Some(body) = record.child_by_field_name("body") else {
        return false;
    };
    let mut cursor = record.walk();
    if record
        .named_children(&mut cursor)
        .any(|child| child.kind() == "base_class_clause")
    {
        return false;
    }
    let mut enums = HashSet::new();
    let mut fields = HashSet::new();
    let mut constructors = Vec::new();
    let mut cursor = body.walk();
    let members = body.named_children(&mut cursor).collect::<Vec<_>>();
    for member in &members {
        if member.kind() == "field_declaration"
            && let Some(ty) = member.child_by_field_name("type")
            && ty.kind() == "enum_specifier"
            && let Some(enum_name) = ty.child_by_field_name("name")
        {
            enums.insert(node_text(enum_name, source).to_string());
        }
    }
    for member in members {
        match member.kind() {
            "comment" | "access_specifier" => {}
            "function_definition" => {
                if node_text(member, source)
                    .split_whitespace()
                    .any(|word| word == "virtual")
                {
                    return false;
                }
                if member.child_by_field_name("type").is_none() {
                    if member
                        .child_by_field_name("declarator")
                        .and_then(|declarator| callable_name(declarator, source))
                        .as_deref()
                        != Some(name)
                    {
                        // Destructors/conversion operators and unresolved callable
                        // declarations need a separate lifetime/effect summary.
                        return false;
                    }
                    constructors.push(member);
                }
            }
            "field_declaration" => {
                if member.child_by_field_name("default_value").is_some() {
                    return false;
                }
                let Some(ty) = member.child_by_field_name("type") else {
                    return false;
                };
                let mut cursor = member.walk();
                for declarator in member.children_by_field_name("declarator", &mut cursor) {
                    if declarator.kind() == "function_declarator" {
                        // Ordinary method declarations do not run at construction.
                        if node_text(member, source)
                            .split_whitespace()
                            .any(|word| word == "virtual")
                        {
                            return false;
                        }
                        continue;
                    }
                    let mut declarator = declarator;
                    let mut pointer = false;
                    while declarator.kind() == "pointer_declarator" {
                        pointer = true;
                        let Some(inner) = declarator.child_by_field_name("declarator") else {
                            return false;
                        };
                        declarator = inner;
                    }
                    if declarator.kind() != "field_identifier"
                        || (!pointer && !scalar_type(ty, source, &enums, aliased_names))
                        || (pointer
                            && identifier_set(node_text(ty, source))
                                .iter()
                                .any(|name| macro_names.contains(name)))
                        || macro_names.contains(node_text(declarator, source))
                    {
                        return false;
                    }
                    fields.insert(node_text(declarator, source).to_string());
                }
            }
            // Templates, conditional member definitions, nested unknown types,
            // defaulted/delegating declarations, and recovery are not proof.
            _ => return false,
        }
    }
    for constructor in constructors {
        let Some(body) = constructor.child_by_field_name("body") else {
            return false;
        };
        let mut cursor = body.walk();
        if body
            .named_children(&mut cursor)
            .any(|child| child.kind() != "comment")
        {
            return false;
        }
        let Some(parameters) = constructor
            .child_by_field_name("declarator")
            .and_then(|declarator| declarator.child_by_field_name("parameters"))
        else {
            return false;
        };
        if parameters.named_child_count() != 0 {
            return false;
        }
        let mut cursor = constructor.walk();
        for list in constructor
            .named_children(&mut cursor)
            .filter(|child| child.kind() == "field_initializer_list")
        {
            let mut cursor = list.walk();
            for initializer in list.named_children(&mut cursor) {
                let Some(field) = initializer.named_child(0) else {
                    return false;
                };
                let Some(value) = initializer.named_child(1) else {
                    return false;
                };
                if !fields.contains(node_text(field, source)) || !literal_initializer(value, source)
                {
                    return false;
                }
            }
        }
    }
    true
}

fn automatic_ranges(
    facts: &FileFacts<'_>,
    allocators: &Allocators,
    records: &AutomaticRecords,
) -> Vec<FreshInitializationRange> {
    let mut ranges = Vec::new();
    for variable in facts.variables.values().flatten() {
        if !variable.local || variable.pointer {
            continue;
        }
        let declaration = variable.declaration_node;
        let Some(block) = declaration
            .parent()
            .filter(|node| node.kind() == "compound_statement" && !node.has_error())
        else {
            continue;
        };
        let Some(function) = enclosing_function(declaration) else {
            continue;
        };
        if facts.jumping_functions.contains(&function.start_byte()) {
            continue;
        }
        let declarator = variable.declarator;
        let plain = declarator.kind() == "identifier"
            || (declarator.kind() == "init_declarator"
                && declarator
                    .child_by_field_name("declarator")
                    .is_some_and(|node| node.kind() == "identifier")
                && declarator.child_by_field_name("value").is_some_and(|node| {
                    node.kind() == "initializer_list" && node.named_child_count() == 0
                }));
        if !plain {
            continue;
        }
        let Some(ty) = declaration.child_by_field_name("type") else {
            continue;
        };
        let type_name = node_text(ty, &facts.file.source).trim_start_matches("::");
        let short = short_name(type_name);
        if records.aliased_names.contains(short) || records.aliased_names.contains(&variable.name) {
            continue;
        }
        let Some(definitions) = records.definitions.get(short) else {
            continue;
        };
        let [record] = definitions.as_slice() else {
            continue;
        };
        let scope = callable_scope(function, &facts.file.source);
        if !record.safe
            || (type_name.contains("::") && type_name != record.qualified)
            || (!type_name.contains("::")
                && !record.scope.is_empty()
                && scope != record.scope
                && !scope.starts_with(&format!("{}::", record.scope)))
            || (record.file == facts.file.path && variable.begin < record.definition)
            || record.local_scope.is_some_and(|(begin, end)| {
                record.file != facts.file.path || variable.begin < begin || end < variable.begin
            })
        {
            continue;
        }
        // A named return value may be constructed directly in a caller-provided
        // result slot (NRVO), which is not proved fresh by this local analysis.
        let returned = facts
            .occurrences
            .get(&variable.name)
            .is_some_and(|occurrences| {
                occurrences.iter().any(|occurrence| {
                    if occurrence.start_byte() < variable.begin
                        || variable.scope.end_byte() <= occurrence.start_byte()
                        || binding(facts, &variable.name, occurrence.start_byte())
                            .is_none_or(|bound| bound.declaration != variable.declaration)
                    {
                        return false;
                    }
                    let mut node = occurrence.parent();
                    while let Some(parent) = node {
                        if parent.kind() == "return_statement" {
                            return true;
                        }
                        if parent.kind() == "function_definition" {
                            break;
                        }
                        node = parent.parent();
                    }
                    false
                })
            });
        if returned {
            continue;
        }
        let begin = declarator.end_byte();
        let end = first_escape(facts, variable, begin, block.end_byte(), allocators).min(
            automatic_macro_cutoff(facts, variable, begin, block.end_byte(), records),
        );
        if begin < end {
            ranges.push(FreshInitializationRange {
                receiver: variable.name.clone(),
                declaration: variable.declaration,
                begin,
                end,
            });
        }
    }
    ranges
}

fn automatic_macro_cutoff(
    facts: &FileFacts<'_>,
    variable: &Variable<'_>,
    begin: usize,
    end: usize,
    records: &AutomaticRecords,
) -> usize {
    let mut pending = vec![variable.name.clone()];
    let mut visited = HashSet::new();
    let mut limit = end;
    while let Some(name) = pending.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        let Some(macros) = records.macro_users.get(&name) else {
            continue;
        };
        for name in macros {
            pending.push(name.clone());
            if let Some(occurrences) = facts.occurrences.get(name) {
                for occurrence in occurrences
                    .iter()
                    .filter(|node| begin <= node.start_byte() && node.start_byte() < end)
                {
                    let mut cutoff = occurrence.start_byte();
                    let mut parent = occurrence.parent();
                    while let Some(node) = parent {
                        if matches!(
                            node.kind(),
                            "for_statement" | "for_range_loop" | "while_statement" | "do_statement"
                        ) && begin <= node.start_byte()
                        {
                            cutoff = cutoff.min(node.start_byte());
                        }
                        if node.start_byte() < begin || node.end_byte() > end {
                            break;
                        }
                        parent = node.parent();
                    }
                    limit = limit.min(cutoff);
                }
            }
        }
    }
    limit
}

fn fresh_ranges(facts: &FileFacts<'_>, allocators: &Allocators) -> Vec<FreshInitializationRange> {
    let Some(tree) = &facts.file.tree else {
        return Vec::new();
    };
    fresh_ranges_in(facts, allocators, tree.root_node())
}

fn fresh_ranges_in(
    facts: &FileFacts<'_>,
    allocators: &Allocators,
    root: Node<'_>,
) -> Vec<FreshInitializationRange> {
    let mut ranges = Vec::new();
    walk_nodes(root, &mut |node| {
        let (target, value, statement) = match node.kind() {
            "init_declarator" => {
                let (Some(target), Some(value), Some(statement)) = (
                    node.child_by_field_name("declarator")
                        .and_then(variable_name),
                    node.child_by_field_name("value"),
                    node.parent(),
                ) else {
                    return;
                };
                (target, value, statement)
            }
            "assignment_expression" => {
                if node
                    .child_by_field_name("operator")
                    .is_some_and(|op| node_text(op, &facts.file.source) != "=")
                {
                    return;
                }
                let (Some(target), Some(value), Some(statement)) = (
                    node.child_by_field_name("left"),
                    node.child_by_field_name("right"),
                    node.parent(),
                ) else {
                    return;
                };
                if target.kind() != "identifier" || statement.kind() != "expression_statement" {
                    return;
                }
                (target, value, statement)
            }
            _ => return,
        };
        let name = node_text(target, &facts.file.source);
        let Some(variable) = binding(facts, name, target.start_byte()) else {
            return;
        };
        if !variable.local || !variable.pointer {
            return;
        }
        let Some(block) = statement
            .parent()
            .filter(|parent| parent.kind() == "compound_statement")
        else {
            return;
        };
        let Some(function) = enclosing_function(statement) else {
            return;
        };
        if facts.jumping_functions.contains(&function.start_byte())
            || !fresh_expression(value, &facts.file.source, allocators, &|callee| {
                binding(facts, callee, value.start_byte()).is_some()
                    || !allocators.available(callee, &facts.file.path, value.start_byte())
            })
        {
            return;
        }
        if statement.has_error() {
            return;
        }
        let begin = value.end_byte();
        let syntax_end = syntax_prefix_end(facts, begin, block.end_byte());
        if syntax_end <= begin {
            return;
        }
        let (family, aliases) = local_allocation_aliases(facts, variable, begin, block, allocators);
        let end = family
            .iter()
            .map(|member| {
                first_escape_except(facts, member, begin, syntax_end, allocators, &aliases)
            })
            .min()
            .unwrap_or(syntax_end);
        for member in family {
            if begin < end {
                ranges.push(FreshInitializationRange {
                    receiver: member.name.clone(),
                    declaration: member.declaration,
                    // Preserve the original allocation domain, including any
                    // parallel construct between allocation and alias binding.
                    begin,
                    end,
                });
            }
        }
    });
    ranges
}

/// Recovery elsewhere in a large body must not invalidate an earlier complete
/// statement. No proof crosses an error; a later error in a loop invalidates
/// that loop's earlier accesses too, because they may execute again.
fn syntax_prefix_end(facts: &FileFacts<'_>, begin: usize, end: usize) -> usize {
    let mut limit = end;
    for error in facts
        .syntax_errors
        .iter()
        .filter(|n| n.start_byte() < end && n.end_byte() >= begin)
    {
        let mut boundary = error.start_byte();
        let mut ancestor = error.parent();
        while let Some(node) = ancestor {
            if node.start_byte() < begin || node.end_byte() > end {
                break;
            }
            if matches!(
                node.kind(),
                "for_statement" | "for_range_loop" | "while_statement" | "do_statement"
            ) {
                boundary = boundary.min(node.start_byte());
            }
            ancestor = node.parent();
        }
        limit = limit.min(boundary);
    }
    limit
}

fn first_escape(
    facts: &FileFacts<'_>,
    variable: &Variable<'_>,
    begin: usize,
    end: usize,
    allocators: &Allocators,
) -> usize {
    first_escape_except(facts, variable, begin, end, allocators, &HashSet::new())
}

fn first_escape_except(
    facts: &FileFacts<'_>,
    variable: &Variable<'_>,
    begin: usize,
    end: usize,
    allocators: &Allocators,
    allowed: &HashSet<usize>,
) -> usize {
    let Some(occurrences) = facts.occurrences.get(&variable.name) else {
        return end;
    };
    let mut limit = end;
    for occurrence in occurrences
        .iter()
        .filter(|node| begin <= node.start_byte() && node.start_byte() < end)
    {
        if allowed.contains(&occurrence.start_byte()) {
            continue;
        }
        if binding(facts, &variable.name, occurrence.start_byte())
            .is_none_or(|bound| bound.declaration != variable.declaration)
        {
            continue;
        }
        if let Some(mut escape) = escape_site(*occurrence, facts, allocators) {
            let mut ancestor = occurrence.parent();
            while let Some(parent) = ancestor {
                // If the allocation is outside a loop, source lines before a
                // handoff can execute again after that handoff on a later turn.
                if matches!(
                    parent.kind(),
                    "for_statement" | "for_range_loop" | "while_statement" | "do_statement"
                ) && begin <= parent.start_byte()
                {
                    escape = escape.min(parent.start_byte());
                }
                if parent.start_byte() < begin || parent.end_byte() > end {
                    break;
                }
                ancestor = parent.parent();
            }
            limit = limit.min(escape);
        }
    }
    limit
}

/// A declaration-only alias in the same block does not publish a pointer.
/// All aliases share the earliest escape boundary; rebinding any member stays
/// conservative. Unknown offsets, scopes, types and excess aliases terminate
/// the proof through the ordinary escape scan instead of being ignored.
fn local_allocation_aliases<'a, 'tree>(
    facts: &'a FileFacts<'tree>,
    root: &'a Variable<'tree>,
    begin: usize,
    block: Node<'tree>,
    allocators: &Allocators,
) -> (Vec<&'a Variable<'tree>>, HashSet<usize>) {
    let mut family = vec![root];
    let mut allowed = HashSet::new();
    if !primitive_pointer(root) {
        return (family, allowed);
    }
    let mut proven = HashSet::from([(root.name.clone(), root.declaration)]);
    let mut variables = facts
        .variables
        .values()
        .flatten()
        .filter(|variable| {
            variable.local
                && primitive_pointer(variable)
                && variable.declarator.start_byte() >= begin
                && variable.declaration_node.parent() == Some(block)
        })
        .collect::<Vec<_>>();
    variables.sort_by_key(|variable| variable.declarator.start_byte());
    let bounded = bounded_alias_candidates(facts, begin, block);
    // A bounded non-primitive alias can make a later primitive alias safe, so
    // run the two local alias scans to a fixed point. The small cap prevents a
    // malformed recovery tree from turning this into an unbounded analysis.
    for _ in 0..4 {
        let mut changed = false;
        for variable in &variables {
            if family.len() >= 32 {
                break;
            }
            let Some(value) = variable
                .declarator
                .child_by_field_name("value")
                .and_then(|value| proven_allocation_alias_base(facts, value, allocators))
            else {
                continue;
            };
            if !proven_alias_base(facts, value, &proven) {
                continue;
            }
            let Some(target) = variable_name(variable.declarator) else {
                continue;
            };
            if !proven.insert((variable.name.clone(), variable.declaration)) {
                continue;
            }
            allowed.insert(value.start_byte());
            allowed.insert(target.start_byte());
            family.push(*variable);
            changed = true;
        }
        for candidate in &bounded {
            if family.len() >= 32 {
                break;
            }
            let candidate_base_proven = proven_alias_base(facts, candidate.base, &proven);
            let candidate_uses_safe = bounded_alias_uses(facts, candidate, block);
            if proven.contains(&(candidate.name.clone(), candidate.declaration))
                || !candidate_base_proven
                || !candidate_uses_safe
            {
                continue;
            }
            if !proven.insert((candidate.name.clone(), candidate.declaration)) {
                continue;
            }
            // The source occurrence, rather than the whole cast expression,
            // is what first_escape_except visits.
            allowed.insert(candidate.base.start_byte());
            changed = true;
        }
        if !changed {
            break;
        }
    }
    if facts.file.is_c {
        let mut tables = facts
            .variables
            .values()
            .flatten()
            .filter(|variable| {
                variable.local
                    && variable.declarator.start_byte() >= begin
                    && variable.declaration_node.parent() == Some(block)
            })
            .collect::<Vec<_>>();
        tables.sort_by_key(|variable| variable.declarator.start_byte());
        for table in tables {
            if family.len() >= 32 {
                break;
            }
            if let Some(uses) = private_pointer_table_uses(facts, table, &family, block) {
                allowed.extend(uses);
                family.push(table);
            }
        }
    }
    (family, allowed)
}

#[derive(Clone)]
enum BoundedAliasShape {
    PointerArray,
    PlainRecord(Vec<String>),
}

struct BoundedAliasCandidate<'tree> {
    name: String,
    declaration: usize,
    declaration_end: usize,
    base: Node<'tree>,
    shape: BoundedAliasShape,
}

/// Collect only local aliases whose pointee shape admits a complete scalar
/// use proof. The pointer-to-array form is recovered from tree-sitter's C++
/// declaration ambiguity (`float (*p)[N]` is an assignment expression in
/// some recovery trees); named record pointers use an ordinary declaration.
fn bounded_alias_candidates<'tree>(
    facts: &FileFacts<'tree>,
    begin: usize,
    block: Node<'tree>,
) -> Vec<BoundedAliasCandidate<'tree>> {
    let source = &facts.file.source;
    let mut candidates = Vec::new();
    if let Some(tree) = &facts.file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            let Some(candidate) = pointer_array_alias_assignment(facts, node, begin, block) else {
                return;
            };
            candidates.push(candidate);
        });
    }
    for variable in facts.variables.values().flatten().filter(|variable| {
        variable.local
            && variable.pointer
            && !primitive_pointer(variable)
            && variable.declarator.start_byte() >= begin
            && variable.declaration_node.parent() == Some(block)
    }) {
        let Some(shape) = plain_record_alias_shape(facts, variable) else {
            continue;
        };
        let Some(value) = variable.declarator.child_by_field_name("value") else {
            continue;
        };
        let Some(base) = bounded_native_alias_base(value, source) else {
            continue;
        };
        candidates.push(BoundedAliasCandidate {
            name: variable.name.clone(),
            declaration: variable.declaration,
            declaration_end: variable.declaration_node.end_byte(),
            base,
            shape,
        });
    }
    candidates.sort_by_key(|candidate| candidate.declaration);
    candidates
}

fn pointer_array_alias_assignment<'tree>(
    facts: &FileFacts<'tree>,
    node: Node<'tree>,
    begin: usize,
    block: Node<'tree>,
) -> Option<BoundedAliasCandidate<'tree>> {
    if node.kind() != "assignment_expression"
        || node.start_byte() < begin
        || node
            .child_by_field_name("operator")
            .is_none_or(|operator| node_text(operator, &facts.file.source) != "=")
    {
        return None;
    }
    let statement = node.parent()?;
    if statement.kind() != "expression_statement" || statement.parent() != Some(block) {
        return None;
    }
    let left = node.child_by_field_name("left")?;
    let alias = left
        .kind()
        .eq("subscript_expression")
        .then(|| left.child_by_field_name("argument"))??;
    if alias.kind() != "call_expression"
        || alias
            .child_by_field_name("function")
            .is_none_or(|function| function.kind() != "primitive_type")
    {
        return None;
    }
    let arguments = alias.child_by_field_name("arguments")?;
    if arguments.named_child_count() != 1 {
        return None;
    }
    let pointer = arguments.named_child(0)?;
    if pointer.kind() != "pointer_expression"
        || pointer
            .child_by_field_name("operator")
            .is_none_or(|operator| node_text(operator, &facts.file.source) != "*")
    {
        return None;
    }
    let target = pointer.child_by_field_name("argument")?;
    if target.kind() != "identifier" {
        return None;
    }
    let indices = left.child_by_field_name("indices")?;
    if indices.named_child_count() != 1
        || !super::evidence::primitive_local_operand(indices.named_child(0)?, &facts.file.source)
    {
        return None;
    }
    let value = node.child_by_field_name("right")?;
    let cast = strip_parenthesized(value);
    let ty = cast
        .kind()
        .eq("cast_expression")
        .then(|| cast.child_by_field_name("type"))??;
    if !primitive_pointer_array_type(ty, &facts.file.source) {
        return None;
    }
    let base = bounded_native_alias_base(value, &facts.file.source)?;
    Some(BoundedAliasCandidate {
        name: node_text(target, &facts.file.source).to_owned(),
        declaration: node.start_byte(),
        declaration_end: statement.end_byte(),
        base,
        shape: BoundedAliasShape::PointerArray,
    })
}

fn primitive_pointer_array_type(ty: Node<'_>, source: &str) -> bool {
    if !ty
        .child_by_field_name("type")
        .is_some_and(|base| matches!(base.kind(), "primitive_type" | "sized_type_specifier"))
    {
        return false;
    }
    let Some(mut declarator) = ty.child_by_field_name("declarator") else {
        return false;
    };
    if declarator.kind() != "abstract_array_declarator"
        || !declarator
            .child_by_field_name("size")
            .is_some_and(|size| super::evidence::primitive_local_operand(size, source))
    {
        return false;
    }
    declarator = match declarator.child_by_field_name("declarator") {
        Some(node) if node.kind() == "abstract_parenthesized_declarator" => node,
        _ => return false,
    };
    declarator
        .named_child(0)
        .is_some_and(|node| node.kind() == "abstract_pointer_declarator")
}

fn bounded_native_alias_base<'tree>(value: Node<'tree>, source: &str) -> Option<Node<'tree>> {
    let value = strip_parenthesized(value);
    if value.kind() != "cast_expression"
        || !value
            .child_by_field_name("type")
            .is_some_and(|ty| pointer_type_text(ty, source))
    {
        return None;
    }
    allocation_alias_base(value.child_by_field_name("value")?, source)
}

fn bounded_index_operand(facts: &FileFacts<'_>, operand: Node<'_>) -> bool {
    let source = &facts.file.source;
    let operand = strip_parenthesized(operand);
    match operand.kind() {
        "number_literal" | "char_literal" | "sizeof_expression" => true,
        "unary_expression" => {
            let Some(operator) = operand.child_by_field_name("operator") else {
                return false;
            };
            let Some(argument) = operand.child_by_field_name("argument") else {
                return false;
            };
            node_text(operator, source)
                .chars()
                .all(|operator| matches!(operator, '+' | '-' | '~'))
                && bounded_index_operand(facts, argument)
        }
        "binary_expression" => {
            let Some(operator) = operand.child_by_field_name("operator") else {
                return false;
            };
            let Some(left) = operand.child_by_field_name("left") else {
                return false;
            };
            let Some(right) = operand.child_by_field_name("right") else {
                return false;
            };
            let operator = node_text(operator, source);
            matches!(
                operator,
                "+" | "-" | "*" | "/" | "%" | "<<" | ">>" | "&" | "|" | "^"
            ) && bounded_index_operand(facts, left)
                && bounded_index_operand(facts, right)
        }
        "conditional_expression" => {
            let Some(consequence) = operand.child_by_field_name("consequence") else {
                return false;
            };
            let Some(alternative) = operand.child_by_field_name("alternative") else {
                return false;
            };
            bounded_index_operand(facts, consequence) && bounded_index_operand(facts, alternative)
        }
        "cast_expression" => {
            let Some(ty) = operand.child_by_field_name("type") else {
                return false;
            };
            let Some(value) = operand.child_by_field_name("value") else {
                return false;
            };
            !node_text(ty, source).contains(['*', '&']) && bounded_index_operand(facts, value)
        }
        "identifier" => {
            let name = node_text(operand, source);
            binding(facts, name, operand.start_byte()).is_some_and(|variable| {
                let shape = if variable.declarator.kind() == "init_declarator" {
                    variable
                        .declarator
                        .child_by_field_name("declarator")
                        .unwrap_or(variable.declarator)
                } else {
                    variable.declarator
                };
                !variable.pointer
                    && !node_text(shape, source).contains(['[', '*', '&'])
                    && variable
                        .declaration_node
                        .child_by_field_name("type")
                        .is_some_and(|ty| {
                            matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                        })
            })
        }
        _ => super::evidence::primitive_local_operand(operand, source),
    }
}

fn plain_record_alias_shape(
    facts: &FileFacts<'_>,
    variable: &Variable<'_>,
) -> Option<BoundedAliasShape> {
    let mut declarator = variable.declarator;
    if declarator.kind() == "init_declarator" {
        declarator = declarator.child_by_field_name("declarator")?;
    }
    if declarator.kind() != "pointer_declarator"
        || declarator
            .child_by_field_name("declarator")
            .is_none_or(|declarator| declarator.kind() != "identifier")
    {
        return None;
    }
    let ty = variable.declaration_node.child_by_field_name("type")?;
    let type_name = node_text(ty, &facts.file.source).trim();
    if type_name.is_empty() {
        return None;
    }
    let function = enclosing_function(variable.declaration_node);
    let mut matches = Vec::new();
    if let Some(tree) = &facts.file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "type_definition"
                || node.start_byte() >= variable.declaration
                || enclosing_function(node) != function
                || !node
                    .child_by_field_name("declarator")
                    .is_some_and(|declarator| {
                        node_text(declarator, &facts.file.source) == type_name
                    })
            {
                return;
            }
            let Some(record) = node.child_by_field_name("type") else {
                return;
            };
            if record.kind() != "struct_specifier" {
                return;
            }
            let Some(body) = record.child_by_field_name("body") else {
                return;
            };
            let mut fields = Vec::new();
            let mut valid = true;
            for field in body.named_children(&mut body.walk()) {
                if field.kind() != "field_declaration"
                    || !field.child_by_field_name("type").is_some_and(|field_type| {
                        matches!(field_type.kind(), "primitive_type" | "sized_type_specifier")
                    })
                {
                    valid = false;
                    break;
                }
                let mut cursor = field.walk();
                let declarators = field
                    .children_by_field_name("declarator", &mut cursor)
                    .collect::<Vec<_>>();
                if declarators.len() != 1 || declarators[0].kind() != "field_identifier" {
                    valid = false;
                    break;
                }
                fields.push(node_text(declarators[0], &facts.file.source).to_owned());
            }
            if valid && !fields.is_empty() {
                matches.push(fields);
            }
        });
    }
    (matches.len() == 1).then(|| BoundedAliasShape::PlainRecord(matches.remove(0)))
}

fn proven_alias_base(
    facts: &FileFacts<'_>,
    base: Node<'_>,
    proven: &HashSet<(String, usize)>,
) -> bool {
    let name = node_text(base, &facts.file.source);
    binding(facts, name, base.start_byte())
        .is_some_and(|variable| proven.contains(&(variable.name.clone(), variable.declaration)))
}

fn bounded_alias_uses(
    facts: &FileFacts<'_>,
    candidate: &BoundedAliasCandidate<'_>,
    block: Node<'_>,
) -> bool {
    let Some(occurrences) = facts.occurrences.get(&candidate.name) else {
        return false;
    };
    let expected_binding = facts
        .variables
        .get(&candidate.name)
        .into_iter()
        .flatten()
        .find(|variable| variable.declaration == candidate.declaration)
        .map(|variable| variable.declaration);
    if expected_binding.is_none() && facts.variables.contains_key(&candidate.name) {
        return false;
    }
    let mut saw_use = false;
    for occurrence in occurrences {
        if occurrence.start_byte() <= candidate.declaration_end {
            continue;
        }
        if occurrence.start_byte() < block.start_byte() || occurrence.end_byte() > block.end_byte()
        {
            if expected_binding.is_some()
                && binding(facts, &candidate.name, occurrence.start_byte())
                    .is_none_or(|variable| Some(variable.declaration) != expected_binding)
            {
                continue;
            }
            return false;
        }
        if let Some(expected) = expected_binding
            && binding(facts, &candidate.name, occurrence.start_byte())
                .is_none_or(|variable| variable.declaration != expected)
        {
            continue;
        }
        if pointer_alias_transfer(facts, *occurrence, block)
            || bounded_alias_scalar_use(facts, *occurrence, &candidate.shape, block)
        {
            saw_use = true;
        } else {
            return false;
        }
    }
    saw_use
}

fn pointer_alias_transfer(facts: &FileFacts<'_>, occurrence: Node<'_>, block: Node<'_>) -> bool {
    let source = &facts.file.source;
    let mut ancestor = occurrence.parent();
    while let Some(node) = ancestor {
        if node.kind() == "init_declarator"
            && node.child_by_field_name("value").is_some_and(|value| {
                value.start_byte() <= occurrence.start_byte()
                    && occurrence.end_byte() <= value.end_byte()
            })
        {
            let Some(declaration) = node.parent() else {
                return false;
            };
            let Some(name) = node
                .child_by_field_name("declarator")
                .and_then(variable_name)
            else {
                return false;
            };
            let name = node_text(name, source);
            let Some(variable) = facts
                .variables
                .get(name)
                .into_iter()
                .flatten()
                .find(|variable| variable.declaration_node == declaration)
            else {
                return false;
            };
            let Some(value) = node.child_by_field_name("value") else {
                return false;
            };
            return declaration.parent() == Some(block)
                && variable.local
                && primitive_pointer(variable)
                && bounded_native_alias_base(value, source)
                    .is_some_and(|base| base.start_byte() == occurrence.start_byte());
        }
        if node == block {
            break;
        }
        ancestor = node.parent();
    }
    false
}

fn bounded_alias_scalar_use(
    facts: &FileFacts<'_>,
    occurrence: Node<'_>,
    shape: &BoundedAliasShape,
    block: Node<'_>,
) -> bool {
    let source = &facts.file.source;
    let mut current = occurrence;
    let mut indexed = 0;
    loop {
        let Some(parent) = current.parent() else {
            return false;
        };
        if parent.kind() != "subscript_expression"
            || parent.child_by_field_name("argument") != Some(current)
        {
            break;
        }
        let Some(indices) = parent.child_by_field_name("indices") else {
            return false;
        };
        if indices.named_child_count() != 1
            || !indices
                .named_child(0)
                .is_some_and(|index| bounded_index_operand(facts, index))
        {
            return false;
        }
        indexed += 1;
        current = parent;
    }
    match shape {
        BoundedAliasShape::PointerArray if indexed < 2 => return false,
        BoundedAliasShape::PlainRecord(fields) if indexed != 1 => return false,
        _ => {}
    }
    if let BoundedAliasShape::PlainRecord(fields) = shape {
        let Some(field) = current.parent().filter(|parent| {
            parent.kind() == "field_expression"
                && parent.child_by_field_name("argument") == Some(current)
        }) else {
            return false;
        };
        let Some(name) = field.child_by_field_name("field") else {
            return false;
        };
        if !fields.iter().any(|field| field == node_text(name, source)) {
            return false;
        }
        current = field;
    }
    let calls = facts
        .scalar_parameters
        .get_or_init(|| super::evidence::scalar_calls::collect(facts.file));
    let mut node = current;
    while let Some(parent) = node.parent() {
        if parent == block {
            return true;
        }
        match parent.kind() {
            "pointer_expression" => return false,
            "argument_list" => {
                let scalar_safe =
                    super::evidence::scalar_calls::consumes_value(calls, parent, node, source);
                let element_safe = element_call_consumes(facts, parent, node);
                if !scalar_safe && !element_safe {
                    return false;
                }
            }
            "call_expression" if parent.child_by_field_name("function") == Some(node) => {
                return false;
            }
            "return_statement" | "lambda_expression" => return false,
            "cast_expression" => {
                if parent
                    .child_by_field_name("type")
                    .is_some_and(|ty| node_text(ty, source).contains(['*', '&']))
                {
                    return false;
                }
            }
            "field_expression" | "subscript_expression" => return false,
            _ => {}
        }
        node = parent;
    }
    false
}

/// A fixed automatic table may hold views of one fresh allocation without
/// publishing them. Every slot must be initialized once, directly in this
/// block, before any pointee use. No table/pointee address may leave the block.
/// This does not infer contiguity between unrelated pointed-to allocations.
fn private_pointer_table_uses(
    facts: &FileFacts<'_>,
    table: &Variable<'_>,
    family: &[&Variable<'_>],
    block: Node<'_>,
) -> Option<HashSet<usize>> {
    let source = &facts.file.source;
    if table.declarator.kind() != "pointer_declarator"
        || !table
            .declaration_node
            .child_by_field_name("type")
            .is_some_and(|ty| matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
    {
        return None;
    }
    // Other declarators in the same statement can refer to and publish the
    // table before the post-declaration use scan begins.
    let mut cursor = table.declaration_node.walk();
    if table
        .declaration_node
        .children_by_field_name("declarator", &mut cursor)
        .count()
        != 1
    {
        return None;
    }
    let array = table.declarator.child_by_field_name("declarator")?;
    if array.kind() != "array_declarator"
        || array.child_by_field_name("declarator")?.kind() != "identifier"
    {
        return None;
    }
    let size = array.child_by_field_name("size")?;
    if size.kind() != "number_literal" {
        return None;
    }
    let size = node_text(size, source).parse::<usize>().ok()?;
    if !(1..=32).contains(&size) {
        return None;
    }
    let calls = facts
        .scalar_parameters
        .get_or_init(|| super::evidence::scalar_calls::collect(facts.file));
    let mut initialized = HashSet::new();
    let mut allowed = HashSet::new();
    for usage in facts.occurrences.get(&table.name)?.iter().filter(|usage| {
        usage.start_byte() > table.declaration_node.end_byte()
            && usage.end_byte() < block.end_byte()
            && binding(facts, &table.name, usage.start_byte())
                .is_some_and(|v| v.declaration == table.declaration)
    }) {
        let slot = usage.parent()?;
        if slot.kind() != "subscript_expression"
            || slot.child_by_field_name("argument") != Some(*usage)
        {
            return None;
        }
        let parent = slot.parent()?;
        if parent.kind() == "assignment_expression"
            && parent.child_by_field_name("left") == Some(slot)
        {
            let statement = parent.parent()?;
            if statement.kind() != "expression_statement"
                || statement.parent() != Some(block)
                || node_text(parent.child_by_field_name("operator")?, source) != "="
            {
                return None;
            }
            let index = node_text(slot.child_by_field_name("indices")?.named_child(0)?, source)
                .parse::<usize>()
                .ok()?;
            if index >= size || !initialized.insert(index) {
                return None;
            }
            let value = allocation_alias_base(parent.child_by_field_name("right")?, source)?;
            let base = binding(facts, node_text(value, source), value.start_byte())?;
            if !family.iter().any(|v| {
                primitive_pointer(v) && v.declaration == base.declaration && v.name == base.name
            }) {
                return None;
            }
            allowed.insert(value.start_byte());
        } else {
            if initialized.len() != size
                || parent.kind() != "subscript_expression"
                || parent.child_by_field_name("argument") != Some(slot)
            {
                return None;
            }
            for subscript in [slot, parent] {
                let indices = subscript.child_by_field_name("indices")?;
                if indices.named_child_count() != 1
                    || !super::evidence::primitive_local_operand(indices.named_child(0)?, source)
                {
                    return None;
                }
            }
            let mut element = parent;
            while let Some(outer) = element.parent() {
                if matches!(
                    outer.kind(),
                    "pointer_expression"
                        | "field_expression"
                        | "subscript_expression"
                        | "lambda_expression"
                        | "ERROR"
                ) {
                    return None;
                }
                if outer.kind() == "argument_list" {
                    if !super::evidence::scalar_calls::consumes_value(calls, outer, element, source)
                    {
                        return None;
                    }
                    break;
                }
                if matches!(
                    outer.kind(),
                    "expression_statement"
                        | "declaration"
                        | "return_statement"
                        | "condition_clause"
                ) {
                    break;
                }
                element = outer;
            }
        }
        allowed.insert(usage.start_byte());
    }
    if initialized.len() != size
        || super::evidence::automatic_storage_scope_may_fork(
            &source[table.declaration_node.end_byte()..block.end_byte()],
        )
    {
        return None;
    }
    // Unknown calls can be macros capturing the table without an argument.
    // A bound C function cannot access an unpassed automatic table.
    let mut opaque = false;
    walk_nodes(block, &mut |node| {
        if node.start_byte() <= table.declaration_node.end_byte() {
            return;
        }
        opaque |= node.kind() == "call_expression"
            && !super::evidence::scalar_calls::declared_c_call(calls, node, source);
    });
    if let Some(tree) = &facts.file.tree {
        let remaining_tokens = source[table.declaration_node.start_byte()..block.end_byte()]
            .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .collect::<HashSet<_>>();
        walk_nodes(tree.root_node(), &mut |node| {
            if matches!(node.kind(), "preproc_def" | "preproc_function_def") {
                opaque |= node
                    .child_by_field_name("name")
                    .is_some_and(|name| remaining_tokens.contains(node_text(name, source)));
                opaque |= node_text(node, source)
                    .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                    .any(|name| name == table.name);
            }
        });
    }
    (!opaque).then_some(allowed)
}

/// Recover the one integer-address idiom that preserves a fresh allocation:
/// convert one native pointer to `uintptr_t`, add a constant alignment delta,
/// and round it down either with a power-of-two mask or with division and
/// multiplication by the same power of two.  The syntax alone is insufficient
/// because rounding can move the pointer past a short allocation, so the
/// allocation must also have a source-proved lower bound for the alignment
/// adjustment.
fn proven_allocation_alias_base<'tree>(
    facts: &FileFacts<'tree>,
    value: Node<'tree>,
    allocators: &Allocators,
) -> Option<Node<'tree>> {
    if let Some(base) = allocation_alias_base(value, &facts.file.source) {
        return Some(base);
    }
    let (base, alignment) = rounded_integer_pointer_base(value, &facts.file.source)?;
    let variable = binding(
        facts,
        node_text(base, &facts.file.source),
        base.start_byte(),
    )?;
    let capacity = allocation_capacity_lower_bound(facts, variable, allocators)?;
    (alignment > 1 && alignment.is_power_of_two() && capacity >= alignment).then_some(base)
}

fn rounded_integer_pointer_base<'tree>(
    mut value: Node<'tree>,
    source: &str,
) -> Option<(Node<'tree>, u128)> {
    value = strip_pointer_casts(value, source);
    value = strip_parenthesized(value);

    if value.kind() == "binary_expression"
        && value
            .child_by_field_name("operator")
            .is_some_and(|operator| node_text(operator, source) == "*")
    {
        let left = value.child_by_field_name("left")?;
        let right = value.child_by_field_name("right")?;
        let (quotient, alignment) = if let Some(alignment) = integer_constant(right, source) {
            (left, alignment)
        } else if let Some(alignment) = integer_constant(left, source) {
            (right, alignment)
        } else {
            return None;
        };
        let quotient = strip_parenthesized(quotient);
        if quotient.kind() != "binary_expression"
            || quotient
                .child_by_field_name("operator")
                .is_none_or(|operator| node_text(operator, source) != "/")
            || integer_constant(quotient.child_by_field_name("right")?, source) != Some(alignment)
        {
            return None;
        }
        let (base, adjustment) =
            address_plus_constant(quotient.child_by_field_name("left")?, source)?;
        return (adjustment.checked_add(1) == Some(alignment)
            && alignment > 1
            && alignment.is_power_of_two())
        .then_some((base, alignment));
    }

    if value.kind() == "binary_expression"
        && value
            .child_by_field_name("operator")
            .is_some_and(|operator| node_text(operator, source) == "&")
    {
        let left = value.child_by_field_name("left")?;
        let right = value.child_by_field_name("right")?;
        let (address, mask) = if let Some(mask) = complement_constant(right, source) {
            (left, mask)
        } else if let Some(mask) = complement_constant(left, source) {
            (right, mask)
        } else {
            return None;
        };
        let (base, adjustment) = address_plus_constant(address, source)?;
        return (adjustment.checked_add(1) == Some(mask) && mask > 1 && mask.is_power_of_two())
            .then_some((base, mask));
    }

    None
}

fn strip_pointer_casts<'tree>(mut value: Node<'tree>, source: &str) -> Node<'tree> {
    for _ in 0..16 {
        value = strip_parenthesized(value);
        if value.kind() == "cast_expression"
            && value
                .child_by_field_name("type")
                .is_some_and(|ty| pointer_type_text(ty, source))
            && let Some(inner) = value.child_by_field_name("value")
        {
            value = inner;
            continue;
        }
        if value.kind() == "call_expression"
            && value
                .child_by_field_name("function")
                .is_some_and(|function| {
                    let text = node_text(function, source);
                    cast_target_text(text).is_some_and(pointer_type_text_text)
                })
            && let Some(argument) = value
                .child_by_field_name("arguments")
                .and_then(|arguments| arguments.named_child(0))
        {
            value = argument;
            continue;
        }
        break;
    }
    value
}

fn strip_parenthesized<'tree>(mut value: Node<'tree>) -> Node<'tree> {
    for _ in 0..16 {
        if value.kind() != "parenthesized_expression" {
            break;
        }
        let Some(inner) = value.named_child(0) else {
            break;
        };
        value = inner;
    }
    value
}

fn address_plus_constant<'tree>(value: Node<'tree>, source: &str) -> Option<(Node<'tree>, u128)> {
    let value = strip_parenthesized(value);
    if value.kind() != "binary_expression"
        || value
            .child_by_field_name("operator")
            .is_none_or(|operator| node_text(operator, source) != "+")
    {
        return None;
    }
    let left = value.child_by_field_name("left")?;
    let right = value.child_by_field_name("right")?;
    if let Some(base) = integer_pointer_root(left, source) {
        return Some((base, integer_constant(right, source)?));
    }
    if let Some(base) = integer_pointer_root(right, source) {
        return Some((base, integer_constant(left, source)?));
    }
    None
}

fn integer_pointer_root<'tree>(mut value: Node<'tree>, source: &str) -> Option<Node<'tree>> {
    value = strip_parenthesized(value);
    if value.kind() == "cast_expression"
        && value
            .child_by_field_name("type")
            .is_some_and(|ty| integer_address_type(ty, source))
    {
        return identifier_value(value.child_by_field_name("value")?);
    }
    if value.kind() == "call_expression"
        && value
            .child_by_field_name("function")
            .is_some_and(|function| {
                let text = node_text(function, source);
                integer_address_type_text(text)
                    || cast_target_text(text).is_some_and(integer_address_type_text)
            })
    {
        let arguments = value.child_by_field_name("arguments")?;
        if arguments.named_child_count() != 1 {
            return None;
        }
        return identifier_value(arguments.named_child(0)?);
    }
    None
}

fn identifier_value(mut value: Node<'_>) -> Option<Node<'_>> {
    value = strip_parenthesized(value);
    (value.kind() == "identifier").then_some(value)
}

fn complement_constant(value: Node<'_>, source: &str) -> Option<u128> {
    let value = strip_parenthesized(value);
    if value.kind() != "unary_expression"
        || value
            .child_by_field_name("operator")
            .is_none_or(|operator| node_text(operator, source) != "~")
    {
        return None;
    }
    integer_constant(value.child_by_field_name("argument")?, source)
        .and_then(|mask| mask.checked_add(1))
}

fn integer_constant(value: Node<'_>, source: &str) -> Option<u128> {
    let value = strip_parenthesized(value);
    match value.kind() {
        "number_literal" => parse_integer_literal(node_text(value, source)),
        "cast_expression" => {
            let ty = value.child_by_field_name("type")?;
            let constant = integer_constant(value.child_by_field_name("value")?, source)?;
            (integer_type_text(node_text(ty, source))
                && integer_cast_fits(node_text(ty, source), constant))
            .then_some(constant)
        }
        "call_expression" => {
            let function = value.child_by_field_name("function")?;
            let text = node_text(function, source);
            let target = cast_target_text(text).unwrap_or(text);
            if !integer_type_text(target) {
                return None;
            }
            let arguments = value.child_by_field_name("arguments")?;
            if arguments.named_child_count() != 1 {
                return None;
            }
            let constant = integer_constant(arguments.named_child(0)?, source)?;
            integer_cast_fits(target, constant).then_some(constant)
        }
        "unary_expression" => {
            let operator = node_text(value.child_by_field_name("operator")?, source);
            let operand = integer_constant(value.child_by_field_name("argument")?, source)?;
            match operator {
                "+" => Some(operand),
                "-" => 0u128.checked_sub(operand),
                _ => None,
            }
        }
        "binary_expression" => {
            let left = integer_constant(value.child_by_field_name("left")?, source)?;
            let right = integer_constant(value.child_by_field_name("right")?, source)?;
            match node_text(value.child_by_field_name("operator")?, source) {
                "+" => left.checked_add(right),
                "-" => left.checked_sub(right),
                "*" => left.checked_mul(right),
                "/" if right != 0 => Some(left / right),
                "%" if right != 0 => Some(left % right),
                "<<" => left.checked_shl(u32::try_from(right).ok()?),
                "&" => Some(left & right),
                "|" => Some(left | right),
                "^" => Some(left ^ right),
                _ => None,
            }
        }
        _ => None,
    }
}

fn parse_integer_literal(text: &str) -> Option<u128> {
    let text = text.trim().replace('\'', "");
    let text = text.trim_end_matches(['u', 'U', 'l', 'L']);
    if text.is_empty() {
        return None;
    }
    let value = if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        u128::from_str_radix(hex, 16).ok()
    } else if let Some(binary) = text.strip_prefix("0b").or_else(|| text.strip_prefix("0B")) {
        u128::from_str_radix(binary, 2).ok()
    } else if text.len() > 1 && text.starts_with('0') {
        u128::from_str_radix(&text[1..], 8).ok()
    } else {
        text.parse().ok()
    }?;
    allocation_integer_bound(value)
}

/// The allocation argument is eventually consumed as a platform-sized byte
/// count. Keeping the proof within 64 bits rejects source arithmetic that can
/// wrap a normal `size_t`/`uintptr_t` expression before the allocator sees it.
fn allocation_integer_bound(value: u128) -> Option<u128> {
    (value <= u64::MAX as u128).then_some(value)
}

fn integer_cast_fits(type_text: &str, value: u128) -> bool {
    let compact = type_text.split_whitespace().collect::<String>();
    let max = if compact.contains("uint8_t") {
        u8::MAX as u128
    } else if compact.contains("uint16_t") {
        u16::MAX as u128
    } else if compact.contains("uint32_t") {
        u32::MAX as u128
    } else if compact.contains("uint64_t") {
        u64::MAX as u128
    } else if compact.contains("int8_t") {
        i8::MAX as u128
    } else if compact.contains("int16_t") {
        i16::MAX as u128
    } else if compact.contains("int32_t") {
        i32::MAX as u128
    } else if compact.contains("int64_t") {
        i64::MAX as u128
    } else if compact.contains("unsignedchar") {
        u8::MAX as u128
    } else if compact.contains("unsignedshort") {
        u16::MAX as u128
    } else if compact.contains("unsignedint") {
        u32::MAX as u128
    } else if compact.contains("unsignedlonglong")
        || compact.contains("unsignedlong")
        || compact.contains("uintptr_t")
        || compact.contains("size_t")
    {
        u64::MAX as u128
    } else if compact.contains("short") {
        i16::MAX as u128
    } else if compact.contains("char") {
        i8::MAX as u128
    } else if compact.contains("int") {
        i32::MAX as u128
    } else if compact.contains("long") {
        i64::MAX as u128
    } else {
        // size_t, uintptr_t and project typedefs are only accepted for values
        // already bounded to the ordinary platform-sized integer domain.
        u64::MAX as u128
    };
    value <= max
}

fn allocation_capacity_lower_bound(
    facts: &FileFacts<'_>,
    variable: &Variable<'_>,
    allocators: &Allocators,
) -> Option<u128> {
    let value = variable.declarator.child_by_field_name("value")?;
    let call = unwrap_cast(value, &facts.file.source);
    if call.kind() != "call_expression" {
        return None;
    }
    let function = call.child_by_field_name("function")?;
    let text = node_text(function, &facts.file.source);
    let name = short_name(text);
    if text.contains("::") && !text.starts_with("std::") && !text.starts_with("::") {
        return None;
    }
    if !allocators.fresh.contains(name) || binding(facts, name, call.start_byte()).is_some() {
        return None;
    }
    let arguments = call.child_by_field_name("arguments")?;
    let mut active = HashSet::new();
    match name {
        "malloc" if arguments.named_child_count() == 1 => {
            integer_lower_bound(arguments.named_child(0)?, facts, &mut active)
        }
        "calloc" if arguments.named_child_count() == 2 => {
            let count = integer_lower_bound(arguments.named_child(0)?, facts, &mut active)?;
            let size = integer_lower_bound(arguments.named_child(1)?, facts, &mut active)?;
            count.checked_mul(size).and_then(allocation_integer_bound)
        }
        "aligned_alloc" if arguments.named_child_count() == 2 => {
            integer_lower_bound(arguments.named_child(1)?, facts, &mut active)
        }
        _ => None,
    }
}

fn integer_lower_bound(
    value: Node<'_>,
    facts: &FileFacts<'_>,
    active: &mut HashSet<(String, usize)>,
) -> Option<u128> {
    let value = strip_parenthesized(value);
    let source = &facts.file.source;
    match value.kind() {
        "number_literal" => parse_integer_literal(node_text(value, source)),
        "sizeof_expression" => Some(1),
        "cast_expression" => {
            let ty = value.child_by_field_name("type")?;
            if !integer_type_text(node_text(ty, source)) {
                return None;
            }
            // A cast can narrow or wrap an allocation count. Resolve it only
            // when the source is an exact constant that fits the target type;
            // an interval lower bound alone is not enough to prove safety.
            let constant = integer_constant(value.child_by_field_name("value")?, source)?;
            integer_cast_fits(node_text(ty, source), constant).then_some(constant)
        }
        "unary_expression" => {
            let operator = node_text(value.child_by_field_name("operator")?, source);
            match operator {
                "+" => integer_lower_bound(value.child_by_field_name("argument")?, facts, active),
                "!" => Some(0),
                _ => None,
            }
        }
        "binary_expression" => {
            let operator = node_text(value.child_by_field_name("operator")?, source);
            let left = value.child_by_field_name("left")?;
            let right = value.child_by_field_name("right")?;
            match operator {
                "+" => integer_lower_bound(left, facts, active)?
                    .checked_add(integer_lower_bound(right, facts, active)?)
                    .and_then(allocation_integer_bound),
                "*" => integer_lower_bound(left, facts, active)?
                    .checked_mul(integer_lower_bound(right, facts, active)?)
                    .and_then(allocation_integer_bound),
                "/" => {
                    let divisor = integer_constant(right, source)?;
                    if divisor == 0 {
                        None
                    } else {
                        Some(integer_lower_bound(left, facts, active)? / divisor)
                    }
                }
                "%" => integer_constant(right, source)
                    .filter(|divisor| *divisor != 0)
                    .map(|_| 0),
                "<<" => {
                    let shift = integer_constant(right, source)?;
                    integer_lower_bound(left, facts, active)?
                        .checked_shl(u32::try_from(shift).ok()?)
                        .and_then(allocation_integer_bound)
                }
                // A non-negative mask result has a zero lower bound even if
                // the source value is unknown. This is useful for bounded
                // MAX/MIN-style allocation formulas without treating the
                // unknown operand as a precise value.
                "&" => integer_constant(right, source).map(|_| 0),
                "-" => {
                    let right = integer_constant(right, source)?;
                    let left = integer_lower_bound(left, facts, active)?;
                    left.checked_sub(right).and_then(allocation_integer_bound)
                }
                _ => None,
            }
        }
        "conditional_expression" => Some(
            integer_lower_bound(value.child_by_field_name("consequence")?, facts, active)?.min(
                integer_lower_bound(value.child_by_field_name("alternative")?, facts, active)?,
            ),
        ),
        "call_expression" => {
            let function = value.child_by_field_name("function")?;
            let name = short_name(node_text(function, source));
            if !matches!(name, "MAX" | "max" | "Max") {
                return None;
            }
            let arguments = value.child_by_field_name("arguments")?;
            let mut lower = None;
            for argument in arguments.named_children(&mut arguments.walk()) {
                if let Some(candidate) = integer_lower_bound(argument, facts, active) {
                    lower = Some(lower.map_or(candidate, |current: u128| current.max(candidate)));
                }
            }
            lower.and_then(allocation_integer_bound)
        }
        "identifier" => {
            let name = node_text(value, source).to_owned();
            let variable = binding(facts, &name, value.start_byte())?;
            let key = (name, variable.declaration);
            if !active.insert(key.clone()) {
                return None;
            }
            let result = if variable
                .declaration_node
                .child_by_field_name("type")
                .is_some_and(|ty| integer_type_text(node_text(ty, source)))
                && (node_text(variable.declaration_node, source)
                    .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                    .any(|word| matches!(word, "const" | "constexpr"))
                    || (unsigned_integer_type(variable.declaration_node, source)
                        && wide_unsigned_integer_type(variable.declaration_node, source)))
            {
                variable
                    .declarator
                    .child_by_field_name("value")
                    .map_or(Some(0), |initializer| {
                        integer_lower_bound(initializer, facts, active)
                    })
            } else {
                None
            };
            active.remove(&key);
            result
        }
        _ => None,
    }
}

fn cast_target_text(text: &str) -> Option<&str> {
    let start = text.find('<')?;
    let end = text.rfind('>')?;
    (start < end).then_some(text[start + 1..end].trim())
}

fn pointer_type_text(ty: Node<'_>, source: &str) -> bool {
    pointer_type_text_text(node_text(ty, source))
}

fn pointer_type_text_text(text: &str) -> bool {
    let compact = text.split_whitespace().collect::<String>();
    compact.contains('*') && !compact.contains('&')
}

fn integer_address_type(ty: Node<'_>, source: &str) -> bool {
    integer_address_type_text(node_text(ty, source))
}

fn integer_address_type_text(text: &str) -> bool {
    matches!(
        text.split_whitespace().collect::<String>().as_str(),
        "uintptr_t" | "::uintptr_t" | "std::uintptr_t"
    )
}

fn integer_type_text(text: &str) -> bool {
    let compact = text.split_whitespace().collect::<String>();
    !compact.contains(['*', '&'])
        && !compact.contains("float")
        && !compact.contains("double")
        && !compact.contains("bool")
        && (compact.contains("int")
            || compact.contains("long")
            || compact.contains("short")
            || compact.contains("char")
            || compact.contains("size_t")
            || compact.contains("ptrdiff_t"))
}

fn unsigned_integer_type(declaration: Node<'_>, source: &str) -> bool {
    let text = node_text(declaration, source);
    text.split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
        .any(|word| {
            word == "unsigned" || word.starts_with("uint") || matches!(word, "size_t" | "uintptr_t")
        })
}

fn wide_unsigned_integer_type(declaration: Node<'_>, source: &str) -> bool {
    let compact = node_text(declaration, source)
        .split_whitespace()
        .collect::<String>();
    compact.contains("uint64_t")
        || compact.contains("unsignedlong")
        || compact.contains("size_t")
        || compact.contains("uintptr_t")
}

fn allocation_alias_base<'tree>(mut value: Node<'tree>, source: &str) -> Option<Node<'tree>> {
    for _ in 0..16 {
        match value.kind() {
            "identifier" => return Some(value),
            "parenthesized_expression" => value = value.named_child(0)?,
            "cast_expression" => {
                let ty = value.child_by_field_name("type")?;
                if !primitive_single_pointer_type(ty) {
                    return None;
                }
                value = value.child_by_field_name("value")?;
            }
            "binary_expression" => {
                if !value
                    .child_by_field_name("operator")
                    .is_some_and(|op| matches!(node_text(op, source), "+" | "-"))
                    || !value.child_by_field_name("right").is_some_and(|offset| {
                        super::evidence::primitive_local_operand(offset, source)
                    })
                {
                    return None;
                }
                value = value.child_by_field_name("left")?;
            }
            _ => return None,
        }
    }
    None
}

/// Parentheses in an abstract declarator do not add indirection. Arrays,
/// function pointers, references and user-defined pointee types stay unknown.
fn primitive_single_pointer_type(ty: Node<'_>) -> bool {
    if !ty
        .child_by_field_name("type")
        .is_some_and(|base| matches!(base.kind(), "primitive_type" | "sized_type_specifier"))
    {
        return false;
    }
    let Some(mut shape) = ty.child_by_field_name("declarator") else {
        return false;
    };
    while shape.kind() == "abstract_parenthesized_declarator" {
        let Some(inner) = shape.named_child(0) else {
            return false;
        };
        shape = inner;
    }
    shape.kind() == "abstract_pointer_declarator"
        && shape.child_by_field_name("declarator").is_none()
}

fn primitive_pointer(variable: &Variable<'_>) -> bool {
    let mut declarator = variable.declarator;
    if declarator.kind() == "init_declarator" {
        let Some(inner) = declarator.child_by_field_name("declarator") else {
            return false;
        };
        declarator = inner;
    }
    variable
        .declaration_node
        .child_by_field_name("type")
        .is_some_and(|ty| matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
        && declarator.kind() == "pointer_declarator"
        && declarator
            .child_by_field_name("declarator")
            .is_some_and(|inner| inner.kind() == "identifier")
}

fn escape_site(
    mut node: Node<'_>,
    facts: &FileFacts<'_>,
    allocators: &Allocators,
) -> Option<usize> {
    let source = &facts.file.source;
    let receiver_is_pointer = binding(facts, node_text(node, source), node.start_byte())
        .is_some_and(|variable| variable.pointer);
    let primitive_elements =
        binding(facts, node_text(node, source), node.start_byte()).is_some_and(primitive_pointer);
    let mut ancestor = node.parent();
    while let Some(parent) = ancestor {
        if parent.kind() == "lambda_expression" {
            return Some(parent.start_byte());
        }
        if parent.kind() == "function_definition" {
            break;
        }
        ancestor = parent.parent();
    }
    let mut field_access = false;
    while let Some(parent) = node.parent() {
        match parent.kind() {
            "pointer_expression" if node_text(parent, source).trim_start().starts_with('&') => {
                // Taking a value object's address solely for a recognized
                // memset does not publish it. In contrast, memset(&p, ...)
                // overwrites the pointer variable itself and invalidates a
                // freshness proof about the old allocation addressed by p.
                if (receiver_is_pointer && !field_access)
                    || !address_used_only_by_memset(parent, facts, allocators)
                {
                    return Some(parent.start_byte());
                }
            }
            "lambda_expression" => return Some(parent.start_byte()),
            "return_statement" => return Some(parent.start_byte()),
            "argument_list" => {
                let call = parent.parent()?;
                let synchronous = call.child_by_field_name("function").is_some_and(|callee| {
                    let text = node_text(callee, source);
                    let name = short_name(text);
                    (!text.contains("::") || text.starts_with("std::") || text.starts_with("::"))
                        && allocators.synchronous_memory.contains(name)
                        && binding(facts, name, call.start_byte()).is_none()
                });
                let scalar_copy = primitive_elements
                    && field_access
                    && (super::evidence::scalar_calls::consumes_value(
                        facts
                            .scalar_parameters
                            .get_or_init(|| super::evidence::scalar_calls::collect(facts.file)),
                        parent,
                        node,
                        source,
                    ) || element_call_consumes(facts, parent, node));
                if !synchronous && !scalar_copy {
                    return Some(call.start_byte());
                }
            }
            "call_expression" => {
                if parent.child_by_field_name("function") == Some(node) {
                    return Some(parent.start_byte());
                }
            }
            "field_expression" if parent.child_by_field_name("argument") == Some(node) => {
                field_access = true;
            }
            "subscript_expression" if parent.child_by_field_name("argument") == Some(node) => {
                // p[i] modifies the allocation's contents, not the local p
                // binding. Address-taking and publication still end the proof.
                if !primitive_elements {
                    return Some(parent.start_byte());
                }
                field_access = true;
            }
            "assignment_expression" => {
                if parent.child_by_field_name("left") == Some(node) {
                    if !field_access {
                        return Some(parent.start_byte());
                    }
                    if primitive_elements
                        && !facts.file.is_c
                        && parent
                            .child_by_field_name("operator")
                            .is_some_and(|op| node_text(op, source) != "=")
                        && !parent.child_by_field_name("right").is_some_and(|right| {
                            super::evidence::primitive_local_operand(right, source)
                        })
                    {
                        // A C++ compound operator with a user-defined right
                        // operand can retain a reference to the scalar slot.
                        return Some(parent.start_byte());
                    }
                } else {
                    // Copying a built-in scalar to built-in scalar storage
                    // cannot preserve a reference to the allocation. Reference
                    // targets and user-defined assignment remain unresolved.
                    if primitive_elements
                        && field_access
                        && parent.child_by_field_name("right") == Some(node)
                        && parent.child_by_field_name("left").is_some_and(|left| {
                            super::evidence::primitive_local_operand(left, source)
                        })
                    {
                        return None;
                    }
                    return Some(parent.start_byte());
                }
            }
            "binary_expression" if primitive_elements && !facts.file.is_c => {
                if !["left", "right"].iter().all(|side| {
                    parent.child_by_field_name(side).is_some_and(|operand| {
                        super::evidence::primitive_local_operand(operand, source)
                    })
                }) {
                    return Some(parent.start_byte());
                }
            }
            "cast_expression" if primitive_elements && !facts.file.is_c => {
                if !parent
                    .child_by_field_name("type")
                    .and_then(|ty| ty.child_by_field_name("type"))
                    .is_some_and(|ty| {
                        matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                    })
                {
                    return Some(parent.start_byte());
                }
            }
            "init_declarator" => {
                if primitive_elements
                    && field_access
                    && parent.child_by_field_name("value") == Some(node)
                    && parent
                        .child_by_field_name("declarator")
                        .is_some_and(|decl| decl.kind() == "identifier")
                    && parent
                        .parent()
                        .and_then(|decl| decl.child_by_field_name("type"))
                        .is_some_and(|ty| {
                            matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                        })
                {
                    return None;
                }
                return Some(parent.start_byte());
            }
            "update_expression" if !field_access => return Some(parent.start_byte()),
            "expression_statement"
            | "if_statement"
            | "while_statement"
            | "for_statement"
            | "compound_statement" => {
                // Keep walking to catch implicit lambda captures.
            }
            "function_definition" => return None,
            _ => {}
        }
        node = parent;
    }
    None
}

fn address_used_only_by_memset(
    mut address: Node<'_>,
    facts: &FileFacts<'_>,
    allocators: &Allocators,
) -> bool {
    while let Some(parent) = address.parent() {
        if parent.kind() == "parenthesized_expression" {
            address = parent;
            continue;
        }
        if parent.kind() != "argument_list"
            || parent.named_child(0) != Some(address)
            || parent.named_child_count() != 3
        {
            return false;
        }
        let Some(call) = parent.parent() else {
            return false;
        };
        return call.child_by_field_name("function").is_some_and(|callee| {
            matches!(
                node_text(callee, &facts.file.source),
                "memset" | "::memset" | "std::memset" | "::std::memset"
            ) && allocators.synchronous_memory.contains("memset")
                && binding(facts, "memset", call.start_byte()).is_none()
        });
    }
    false
}

fn fresh_returning_function(
    function: Node<'_>,
    facts: &FileFacts<'_>,
    allocators: &Allocators,
) -> bool {
    let Some(body) = function.child_by_field_name("body") else {
        return false;
    };
    if body.has_error() {
        return false;
    }
    if !mentions_known_allocator(node_text(body, &facts.file.source), allocators) {
        return false;
    }
    let mut fresh = false;
    let mut valid = true;
    let ranges = fresh_ranges_in(facts, allocators, function);
    walk_nodes(body, &mut |node| {
        if node.kind() != "return_statement" || enclosing_function(node) != Some(function) {
            return;
        }
        let Some(value) = node.named_child(0) else {
            valid = false;
            return;
        };
        let value = unwrap_cast(value, &facts.file.source);
        if matches!(
            node_text(value, &facts.file.source).trim(),
            "nullptr" | "NULL" | "0"
        ) {
            return;
        }
        let directly_fresh = fresh_expression(value, &facts.file.source, allocators, &|name| {
            binding(facts, name, value.start_byte()).is_some()
                || !allocators.available(name, &facts.file.path, value.start_byte())
        });
        let local_fresh = value.kind() == "identifier"
            && binding(
                facts,
                node_text(value, &facts.file.source),
                value.start_byte(),
            )
            .is_some_and(|variable| {
                ranges.iter().any(|range| {
                    range.receiver == variable.name
                        && range.declaration == variable.declaration
                        && range.begin <= node.start_byte()
                        && node.start_byte() <= range.end
                })
            });
        fresh |= directly_fresh || local_fresh;
        valid &= directly_fresh || local_fresh;
    });
    fresh && valid
}
