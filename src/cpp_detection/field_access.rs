//! Source syntax facts for member accesses. These are deliberately not ABI or
//! whole-program ownership proofs: they bind an occurrence to its lexical
//! declaration, mutation target, and enclosing function before heuristics run.

use super::*;
use tree_sitter::Node;

#[path = "reference_returns.rs"]
mod reference_returns;
pub(super) use reference_returns::ReferenceReturns;

#[derive(Clone)]
pub(super) struct SyntaxAccess {
    /// Another occurrence on this row still needs heuristic recovery. It must
    /// not erase this occurrence's resolved storage/lifetime/access facts.
    pub needs_line_fallback: bool,
    pub record: usize,
    pub field: String,
    pub kind: CppAccessKind,
    pub start_byte: usize,
    pub atomic: bool,
    pub receiver: Option<String>,
    pub raw_pointer: bool,
    pub initialization: bool,
    pub in_record_constructor: bool,
    pub function: Option<String>,
    pub loop_depth: Option<usize>,
    pub thread_local: bool,
    pub nonescaping_local: bool,
    pub automatic_receiver: bool,
    pub contiguous_element: bool,
    pub element_index: Option<String>,
    pub element_member_path: Vec<String>,
}

struct Binding {
    declaration: usize,
    name_byte: usize,
    begin: usize,
    end: usize,
    record: Option<usize>,
    callable: Option<usize>,
    thread_local: bool,
    local_owner: bool,
    value_parameter: bool,
}

struct Function {
    begin: usize,
    end: usize,
    name: String,
    owner: Option<usize>,
    constructor_unpublished_until: Option<usize>,
}

/// One-hop, receiver-bound propagation from an existing parallel region. Only
/// shared value objects are eligible: opaque pointers, automatic objects,
/// overloaded methods and shadowed names are deliberately not inferred. This
/// bounded recovery targets loop-bearing worker methods, not one-off lifecycle
/// calls (e.g. cleanup after workers finish) or plain metadata getters.
pub(super) fn propagate_shared_method_context(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    lines: &mut HashSet<usize>,
) -> HashMap<usize, Vec<String>> {
    let mut paths = HashMap::new();
    let source_lines = file.source.lines().collect::<Vec<_>>();
    if !lines.iter().any(|line| {
        source_lines
            .get(line.saturating_sub(1))
            .is_some_and(|source| source.contains('.') || source.contains("->"))
    }) {
        return paths;
    }
    let Some(tree) = &file.tree else { return paths };
    let mut aliases: HashMap<String, Vec<String>> = HashMap::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "alias_declaration"
            && let (Some(name), Some(ty)) = (
                node.child_by_field_name("name"),
                node.child_by_field_name("type"),
            )
        {
            aliases
                .entry(node_text(name, &file.source).into())
                .or_default()
                .push(node_text(ty, &file.source).into());
        }
    });
    let resolve = |ty: &str| -> Option<usize> {
        let mut ty = ty.to_owned();
        for _ in 0..8 {
            if ty.contains(['*', '&', '[', ']']) {
                return None;
            }
            let outer = ty.split('<').next()?.trim();
            if let Some(values) = aliases.get(outer) {
                if values.len() != 1 {
                    return None;
                }
                ty = values[0].clone();
            } else {
                return index.unambiguous_record_index(outer, &file.path);
            }
        }
        None
    };
    let mut objects: HashMap<String, Vec<Option<usize>>> = HashMap::new();
    let mut methods: HashMap<(usize, String), Vec<Node<'_>>> = HashMap::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "function_definition"
            && let Some(owner) = function_owner(node, file, index)
            && let Some(name) = function_definition_name(node, file)
            && let Some(body) = node.child_by_field_name("body")
        {
            methods.entry((owner, name)).or_default().push(body);
        }
        if !matches!(
            node.kind(),
            "declaration"
                | "field_declaration"
                | "parameter_declaration"
                | "optional_parameter_declaration"
                | "for_range_loop"
        ) {
            return;
        }
        let text = node_text(node, &file.source);
        let shared = !node.kind().contains("parameter")
            && node.kind() != "for_range_loop"
            && !identifier_tokens(text).any(|s| matches!(s, "thread_local" | "__thread"))
            && (identifier_tokens(text).any(|s| s == "static")
                || (enclosing_callable(node).is_none() && node.kind() == "declaration"));
        let record = node
            .child_by_field_name("type")
            .and_then(|ty| resolve(node_text(ty, &file.source)));
        let mut cursor = node.walk();
        for declarator in node.children_by_field_name("declarator", &mut cursor) {
            if let Some(name) = declarator_variable_name(declarator, &file.source) {
                let value =
                    shared && !node_text(declarator, &file.source).contains(['*', '&', '[', '(']);
                objects
                    .entry(name)
                    .or_default()
                    .push(if value { record } else { None });
            }
        }
    });
    let seeds = lines.clone();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "call_expression" || !seeds.contains(&(node.start_position().row + 1)) {
            return;
        }
        let Some(callee) = node.child_by_field_name("function") else {
            return;
        };
        if callee.kind() != "field_expression" {
            return;
        }
        let (Some(receiver), Some(method)) = (
            callee.child_by_field_name("argument"),
            callee.child_by_field_name("field"),
        ) else {
            return;
        };
        if receiver.kind() != "identifier" {
            return;
        }
        let Some(objects) = objects.get(node_text(receiver, &file.source)) else {
            return;
        };
        let [Some(owner)] = objects.as_slice() else {
            return;
        };
        let Some(bodies) = methods.get(&(*owner, node_text(method, &file.source).into())) else {
            return;
        };
        let [body] = bodies.as_slice() else { return };
        let mut repeated = false;
        let mut pending = vec![*body];
        while let Some(node) = pending.pop() {
            if matches!(
                node.kind(),
                "lambda_expression"
                    | "function_definition"
                    | "class_specifier"
                    | "struct_specifier"
            ) {
                continue;
            }
            repeated |= matches!(
                node.kind(),
                "for_statement" | "for_range_loop" | "while_statement" | "do_statement"
            );
            let mut cursor = node.walk();
            pending.extend(node.named_children(&mut cursor));
        }
        if !repeated {
            return;
        }
        lines.extend((body.start_position().row + 1)..=(body.end_position().row + 1));
        for line in (body.start_position().row + 1)..=(body.end_position().row + 1) {
            if !seeds.contains(&line) {
                paths.entry(line).or_insert_with(|| {
                    vec![
                        format!("{}:{}", file.path, node.start_position().row + 1),
                        node_text(callee, &file.source).to_owned(),
                    ]
                });
            }
        }
    });
    paths
}

/// A present empty row also matters: it says a lexical name was a parameter,
/// local, declaration, or unevaluated expression, not a member access.
pub(super) fn collect(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    fallback_variables: &HashMap<String, Vec<usize>>,
    initialization: &[super::super::initialization::FreshInitializationRange],
) -> HashMap<usize, Vec<SyntaxAccess>> {
    let Some(tree) = &file.tree else {
        return HashMap::new();
    };
    let mut bindings: HashMap<String, Vec<Binding>> = HashMap::new();
    let mut functions = Vec::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "function_definition" {
            let Some(declarator) = node.child_by_field_name("declarator") else {
                return;
            };
            let name = function_definition_name(node, file).unwrap_or_default();
            let owner = function_owner(node, file, index);
            let destructor = node_text(declarator, &file.source)
                .split('(')
                .next()
                .is_some_and(|name| name.contains('~'));
            let constructor = !destructor
                && owner.is_some_and(|owner| is_record_constructor(&name, index.record(owner)));
            functions.push(Function {
                begin: node.start_byte(),
                end: node.end_byte(),
                name,
                owner,
                constructor_unpublished_until: constructor
                    .then(|| constructor_publication_boundary(node, file, index, owner)),
            });
        }
        if !matches!(
            node.kind(),
            "declaration" | "parameter_declaration" | "optional_parameter_declaration"
        ) {
            return;
        }
        let scope = binding_scope(node);
        let type_text = node
            .child_by_field_name("type")
            .map(|ty| node_text(ty, &file.source))
            .unwrap_or("");
        let mut records = if type_text.contains("::") && !type_text.contains(['<', '>', '(', ')']) {
            // A qualified type names one declaration, not a bag of tokens.
            // In particular Missing::State must not resolve to A::State.
            let qualified = type_text.split_whitespace().collect::<String>();
            let short = qualified.rsplit("::").next().unwrap_or("");
            index
                .record_indices_for_name(short)
                .into_iter()
                .flatten()
                .copied()
                .filter(|candidate| {
                    index
                        .record(*candidate)
                        .qualified_name
                        .trim_start_matches("::")
                        == qualified.trim_start_matches("::")
                })
                .collect::<HashSet<_>>()
        } else {
            identifier_tokens(type_text)
                .filter_map(|name| index.unambiguous_record_index(name, &file.path))
                .collect::<HashSet<_>>()
        };
        if records.is_empty() && type_text == "auto" {
            let declaration = node_text(node, &file.source);
            if declaration.contains("make_shared<") || declaration.contains("make_unique<") {
                records = identifier_tokens(declaration)
                    .filter_map(|name| index.unambiguous_record_index(name, &file.path))
                    .collect();
            }
        }
        let record = (records.len() == 1).then(|| *records.iter().next().unwrap());
        let declaration = node_text(node, &file.source);
        let thread_local = identifier_tokens(declaration)
            .any(|token| matches!(token, "thread_local" | "__thread"));
        let static_storage = identifier_tokens(declaration).any(|token| token == "static");
        let callable = enclosing_callable(node);
        let mut cursor = node.walk();
        for declarator in node.children_by_field_name("declarator", &mut cursor) {
            let Some(name) = declarator_variable_name(declarator, &file.source) else {
                continue;
            };
            let declarator_text = node_text(declarator, &file.source);
            let owned_value = record.is_some()
                && !declarator_text.contains(['*', '&'])
                && !type_text.contains(['*', '&'])
                && !type_text.contains("shared_ptr")
                && !type_text.contains("unique_ptr")
                && type_text != "auto";
            let factory_owner = record.is_some()
                && declarator
                    .child_by_field_name("value")
                    .is_some_and(|value| {
                        value.kind() == "call_expression"
                            && value.child_by_field_name("function").is_some_and(|callee| {
                                let callee = node_text(callee, &file.source);
                                callee.starts_with("std::make_shared<")
                                    || callee.starts_with("std::make_unique<")
                            })
                    });
            // Array parameters decay to pointers; references and pointer
            // wrappers also refer to external storage. Only an explicit
            // record value with a plain declarator supplies a private copy.
            let value_parameter = node.kind().contains("parameter")
                && declarator.kind() == "identifier"
                && !type_text.contains(['<', '>'])
                // Copy/move constructors or opaque subobject construction
                // can publish this before entering the callee. Require the
                // source-backed inert aggregate proof across included files.
                && record.is_some_and(|owner| index.inert_value_records.contains(&owner))
                && owned_value;
            let name_byte = declarator.start_byte() + declarator_text.find(&name).unwrap_or(0);
            bindings.entry(name).or_default().push(Binding {
                declaration: node.start_byte(),
                name_byte,
                begin: if node.kind().contains("parameter") {
                    scope.start_byte()
                } else {
                    declarator.start_byte()
                },
                end: scope.end_byte(),
                record,
                callable,
                // TLS of a pointer slot does not imply TLS of its pointee.
                thread_local: thread_local && owned_value,
                value_parameter,
                local_owner: (node.kind() == "declaration" || value_parameter)
                    && callable.is_some()
                    && !thread_local
                    && !static_storage
                    && (owned_value || factory_owner),
            });
        }
    });
    let mut escaping = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "identifier" {
            return;
        }
        let name = node_text(node, &file.source);
        let Some(binding) = binding_at(&bindings, name, node.start_byte()) else {
            return;
        };
        if !(binding.local_owner || binding.thread_local) || node.start_byte() == binding.name_byte
        {
            return;
        }
        if (binding.local_owner && enclosing_callable(node) != binding.callable)
            || inside_error(node)
            || !is_nonescaping_member_use(node, &file.source)
        {
            escaping.insert((binding.declaration, binding.begin));
        }
    });
    let mut by_line: HashMap<usize, Vec<SyntaxAccess>> = HashMap::new();
    let mut fallback_lines = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if matches!(
            node.kind(),
            "comment" | "string_literal" | "raw_string_literal"
        ) {
            for line in node.start_position().row + 1..=node.end_position().row + 1 {
                by_line.entry(line).or_default();
            }
            return;
        }
        let is_field_reference = matches!(node.kind(), "identifier" | "field_identifier")
            || (node.kind() == "type_identifier"
                // tree-sitter classifies the mutex argument in the
                // most-vexing-parse form `lock_guard lock(mutex)` as a
                // type_identifier even though its spelling is the field
                // name. Restrict the expensive ancestry check to nodes that
                // are direct single guard parameters; checking the spelling
                // itself would miss this valid form.
                && node
                    .parent()
                    .is_some_and(|parent| parent.kind() == "parameter_declaration")
                && ambiguous_guard_constructor_argument(node, &file.source));
        if !is_field_reference {
            return;
        }
        let field = node_text(node, &file.source);
        if !index.is_known_field(field) {
            return;
        }
        // A syntax recovery node is not authoritative enough to erase a
        // fallback access; retain the existing may-analysis for that row.
        if node.kind() == "ERROR" || node.is_missing() || inside_error(node) {
            fallback_lines.insert(node.start_position().row + 1);
            return;
        }
        let row = by_line.entry(node.start_position().row + 1).or_default();
        let end = functions.partition_point(|function| function.begin <= node.start_byte());
        let Some(function) = functions[..end]
            .iter()
            .rev()
            .find(|function| node.end_byte() <= function.end)
        else {
            return;
        };
        if is_declaration_or_unevaluated(node)
            && !ambiguous_guard_constructor_argument(node, &file.source)
        {
            return;
        }
        let parent = node.parent();
        let qualified = parent.filter(|parent| {
            parent.kind() == "field_expression" && parent.child_by_field_name("field") == Some(node)
        });
        let (expression, receiver, raw_pointer, record) = if let Some(expression) = qualified {
            let Some(argument) = expression.child_by_field_name("argument") else {
                return;
            };
            let receiver = receiver_identifier(argument, &file.source);
            let record = expression_record(
                argument,
                file,
                index,
                &bindings,
                fallback_variables,
                function.owner,
            );
            if record.is_none() && !matches!(argument.kind(), "identifier" | "this") {
                // Calls, qualified names and recovered complex receivers may
                // still be understood by the existing source frontend. An
                // unsupported syntax query is not proof of no member access.
                fallback_lines.insert(node.start_position().row + 1);
            }
            let pointer = expression
                .child_by_field_name("operator")
                .is_some_and(|operator| node_text(operator, &file.source) == "->");
            (expression, receiver, pointer, record)
        } else {
            // Bare names are members only inside the owner and in the absence
            // of a nearer parameter/local declaration, regardless of its type.
            if binding_at(&bindings, field, node.start_byte()).is_some() {
                return;
            }
            (node, None, false, function.owner)
        };
        let Some(record) = record else { return };
        let Some(info) = index
            .record(record)
            .fields
            .iter()
            .find(|info| info.name == field)
        else {
            return;
        };
        if array_address_only(expression, info, &file.source)
            || address_without_memory_access(expression, info, &file.source)
        {
            return;
        }
        let kind = expression_access_kind(expression, info, &file.source);
        let own_receiver =
            receiver.as_deref().is_none_or(|name| name == "this") && function.owner == Some(record);
        let fresh_unpublished = receiver.as_deref().is_some_and(|name| {
            binding_at(&bindings, name, expression.start_byte()).is_some_and(|binding| {
                initialization
                    .iter()
                    .any(|range| range.contains(name, binding.declaration, expression.start_byte()))
            })
        });
        let receiver_binding = receiver
            .as_deref()
            .and_then(|name| binding_at(&bindings, name, expression.start_byte()));
        let access = SyntaxAccess {
            needs_line_fallback: false,
            record,
            field: field.to_string(),
            kind,
            start_byte: expression.start_byte(),
            atomic: expression_is_atomic(expression, info, &file.source),
            receiver,
            raw_pointer,
            initialization: (own_receiver
                && function
                    .constructor_unpublished_until
                    .is_some_and(|end| expression.start_byte() < end))
                || fresh_unpublished,
            in_record_constructor: function.owner == Some(record)
                && function.constructor_unpublished_until.is_some()
                && enclosing_callable(expression) == Some(function.begin),
            function: Some(function.name.clone()),
            loop_depth: Some(access_loop_depth(expression)),
            thread_local: receiver_binding.is_some_and(|binding| {
                binding.thread_local && !escaping.contains(&(binding.declaration, binding.begin))
            }),
            nonescaping_local: receiver_binding.is_some_and(|binding| {
                binding.local_owner && !escaping.contains(&(binding.declaration, binding.begin))
            }),
            // This is provenance, not a nonescape proof: unknown calls may
            // publish the object. A parallel enclosing body alone cannot
            // certify sharing of this invocation's automatic value.
            automatic_receiver: receiver_binding.is_some_and(|binding| {
                binding.local_owner && binding.callable == enclosing_callable(expression)
            }),
            contiguous_element: false,
            element_index: None,
            element_member_path: Vec::new(),
        };
        if let Some((kind, member_path)) = contiguous_element_access(expression, info, file, index)
        {
            let mut element = access.clone();
            element.kind = kind;
            element.element_member_path = member_path;
            element.contiguous_element = true;
            if receiver_binding.is_some_and(|binding| binding.value_parameter) {
                // Copying the wrapper is not a proof that the referenced
                // allocation is private (span/view/shared buffer wrappers).
                element.nonescaping_local = false;
            }
            element.element_index = contiguous_element_index(expression, &file.source);
            row.push(element);
        }
        row.push(access);
    });
    reference_returns::collect_uses(file, index, &bindings, &functions, &escaping, &mut by_line);
    by_line.retain(|line, accesses| {
        if fallback_lines.contains(line) {
            for access in accesses.iter_mut() {
                access.needs_line_fallback = true;
            }
            !accesses.is_empty()
        } else {
            true
        }
    });
    by_line
}

fn inside_error(mut node: Node<'_>) -> bool {
    while let Some(parent) = node.parent() {
        if parent.kind() == "ERROR" {
            return true;
        }
        if matches!(parent.kind(), "compound_statement" | "function_definition") {
            break;
        }
        node = parent;
    }
    false
}

pub(super) fn binding_scope(mut node: Node<'_>) -> Node<'_> {
    let parameter = node.kind().contains("parameter");
    while let Some(parent) = node.parent() {
        node = parent;
        if matches!(
            node.kind(),
            "function_definition" | "lambda_expression" | "translation_unit"
        ) || (!parameter
            && matches!(
                node.kind(),
                "compound_statement"
                    | "for_statement"
                    | "for_range_loop"
                    | "if_statement"
                    | "namespace_definition"
            ))
        {
            break;
        }
    }
    node
}

fn enclosing_callable(mut node: Node<'_>) -> Option<usize> {
    while let Some(parent) = node.parent() {
        if matches!(parent.kind(), "function_definition" | "lambda_expression") {
            return Some(parent.start_byte());
        }
        node = parent;
    }
    None
}

/// Prove that all value declarations on a storage declaration stay in their
/// owning callable. Unknown calls, references, shadowed names and captures
/// deliberately fail this proof; local syntax alone is not ownership proof.
pub(super) fn storage_declaration_is_private(node: Node<'_>, source: &str) -> bool {
    if node.kind() != "declaration" || inside_error(node) || node.has_error() {
        return false;
    }
    let Some(callable) = enclosing_callable(node) else {
        return false;
    };
    if super::identifier_tokens(node_text(node, source))
        .any(|token| matches!(token, "static" | "extern" | "thread_local" | "__thread"))
    {
        return false;
    }
    let scope = binding_scope(node);
    let mut any = false;
    let mut cursor = node.walk();
    for mut name in node.children_by_field_name("declarator", &mut cursor) {
        any = true;
        while matches!(name.kind(), "init_declarator" | "array_declarator") {
            let Some(inner) = name.child_by_field_name("declarator") else {
                return false;
            };
            name = inner;
        }
        if name.kind() != "identifier" {
            return false;
        }
        let spelling = node_text(name, source);
        let mut escaped = false;
        walk_nodes(scope, &mut |usage| {
            if usage.kind() == "identifier"
                && usage.start_byte() > name.start_byte()
                && node_text(usage, source) == spelling
                && (inside_error(usage)
                    || storage_execution_callable(usage, source) != Some(callable)
                    || storage_use_is_returned(usage)
                    || has_receiver_call(usage)
                    || !is_nonescaping_member_use(usage, source))
            {
                escaped = true;
            }
        });
        if escaped {
            return false;
        }
    }
    any
}

/// A directly invoked lambda executes synchronously in its caller. Merely
/// creating, returning or passing a closure supplies no such guarantee.
/// Nested asynchronous/opaque callbacks still introduce a distinct domain.
fn storage_execution_callable(mut node: Node<'_>, source: &str) -> Option<usize> {
    while let Some(parent) = node.parent() {
        if parent.kind() == "lambda_expression" {
            if super::identifier_tokens(node_text(parent, source))
                .any(|word| matches!(word, "co_await" | "co_yield" | "co_return"))
            {
                return Some(parent.start_byte());
            }
            let mut target = parent;
            while let Some(wrapper) = target.parent() {
                if wrapper.kind() != "parenthesized_expression" {
                    break;
                }
                target = wrapper;
            }
            if !target.parent().is_some_and(|call| {
                call.kind() == "call_expression"
                    && call.child_by_field_name("function") == Some(target)
            }) {
                return Some(parent.start_byte());
            }
        } else if parent.kind() == "function_definition" {
            return Some(parent.start_byte());
        }
        node = parent;
    }
    None
}

fn storage_use_is_returned(mut node: Node<'_>) -> bool {
    while let Some(parent) = node.parent() {
        if parent.kind() == "return_statement" {
            // Without the result type/binding, even a scalar member expression
            // may return a reference (including decltype(auto)).
            return true;
        }
        if matches!(parent.kind(), "expression_statement" | "declaration") {
            return false;
        }
        node = parent;
    }
    false
}

fn has_receiver_call(mut node: Node<'_>) -> bool {
    while let Some(parent) = node.parent() {
        if parent.kind() == "call_expression" {
            return true;
        }
        if matches!(
            parent.kind(),
            "expression_statement" | "declaration" | "return_statement"
        ) {
            break;
        }
        node = parent;
    }
    false
}

fn access_loop_depth(mut node: Node<'_>) -> usize {
    let mut depth = 0;
    while let Some(parent) = node.parent() {
        if matches!(parent.kind(), "lambda_expression" | "function_definition") {
            break;
        }
        if matches!(
            parent.kind(),
            "for_statement" | "for_range_loop" | "while_statement" | "do_statement"
        ) {
            // A for initializer/range expression is evaluated once per loop
            // entry; only the body, condition and increment recur here.
            let once = parent
                .child_by_field_name("initializer")
                .is_some_and(|n| n.id() == node.id())
                || (parent.kind() == "for_range_loop"
                    && parent
                        .child_by_field_name("right")
                        .is_some_and(|n| n.id() == node.id()));
            if !once {
                depth += 1;
            }
        }
        node = parent;
    }
    depth
}

/// Narrow, source-backed construction proof. A local array of objects whose
/// constructors publish `this` is not private merely because its name never
/// escapes. Opaque/member construction remains unresolved.
pub(super) fn record_construction_is_inert(
    file: &ParsedCppFile,
    record: &super::CppStructInfo,
) -> bool {
    if record.file != file.path || record.has_base_classes || record.fields.is_empty() {
        return false;
    }
    if record.fields.iter().any(|field| {
        !matches!(
            field.ty_str.trim(),
            "bool"
                | "char"
                | "int"
                | "unsigned"
                | "unsigned int"
                | "long"
                | "unsigned long"
                | "long long"
                | "unsigned long long"
                | "short"
                | "unsigned short"
                | "float"
                | "double"
        )
    }) {
        return false;
    }
    let Some(tree) = &file.tree else {
        return false;
    };
    let mut inert = false;
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(node.kind(), "struct_specifier" | "class_specifier")
            || node.start_position().row + 1 != record.line
            || node.has_error()
            || node
                .child_by_field_name("name")
                .is_none_or(|name| node_text(name, &file.source) != record.name)
        {
            return;
        }
        let Some(body) = node.child_by_field_name("body") else {
            return;
        };
        let mut has_special_member = false;
        walk_nodes(body, &mut |part| {
            if part.kind() == "function_declarator"
                && let Some(name) = part.child_by_field_name("declarator")
            {
                let name = node_text(name, &file.source).trim();
                if name == record.name || name == format!("~{}", record.name) {
                    has_special_member = true;
                }
            }
        });
        if has_special_member {
            return;
        }
        inert = true;
        let mut cursor = body.walk();
        for field in body.named_children(&mut cursor) {
            if matches!(field.kind(), "field_declaration" | "declaration") {
                walk_nodes(field, &mut |part| {
                    if matches!(
                        part.kind(),
                        "call_expression" | "new_expression" | "lambda_expression" | "this"
                    ) {
                        inert = false;
                    }
                    if part.kind() == "init_declarator"
                        && part.child_by_field_name("value").is_some_and(|value| {
                            !matches!(
                                value.kind(),
                                "number_literal" | "true" | "false" | "char_literal"
                            )
                        })
                    {
                        inert = false;
                    }
                });
                let mut field_cursor = field.walk();
                for value in field.children_by_field_name("default_value", &mut field_cursor) {
                    if !matches!(
                        value.kind(),
                        "number_literal" | "true" | "false" | "char_literal"
                    ) {
                        inert = false;
                    }
                }
            }
        }
    });
    inert
}

fn is_nonescaping_member_use(mut node: Node<'_>, source: &str) -> bool {
    let mut member = false;
    while let Some(parent) = node.parent() {
        match parent.kind() {
            "field_expression" if parent.child_by_field_name("argument") == Some(node) => {
                member = true;
            }
            "parenthesized_expression" | "subscript_expression" => {}
            "pointer_expression" => {
                if node_text(parent, source).trim_start().starts_with('&') {
                    return false;
                }
            }
            "call_expression" if parent.child_by_field_name("function") == Some(node) => {
                let method = node
                    .child_by_field_name("field")
                    .map(|field| node_text(field, source))
                    .unwrap_or("");
                if !member
                    || (mutation_kind_around("", &format!(".{method}(")).is_none()
                        && method != "load")
                {
                    return false;
                }
            }
            "assignment_expression"
            | "update_expression"
            | "binary_expression"
            | "conditional_expression"
            | "unary_expression" => {
                if !member {
                    return false;
                }
            }
            "expression_statement" | "return_statement" | "condition_clause" => return member,
            // Passing an object/field to an unknown call, storing an alias,
            // or entering an unsupported syntax form is not nonescape proof.
            _ => return false,
        }
        node = parent;
    }
    false
}

fn binding_at<'a>(
    bindings: &'a HashMap<String, Vec<Binding>>,
    name: &str,
    offset: usize,
) -> Option<&'a Binding> {
    bindings
        .get(name)?
        .iter()
        .filter(|binding| binding.begin <= offset && offset < binding.end)
        .max_by_key(|binding| binding.begin)
}

pub(super) fn function_owner(
    node: Node<'_>,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
) -> Option<usize> {
    let mut ancestor = node.parent();
    while let Some(parent) = ancestor {
        if matches!(parent.kind(), "class_specifier" | "struct_specifier") {
            let name = node_text(parent.child_by_field_name("name")?, &file.source);
            // Bind the enclosing declaration, not a same-named record from
            // another scope. An empty/uncollected owner must not fall back to
            // the type of an unrelated parameter merely sharing its name.
            let mut scopes = vec![name.to_string()];
            let mut outer = parent.parent();
            while let Some(scope) = outer {
                if matches!(
                    scope.kind(),
                    "namespace_definition" | "class_specifier" | "struct_specifier"
                ) {
                    if let Some(scope_name) = scope.child_by_field_name("name") {
                        scopes.push(node_text(scope_name, &file.source).to_string());
                    } else if scope.kind() != "namespace_definition" {
                        return None;
                    }
                    // Anonymous namespaces have no textual qualifier in the
                    // layout identity. File + declaration line still bind the
                    // exact local record; anonymity does not erase its body.
                }
                outer = scope.parent();
            }
            scopes.reverse();
            let qualified = scopes.join("::");
            let mut matches =
                index
                    .record_indices_for_name(name)?
                    .iter()
                    .copied()
                    .filter(|candidate| {
                        let record = index.record(*candidate);
                        record.file == file.path
                            && record.line == parent.start_position().row + 1
                            && record.qualified_name.trim_start_matches("::")
                                == qualified.trim_start_matches("::")
                    });
            let owner = matches.next()?;
            return matches.next().is_none().then_some(owner);
        }
        ancestor = parent.parent();
    }
    let mut declarator = node.child_by_field_name("declarator")?;
    while let Some(inner) = declarator.child_by_field_name("declarator") {
        declarator = inner;
    }
    // Outer::Nested::method belongs to Nested. Parameter types and template
    // arguments are not owning records; preserve the unambiguous namespace /
    // same-file fallback only among the actual qualification components.
    let qualified_name = without_template_arguments(node_text(declarator, &file.source));
    let (scope, _) = qualified_name.rsplit_once("::")?;
    let compact_scope = scope.split_whitespace().collect::<String>();
    for name in identifier_tokens(scope)
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
    {
        let Some(candidates) = index.record_indices_for_name(name) else {
            continue;
        };
        let mut exact = candidates.iter().copied().filter(|candidate| {
            index
                .record(*candidate)
                .qualified_name
                .trim_start_matches("::")
                == compact_scope.trim_start_matches("::")
        });
        if let Some(candidate) = exact.next()
            && exact.next().is_none()
        {
            return Some(candidate);
        }
        // An ambiguous inner record must not fall through to an outer class
        // that happens to have a member with the same spelling.
        return index.unambiguous_record_index(name, &file.path);
    }
    None
}

fn constructor_publication_boundary(
    node: Node<'_>,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    owner: Option<usize>,
) -> usize {
    let mut boundary = node.end_byte();
    let mut member_methods = HashSet::new();
    let mut ancestor = node.parent();
    while let Some(parent) = ancestor {
        if matches!(parent.kind(), "class_specifier" | "struct_specifier") {
            walk_nodes(parent, &mut |member| {
                if member.kind() == "function_declarator"
                    && let Some(name) = callable_name(node_text(member, &file.source))
                {
                    member_methods.insert(name);
                }
            });
            break;
        }
        ancestor = parent.parent();
    }
    walk_nodes(node, &mut |child| {
        // A jump may revisit a lexical prefix after publication. Until CFG
        // recovery handles it, do not infer an unpublished prefix at all.
        if matches!(child.kind(), "goto_statement" | "labeled_statement") {
            boundary = node.start_byte();
        }
        let mut can_publish = false;
        // A capture default can publish the implicit receiver without an
        // explicit `this` token. Proving a lambda synchronous is a separate
        // analysis, so do not use constructor-only exclusion in this case.
        can_publish |= child.kind() == "lambda_expression";
        if child.kind() == "this" {
            let direct_member = child.parent().is_some_and(|parent| {
                parent.kind() == "field_expression"
                    && parent.child_by_field_name("argument") == Some(child)
            });
            can_publish |= !direct_member;
        }
        if child.kind() == "call_expression"
            && let Some(callee) = child.child_by_field_name("function")
        {
            let name = node_text(callee, &file.source);
            can_publish |= callee.kind() == "identifier"
                && (member_methods.contains(name)
                    || owner.is_some_and(|owner| {
                        index
                            .record(owner)
                            .public_methods
                            .iter()
                            .any(|method| method == name)
                    }));
            can_publish |= callee.kind() == "field_expression"
                && callee
                    .child_by_field_name("argument")
                    .is_some_and(|argument| node_text(argument, &file.source) == "this");
        }
        if child.kind() == "pointer_expression"
            && node_text(child, &file.source).trim_start().starts_with('&')
        {
            can_publish |=
                owner.is_some_and(|owner| {
                    index.record(owner).fields.iter().any(|field| {
                        contains_identifier(node_text(child, &file.source), &field.name)
                    })
                });
        }
        if can_publish {
            let mut begin = child.start_byte();
            let mut ancestor = child.parent();
            while let Some(scope) = ancestor {
                if scope == node {
                    break;
                }
                // The next iteration can execute before the publication's
                // lexical position while the object is already shared.
                if matches!(
                    scope.kind(),
                    "for_statement" | "for_range_loop" | "while_statement" | "do_statement"
                ) {
                    begin = scope.start_byte();
                }
                ancestor = scope.parent();
            }
            boundary = boundary.min(begin);
        }
    });
    boundary
}

fn receiver_identifier(mut node: Node<'_>, source: &str) -> Option<String> {
    loop {
        match node.kind() {
            "identifier" | "this" => return Some(node_text(node, source).to_string()),
            "subscript_expression" => node = node.child_by_field_name("argument")?,
            "parenthesized_expression" | "pointer_expression" => node = node.named_child(0)?,
            _ => return None,
        }
    }
}

fn expression_record(
    node: Node<'_>,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    bindings: &HashMap<String, Vec<Binding>>,
    fallback: &HashMap<String, Vec<usize>>,
    owner: Option<usize>,
) -> Option<usize> {
    match node.kind() {
        "this" => owner,
        "identifier" => {
            let name = node_text(node, &file.source);
            if let Some(binding) = binding_at(bindings, name, node.start_byte()) {
                return binding.record;
            }
            if let Some(owner) = owner
                && let Some(field) = index
                    .record(owner)
                    .fields
                    .iter()
                    .find(|field| field.name == name)
            {
                return type_record_in_scope(&field.ty_str, file, index, Some(owner));
            }
            let candidates = fallback.get(name)?;
            (candidates.len() == 1).then(|| candidates[0])
        }
        "subscript_expression" => expression_record(
            node.child_by_field_name("argument")?,
            file,
            index,
            bindings,
            fallback,
            owner,
        ),
        "parenthesized_expression" | "pointer_expression" => {
            expression_record(node.named_child(0)?, file, index, bindings, fallback, owner)
        }
        "field_expression" => {
            let parent = expression_record(
                node.child_by_field_name("argument")?,
                file,
                index,
                bindings,
                fallback,
                owner,
            )?;
            let name = node_text(node.child_by_field_name("field")?, &file.source);
            let field = index
                .record(parent)
                .fields
                .iter()
                .find(|field| field.name == name)?;
            type_record_in_scope(&field.ty_str, file, index, Some(parent))
        }
        "call_expression" => {
            let function = node.child_by_field_name("function")?;
            if function.kind() != "field_expression"
                || function
                    .child_by_field_name("field")
                    .is_none_or(|field| node_text(field, &file.source) != "at")
            {
                return None;
            }
            expression_record(
                function.child_by_field_name("argument")?,
                file,
                index,
                bindings,
                fallback,
                owner,
            )
        }
        _ => None,
    }
}

fn type_record(ty: &str, file: &ParsedCppFile, index: &EvidenceIndex<'_>) -> Option<usize> {
    type_record_in_scope(ty, file, index, None)
}

/// Resolve a member's value type in the namespace of its owning record before
/// falling back to the existing file/path disambiguation. A short field type
/// can be ambiguous project-wide (for example several `Board` records), but
/// an owner such as `StockDory::SearchTask` supplies a real lexical namespace
/// without guessing across unrelated namespaces.
pub(super) fn type_record_in_scope(
    ty: &str,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    scope: Option<usize>,
) -> Option<usize> {
    let without_templates = without_template_arguments(ty);
    let base = without_templates
        .split(['*', '&', '['])
        .next()
        .unwrap_or(ty)
        .trim()
        .trim_start_matches("const ")
        .trim_start_matches("volatile ")
        .trim_start_matches("struct ")
        .trim_start_matches("class ")
        .trim();
    let compact = base.split_whitespace().collect::<String>();
    let short = compact.rsplit("::").next().unwrap_or(compact.as_str());
    let candidates = index.record_indices_for_name(short)?;
    if compact.contains("::") {
        let qualified = compact.trim_start_matches("::");
        let matches = candidates
            .iter()
            .copied()
            .filter(|candidate| {
                index.records[*candidate]
                    .qualified_name
                    .trim_start_matches("::")
                    == qualified
            })
            .collect::<Vec<_>>();
        return (matches.len() == 1).then(|| matches[0]);
    }
    if let Some(scope) = scope {
        let qualified_scope = index.records[scope].qualified_name.trim_start_matches("::");
        if let Some((namespace, _)) = qualified_scope.rsplit_once("::") {
            let matches = candidates
                .iter()
                .copied()
                .filter(|candidate| {
                    index.records[*candidate]
                        .qualified_name
                        .trim_start_matches("::")
                        .rsplit_once("::")
                        .is_some_and(|(name, _)| name == namespace)
                })
                .collect::<Vec<_>>();
            if matches.len() == 1 {
                return matches.first().copied();
            }
        }
    }
    let matches = candidates
        .iter()
        .copied()
        .filter(|candidate| index.records[*candidate].file == file.path)
        .collect::<Vec<_>>();
    if matches.len() == 1 {
        return matches.first().copied();
    }
    index.unambiguous_record_index(short, &file.path)
}

fn is_declaration_or_unevaluated(mut node: Node<'_>) -> bool {
    let original = node;
    if node.parent().is_some_and(|parent| {
        parent.kind() == "field_expression"
            && parent.child_by_field_name("field") == Some(node)
            && parent.parent().is_some_and(|call| {
                call.kind() == "call_expression"
                    && call.child_by_field_name("function") == Some(parent)
            })
    }) {
        return true;
    }
    while let Some(parent) = node.parent() {
        match parent.kind() {
            "sizeof_expression" | "alignof_expression" | "decltype" | "comment" => return true,
            "parameter_declaration" | "optional_parameter_declaration" | "field_declaration" => {
                return true;
            }
            "init_declarator" if parent.child_by_field_name("declarator") == Some(node) => {
                return true;
            }
            "declaration"
                if parent.child_by_field_name("type") == Some(node)
                    || (parent.child_by_field_name("declarator") == Some(node)
                        && node.kind() != "init_declarator") =>
            {
                return true;
            }
            "call_expression"
                if node == original && parent.child_by_field_name("function") == Some(node) =>
            {
                return true;
            }
            "function_declarator" | "type_descriptor" | "qualified_identifier" => return true,
            "expression_statement" | "compound_statement" | "function_definition" => return false,
            _ => {}
        }
        node = parent;
    }
    false
}

fn expression_is_atomic(
    mut node: Node<'_>,
    field: &super::super::types::CppFieldInfo,
    source: &str,
) -> bool {
    let outer = without_template_arguments(&field.ty_str);
    if outer.contains('&') {
        return false;
    }
    if field.is_atomic && !outer.contains('*') {
        return true;
    }
    let mut address = false;
    while let Some(parent) = node.parent() {
        match parent.kind() {
            "parenthesized_expression" => node = parent,
            "pointer_expression" if node_text(parent, source).trim_start().starts_with('&') => {
                address = true;
                node = parent;
            }
            "argument_list" => {
                // Only the atomic object's argument supplies atomic-state
                // evidence, not the desired value, output or expected value.
                return (address || !outer.contains('*'))
                    && parent.named_child(0) == Some(node)
                    && parent
                        .parent()
                        .and_then(|call| call.child_by_field_name("function"))
                        .is_some_and(|callee| {
                            explicit_atomic_argument_access(node_text(callee, source), 0).is_some()
                        });
            }
            _ => return false,
        }
    }
    false
}

fn expression_access_kind(
    mut node: Node<'_>,
    field: &super::super::types::CppFieldInfo,
    source: &str,
) -> CppAccessKind {
    // Assigning through a reference changes its referent, never the reference
    // member's own binding/storage. Reading that binding may still conflict
    // with a real write to another inline field.
    if without_template_arguments(&field.ty_str).contains('&') {
        return CppAccessKind::Read;
    }
    if field.is_hot_sync
        && !without_template_arguments(&field.ty_str).contains('*')
        && standard_guard_acquires_argument(node, source)
    {
        return CppAccessKind::ReadModifyWrite;
    }
    let mut indexed_layers = 0;
    let mut takes_address = false;
    while let Some(parent) = node.parent() {
        let indexed_storage = field_indexed_storage(field, indexed_layers);
        match parent.kind() {
            "assignment_expression" => {
                if parent.child_by_field_name("left") != Some(node) {
                    return CppAccessKind::Read;
                }
                let operator = parent
                    .child_by_field_name("operator")
                    .map(|op| node_text(op, source))
                    .unwrap_or("=");
                return if operator == "="
                    && !parent
                        .child_by_field_name("right")
                        .is_some_and(|right| expression_depends_on_lvalue(right, node, source, 4))
                {
                    CppAccessKind::Write
                } else {
                    CppAccessKind::ReadModifyWrite
                };
            }
            "update_expression" => return CppAccessKind::ReadModifyWrite,
            "subscript_expression" if parent.child_by_field_name("argument") == Some(node) => {
                match indexed_storage {
                    IndexedStorage::Indirect => return CppAccessKind::Read,
                    // Non-const map::operator[] can insert even if the result
                    // is only read or dereferenced. That may mutate the inline
                    // container control block, unlike vector::operator[].
                    IndexedStorage::Associative => return CppAccessKind::ReadModifyWrite,
                    IndexedStorage::Inline => indexed_layers += 1,
                }
                node = parent;
            }
            "field_expression" if parent.child_by_field_name("argument") == Some(node) => {
                let op = parent
                    .child_by_field_name("operator")
                    .map(|op| node_text(op, source))
                    .unwrap_or(".");
                if op == "->" {
                    return CppAccessKind::Read;
                }
                if let Some(call) = parent.parent().filter(|call| {
                    call.kind() == "call_expression"
                        && call.child_by_field_name("function") == Some(parent)
                }) {
                    let method = parent
                        .child_by_field_name("field")
                        .map(|name| node_text(name, source))
                        .unwrap_or("");
                    if method == "store"
                        && field.is_atomic
                        && call
                            .child_by_field_name("arguments")
                            .and_then(|args| args.named_child(0))
                            .is_some_and(|value| {
                                expression_depends_on_lvalue(value, node, source, 4)
                            })
                    {
                        return CppAccessKind::ReadModifyWrite;
                    }
                    if indexed_layers == 0
                        && let Some(kind) =
                            smart_pointer_holder_method_access(&field.ty_str, method)
                    {
                        return kind;
                    }
                    let suffix = format!(".{method}(");
                    return mutation_kind_around("", &suffix).unwrap_or_else(|| {
                        // Unknown methods retain read evidence. Their mutations
                        // can be supplied by the optional compiler frontend.
                        let _ = call;
                        CppAccessKind::Read
                    });
                }
                if matches!(indexed_storage, IndexedStorage::Indirect) {
                    return CppAccessKind::Read;
                }
                node = parent;
            }
            "pointer_expression" => {
                if node_text(parent, source).trim_start().starts_with('&') {
                    takes_address = true;
                    node = parent;
                } else {
                    return CppAccessKind::Read;
                }
            }
            "parenthesized_expression" => node = parent,
            "argument_list" => {
                // Passing a pointer member to a C atomic/lock API mutates its
                // pointee, not the pointer slot. Passing &member is different.
                if !takes_address && without_template_arguments(&field.ty_str).contains('*') {
                    return CppAccessKind::Read;
                }
                if let Some(call) = parent.parent()
                    && let Some(callee) = call.child_by_field_name("function")
                {
                    let name = node_text(callee, source);
                    let mut cursor = parent.walk();
                    if let Some(argument) = parent
                        .named_children(&mut cursor)
                        .position(|arg| arg == node)
                        && let Some(kind) = explicit_atomic_argument_access(name, argument)
                    {
                        return kind;
                    }
                    if parent.named_child(0) == Some(node) {
                        if let Some(kind) =
                            macro_field_mutation(node_text(call, source), &field.name)
                        {
                            return kind;
                        }
                        if explicit_lock_operation(call, source).is_some() {
                            return CppAccessKind::ReadModifyWrite;
                        }
                    }
                }
                return CppAccessKind::Read;
            }
            _ => return CppAccessKind::Read,
        }
    }
    CppAccessKind::Read
}

/// A directly constructed standard guard acquires its mutex argument. Tags
/// such as defer_lock/adopt_lock and wrapper calls need different effects and
/// are not inferred here. Reading a pointer to a mutex is not a slot RMW.
fn standard_guard_acquires_argument(mut node: Node<'_>, source: &str) -> bool {
    if ambiguous_guard_constructor_argument(node, source) {
        return true;
    }
    while let Some(parent) = node.parent() {
        if parent.kind() == "parenthesized_expression" {
            node = parent;
            continue;
        }
        if !matches!(parent.kind(), "argument_list" | "initializer_list")
            || parent.named_child_count() != 1
            || parent.named_child(0) != Some(node)
        {
            return false;
        }
        let Some(init) = parent.parent().filter(|n| n.kind() == "init_declarator") else {
            return false;
        };
        let Some(declaration) = init.parent().filter(|n| n.kind() == "declaration") else {
            return false;
        };
        let Some(ty) = declaration.child_by_field_name("type") else {
            return false;
        };
        return standard_guard_type(node_text(ty, source));
    }
    false
}

fn standard_guard_type(ty: &str) -> bool {
    // Jolt and similar code commonly import these standard guard types with
    // `using std::lock_guard;`. The unqualified forms are accepted here,
    // while qualified non-standard namespaces remain conservative.
    matches!(
        without_template_arguments(ty).trim(),
        "std::lock_guard"
            | "std::unique_lock"
            | "std::scoped_lock"
            | "std::shared_lock"
            | "lock_guard"
            | "unique_lock"
            | "scoped_lock"
            | "shared_lock"
    )
}

/// Tree-sitter parses `lock_guard lock(member);` as a function declarator
/// (the C++ most-vexing-parse shape), so the member is hidden in a single
/// parameter declaration instead of an argument list. Recognize that shape
/// only for a standard guard type with exactly one argument; multi-argument
/// defer/adopt forms remain unresolved.
fn ambiguous_guard_constructor_argument(node: Node<'_>, source: &str) -> bool {
    let mut current = node;
    while let Some(parent) = current.parent() {
        if parent.kind() == "parameter_declaration" {
            let Some(parameters) = parent.parent().filter(|n| n.kind() == "parameter_list") else {
                return false;
            };
            if parameters.named_child_count() != 1
                || !parameters
                    .named_children(&mut parameters.walk())
                    .any(|parameter| parameter == parent)
            {
                return false;
            }
            let Some(function) = parameters
                .parent()
                .filter(|n| n.kind() == "function_declarator")
            else {
                return false;
            };
            let Some(declaration) = function.parent().and_then(|parent| {
                if parent.kind() == "declaration" {
                    Some(parent)
                } else if parent.kind() == "init_declarator" {
                    parent
                        .parent()
                        .filter(|grandparent| grandparent.kind() == "declaration")
                } else {
                    None
                }
            }) else {
                return false;
            };
            return declaration
                .child_by_field_name("type")
                .is_some_and(|ty| standard_guard_type(node_text(ty, source)));
        }
        if matches!(
            parent.kind(),
            "expression_statement" | "compound_statement" | "function_definition"
        ) {
            return false;
        }
        current = parent;
    }
    false
}

/// The weak promotion RMW targets the separately allocated control block,
/// never the weak_ptr holder. Conversely reset/swap really modify the holder.
/// Match the outer standard-library type, not a name inside template arguments.
fn smart_pointer_holder_method_access(ty: &str, method: &str) -> Option<CppAccessKind> {
    let head = ty.split('<').next()?.trim();
    let head = head.strip_prefix("const ").unwrap_or(head).trim();
    if !matches!(
        head,
        "std::weak_ptr" | "std::shared_ptr" | "std::unique_ptr"
    ) || without_template_arguments(ty).contains(['*', '&', '['])
    {
        return None;
    }
    match method {
        "lock" if head == "std::weak_ptr" => Some(CppAccessKind::Read),
        "reset" | "swap" => Some(CppAccessKind::ReadModifyWrite),
        "release" if head == "std::unique_ptr" => Some(CppAccessKind::ReadModifyWrite),
        _ => None,
    }
}

/// A plain assignment can consume the old value (x = x + delta). An earlier
/// condition mentioning x is not such a data dependency. Keep receiver paths
/// intact: a.x = b.x must not become an old-value update of a.x.
fn expression_reads_lvalue(rhs: Node<'_>, lhs: Node<'_>, source: &str) -> bool {
    let target = node_text(lhs, source).replace(char::is_whitespace, "");
    let mut reads = false;
    walk_nodes(rhs, &mut |occurrence| {
        if !matches!(
            occurrence.kind(),
            "identifier" | "field_expression" | "subscript_expression"
        ) || node_text(occurrence, source).replace(char::is_whitespace, "") != target
            || is_declaration_or_unevaluated(occurrence)
        {
            return;
        }
        let mut ancestor = occurrence;
        while ancestor != rhs {
            let Some(parent) = ancestor.parent() else {
                return;
            };
            if (parent.kind() == "assignment_expression"
                && parent.child_by_field_name("left") == Some(ancestor)
                && parent
                    .child_by_field_name("operator")
                    .is_some_and(|op| node_text(op, source) == "="))
                || (parent.kind() == "pointer_expression"
                    && node_text(parent, source).trim_start().starts_with('&'))
            {
                return;
            }
            if matches!(
                parent.kind(),
                "lambda_expression" | "sizeof_expression" | "alignof_expression" | "decltype"
            ) {
                return;
            }
            ancestor = parent;
        }
        // A bare field token inside a different receiver expression is not
        // the bare lhs. This also avoids matching other.x against x.
        if occurrence.parent().is_some_and(|parent| {
            parent.kind() == "field_expression"
                && parent.child_by_field_name("field") == Some(occurrence)
        }) {
            return;
        }
        reads = true;
    });
    reads
}

/// Bounded local def-use recovery for load / compute / store idioms. A local
/// must have a dominating initializer and no intervening overwrite or escape.
/// This is a value dependency, not a claim of a single atomic RMW instruction.
fn expression_depends_on_lvalue(rhs: Node<'_>, lhs: Node<'_>, source: &str, depth: usize) -> bool {
    if expression_reads_lvalue(rhs, lhs, source) {
        return true;
    }
    if depth == 0 {
        return false;
    }
    let mut dependent = false;
    walk_nodes(rhs, &mut |use_node| {
        if dependent || use_node.kind() != "identifier" || is_declaration_or_unevaluated(use_node) {
            return;
        }
        let name = node_text(use_node, source);
        let mut scope = use_node.parent();
        while let Some(block) = scope {
            if matches!(block.kind(), "lambda_expression" | "function_definition") {
                break;
            }
            if block.kind() == "compound_statement" {
                let mut declaration = None;
                for statement in block.named_children(&mut block.walk()) {
                    if statement.end_byte() > use_node.start_byte()
                        || statement.kind() != "declaration"
                    {
                        continue;
                    }
                    for declarator in
                        statement.children_by_field_name("declarator", &mut statement.walk())
                    {
                        if declarator.kind() == "init_declarator"
                            && declarator
                                .child_by_field_name("declarator")
                                .is_some_and(|n| {
                                    n.kind() == "identifier" && node_text(n, source) == name
                                })
                        {
                            declaration = Some(declarator);
                        }
                    }
                }
                if let Some(declaration) = declaration {
                    let Some(value) = declaration.child_by_field_name("value") else {
                        return;
                    };
                    let mut killed = false;
                    walk_nodes(block, &mut |node| {
                        if node.start_byte() < declaration.end_byte()
                            || node.end_byte() > rhs.start_byte()
                        {
                            return;
                        }
                        if node.kind() == "assignment_expression"
                            && node
                                .child_by_field_name("left")
                                .is_some_and(|n| node_text(n, source) == name)
                            && node
                                .child_by_field_name("operator")
                                .is_some_and(|n| node_text(n, source) == "=")
                        {
                            killed = true;
                        }
                        if node.kind() == "argument_list"
                            && contains_identifier(node_text(node, source), name)
                        {
                            killed = true;
                        }
                        if node.kind() == "init_declarator"
                            && node
                                .child_by_field_name("declarator")
                                .is_some_and(|n| node_text(n, source).contains('&'))
                            && node.child_by_field_name("value").is_some_and(|n| {
                                n.kind() != "subscript_expression"
                                    && contains_identifier(node_text(n, source), name)
                            })
                        {
                            killed = true;
                        }
                        if node.kind() == "pointer_expression"
                            && node_text(node, source).trim_start().starts_with('&')
                            && contains_identifier(node_text(node, source), name)
                        {
                            killed = true;
                        }
                    });
                    dependent =
                        !killed && expression_depends_on_lvalue(value, lhs, source, depth - 1);
                    return;
                }
            }
            scope = block.parent();
        }
    });
    dependent
}

fn contiguous_element_index(mut node: Node<'_>, source: &str) -> Option<String> {
    while node
        .parent()
        .is_some_and(|p| p.kind() == "parenthesized_expression")
    {
        node = node.parent()?;
    }
    let parent = node.parent()?;
    let index = if parent.kind() == "subscript_expression"
        && parent.child_by_field_name("argument") == Some(node)
    {
        parent.child_by_field_name("indices")?.named_child(0)?
    } else if parent.kind() == "field_expression"
        && parent.child_by_field_name("argument") == Some(node)
        && parent
            .child_by_field_name("field")
            .is_some_and(|n| node_text(n, source) == "at")
    {
        let arguments = parent.parent()?.child_by_field_name("arguments")?;
        if arguments.named_child_count() != 1 {
            return None;
        }
        arguments.named_child(0)?
    } else {
        return None;
    };
    Some(node_text(index, source).to_string())
}

#[cfg(test)]
pub(super) fn contiguous_element_access_kind(
    node: Node<'_>,
    owner_field: &super::super::types::CppFieldInfo,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
) -> Option<CppAccessKind> {
    contiguous_element_access(node, owner_field, file, index).map(|(kind, _)| kind)
}

fn contiguous_element_access(
    mut node: Node<'_>,
    owner_field: &super::super::types::CppFieldInfo,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
) -> Option<(CppAccessKind, Vec<String>)> {
    if !super::super::types::has_contiguous_elements(owner_field) {
        return None;
    }
    while node
        .parent()
        .is_some_and(|parent| parent.kind() == "parenthesized_expression")
    {
        node = node.parent()?;
    }
    let parent = node.parent()?;
    node = if parent.kind() == "subscript_expression"
        && parent.child_by_field_name("argument") == Some(node)
    {
        parent
    } else if parent.kind() == "field_expression"
        && parent.child_by_field_name("argument") == Some(node)
        && parent
            .child_by_field_name("field")
            .is_some_and(|field| node_text(field, &file.source) == "at")
        && parent
            .parent()
            .is_some_and(|call| call.kind() == "call_expression")
    {
        parent.parent()?
    } else {
        return None;
    };
    let mut element = owner_field.clone();
    element.ty_str = first_template_argument(&owner_field.ty_str)
        .or(owner_field.element_type.as_deref())?
        .to_string();
    element.is_array = false;
    let mut member_path = Vec::new();
    loop {
        let parent = node.parent()?;
        if parent.kind() == "parenthesized_expression" {
            node = parent;
            continue;
        }
        if parent.kind() == "subscript_expression" {
            // Another index may follow a pointer or nested vector. Without a
            // resolved inline-array path it is not the original slot's bytes.
            return None;
        }
        if parent.kind() != "field_expression"
            || parent.child_by_field_name("argument") != Some(node)
        {
            return Some((
                expression_access_kind(node, &element, &file.source),
                member_path,
            ));
        }
        if parent
            .child_by_field_name("operator")
            .is_some_and(|operator| node_text(operator, &file.source) == "->")
        {
            return None;
        }
        if parent.parent().is_some_and(|call| {
            call.kind() == "call_expression" && call.child_by_field_name("function") == Some(parent)
        }) {
            return Some((
                expression_access_kind(node, &element, &file.source),
                member_path,
            ));
        }
        let member = node_text(parent.child_by_field_name("field")?, &file.source);
        let record = type_record(&element.ty_str, file, index)?;
        element = index
            .record(record)
            .fields
            .iter()
            .find(|field| field.name == member)?
            .clone();
        if without_template_arguments(&element.ty_str).contains('&') {
            return None;
        }
        member_path.push(member.to_string());
        node = parent;
    }
}

enum IndexedStorage {
    Inline,
    Indirect,
    Associative,
}

pub(super) fn without_template_arguments(text: &str) -> String {
    let mut result = String::new();
    let mut depth = 0usize;
    for ch in text.chars() {
        match ch {
            '<' => depth += 1,
            '>' if depth > 0 => depth -= 1,
            _ if depth == 0 => result.push(ch),
            _ => {}
        }
    }
    result
}

fn field_indexed_storage(
    field: &super::super::types::CppFieldInfo,
    indexed_layers: usize,
) -> IndexedStorage {
    // A pointer in a template argument is not a pointer to the field itself.
    // Conversely an inline T* slots[N] owns its slots, but not slots[i][j].
    let outer = without_template_arguments(&field.ty_str);
    let compact = outer
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    let pointer_to_array = compact.contains("(*") || compact.contains("(&");
    let inline_dimensions = if field.is_array && !pointer_to_array {
        outer.chars().filter(|ch| *ch == '[').count()
    } else {
        0
    };
    if indexed_layers < inline_dimensions {
        return IndexedStorage::Inline;
    }
    type_indexed_storage(&field.ty_str, indexed_layers - inline_dimensions)
}

fn type_indexed_storage(ty: &str, indexed_layers: usize) -> IndexedStorage {
    let outer = without_template_arguments(ty);
    if outer.contains('*') || outer.contains('&') {
        return IndexedStorage::Indirect;
    }
    let base = ty.split('<').next().unwrap_or(ty);
    match identifier_tokens(base).last() {
        Some("map" | "unordered_map") => IndexedStorage::Associative,
        Some("vector" | "span" | "deque" | "shared_ptr" | "unique_ptr") => IndexedStorage::Indirect,
        Some("array") if indexed_layers > 0 => first_template_argument(ty)
            .map(|element| type_indexed_storage(element, indexed_layers - 1))
            .unwrap_or(IndexedStorage::Inline),
        // basic_string may own its characters inline (small-string storage).
        // Unknown value containers similarly cannot prove an indirection.
        _ => IndexedStorage::Inline,
    }
}

pub(super) fn first_template_argument(ty: &str) -> Option<&str> {
    let begin = ty.find('<')? + 1;
    let mut depth = 0usize;
    for (offset, ch) in ty[begin..].char_indices() {
        match ch {
            ',' | '>' if depth == 0 => return Some(&ty[begin..begin + offset]),
            '<' => depth += 1,
            '>' => depth -= 1,
            _ => {}
        }
    }
    None
}

// Built-in array-to-pointer decay forms an address without loading any array
// element. Restrict this proof to a direct return or ordinary local binding;
// calls, indexing, dereferencing and structured-binding copies need their own
// memory effects and must not be erased by this syntactic rule.
fn array_address_only(
    mut node: Node<'_>,
    field: &super::super::types::CppFieldInfo,
    source: &str,
) -> bool {
    if !field.is_array || field.is_indirect || field.ty_str.contains(['*', '&']) {
        return false;
    }
    while let Some(parent) = node.parent() {
        match parent.kind() {
            "parenthesized_expression" => node = parent,
            "return_statement" => {
                // An unknown return type can invoke a converting constructor
                // that reads the array. Only an explicitly pointer-returning
                // function establishes address formation here.
                let mut scope = parent.parent();
                while let Some(ancestor) = scope {
                    if ancestor.kind() == "lambda_expression" {
                        return false;
                    }
                    if ancestor.kind() == "function_definition" {
                        return ancestor
                            .child_by_field_name("declarator")
                            .is_some_and(|decl| decl.kind() == "pointer_declarator");
                    }
                    scope = ancestor.parent();
                }
                return false;
            }
            "init_declarator" if parent.child_by_field_name("value") == Some(node) => {
                let Some(mut declarator) = parent.child_by_field_name("declarator") else {
                    return false;
                };
                let pointer_binding = declarator.kind() == "pointer_declarator";
                let deduced_binding = declarator.kind() == "identifier"
                    && parent
                        .parent()
                        .and_then(|decl| decl.child_by_field_name("type"))
                        .is_some_and(|ty| node_text(ty, source) == "auto");
                if !pointer_binding && !deduced_binding {
                    return false;
                }
                while matches!(
                    declarator.kind(),
                    "pointer_declarator" | "reference_declarator"
                ) {
                    let Some(inner) = declarator.child_by_field_name("declarator") else {
                        return false;
                    };
                    declarator = inner;
                }
                if declarator.kind() != "identifier" {
                    return false;
                }
                // Until pointer-alias memory effects are recovered at their
                // use sites, a used alias must keep the conservative evidence.
                // A shadowed same-spelled use only makes this proof fail.
                let name = node_text(declarator, source);
                let mut used = false;
                walk_nodes(binding_scope(parent), &mut |usage| {
                    used |= usage.start_byte() >= parent.end_byte()
                        && usage.kind() == "identifier"
                        && node_text(usage, source) == name;
                });
                return !used;
            }
            _ => return false,
        }
    }
    false
}

fn address_without_memory_access(
    mut node: Node<'_>,
    field: &super::super::types::CppFieldInfo,
    source: &str,
) -> bool {
    let mut address = false;
    while let Some(parent) = node.parent() {
        if parent.kind() == "subscript_expression" {
            // &array[index] forms an element address, but computing index
            // still reads it. A pointer base is also loaded to form &ptr[i].
            // Conversely (&field)[0] dereferences the already formed address.
            if parent.child_by_field_name("argument") != Some(node) {
                return false;
            }
            if address {
                // The result is an lvalue again; an outer '&' can form its
                // address without reading it, whereas a value use will read.
                address = false;
            } else if !field.is_array || field.is_indirect || field.ty_str.contains(['*', '&']) {
                return false;
            }
        }
        if parent.kind() == "field_expression"
            && parent.child_by_field_name("argument") == Some(node)
        {
            if address {
                address = false;
            } else if field.is_indirect
                || parent
                    .child_by_field_name("operator")
                    .is_some_and(|op| node_text(op, source) == "->")
            {
                // A pointer receiver must be loaded. Selecting a subfield of
                // an inline value with '.' only projects an lvalue.
                return false;
            }
        }
        if parent.kind() == "pointer_expression"
            && node_text(parent, source).trim_start().starts_with('*')
        {
            if address {
                address = false;
            } else if !field.is_array || field.is_indirect || field.ty_str.contains(['*', '&']) {
                return false;
            }
        }
        if parent.kind() == "pointer_expression"
            && node_text(parent, source).trim_start().starts_with('&')
        {
            address = true;
        }
        if address
            && parent.kind() == "argument_list"
            && let Some(call) = parent.parent()
            && let Some(callee) = call.child_by_field_name("function")
        {
            let mut cursor = parent.walk();
            if let Some(argument) = parent
                .named_children(&mut cursor)
                .position(|arg| arg == node)
                && explicit_atomic_argument_access(node_text(callee, source), argument).is_some()
            {
                return false;
            }
        }
        if parent.kind() == "call_expression" {
            if !address {
                return false;
            }
            // These operations are known to access the addressed storage.
            // Merely passing an address to another call establishes escape,
            // not a load of the field at the address-taking expression.
            return macro_field_mutation(node_text(parent, source), &field.name).is_none()
                && explicit_lock_operation(parent, source).is_none();
        }
        if matches!(
            parent.kind(),
            "expression_statement" | "declaration" | "return_statement" | "compound_statement"
        ) {
            break;
        }
        node = parent;
    }
    address
}
