//! Bounded direct reference getters. Unsupported uses retain the old may facts.
use super::*;

#[derive(Clone)]
struct Getter {
    owner: usize,
    name: String,
    field: String,
    file: String,
    line: usize,
    header_tokens: HashSet<String>,
}

#[derive(Default)]
pub(crate) struct ReferenceReturns {
    getters: HashMap<(usize, String), Getter>,
    names: HashSet<String>,
    blocked: HashSet<(usize, String)>,
}

impl ReferenceReturns {
    pub(crate) fn collect(files: &[ParsedCppFile], index: &EvidenceIndex<'_>) -> Self {
        let mut result = Self::default();
        let mut definitions = HashMap::<(usize, String), usize>::new();
        let mut macro_names = HashSet::new();
        for file in files {
            let Some(tree) = &file.tree else { continue };
            walk_nodes(tree.root_node(), &mut |node| {
                if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                    && let Some(name) = node.child_by_field_name("name")
                {
                    macro_names.insert(node_text(name, &file.source).to_owned());
                }
                if node.kind() != "function_definition" {
                    return;
                }
                let (Some(owner), Some(name)) = (
                    function_owner(node, file, index),
                    function_definition_name(node, file),
                ) else {
                    return;
                };
                let name = name.rsplit("::").next().unwrap_or(&name).to_owned();
                let key = (owner, name.clone());
                *definitions.entry(key.clone()).or_default() += 1;
                let (Some(declarator), Some(body), Some(ty)) = (
                    node.child_by_field_name("declarator"),
                    node.child_by_field_name("body"),
                    node.child_by_field_name("type"),
                ) else {
                    return;
                };
                // Inline, non-virtual, zero-argument getters with one return.
                if node.has_error()
                    || index.record(owner).has_base_classes
                    || node
                        .parent()
                        .is_none_or(|p| p.kind() != "field_declaration_list")
                    || declarator.kind() != "reference_declarator"
                    || node_text(declarator, &file.source).contains("&&")
                    || identifier_tokens(&file.source[node.start_byte()..body.start_byte()])
                        .any(|s| matches!(s, "virtual" | "override" | "volatile" | "static"))
                {
                    return;
                }
                let Some(function) = declarator
                    .named_child(0)
                    .filter(|n| n.kind() == "function_declarator")
                else {
                    return;
                };
                if function
                    .child_by_field_name("parameters")
                    .is_none_or(|p| p.named_child_count() != 0)
                {
                    return;
                }
                let statements = body
                    .named_children(&mut body.walk())
                    .filter(|n| n.kind() != "comment")
                    .collect::<Vec<_>>();
                let [statement] = statements.as_slice() else {
                    return;
                };
                if statement.kind() != "return_statement" {
                    return;
                }
                let Some(mut value) = statement.named_child(0) else {
                    return;
                };
                while value.kind() == "parenthesized_expression" {
                    let Some(inner) = value.named_child(0) else {
                        return;
                    };
                    value = inner;
                }
                let field = match value.kind() {
                    "identifier" => node_text(value, &file.source),
                    "field_expression"
                        if value
                            .child_by_field_name("argument")
                            .is_some_and(|a| a.kind() == "this") =>
                    {
                        let Some(field) = value.child_by_field_name("field") else {
                            return;
                        };
                        node_text(field, &file.source)
                    }
                    _ => return,
                };
                let Some(info) = index.record(owner).fields.iter().find(|f| f.name == field) else {
                    return;
                };
                let canonical = |text: &str| {
                    text.split_whitespace()
                        .filter(|s| *s != "const")
                        .collect::<String>()
                };
                if info.is_static
                    || info.is_array
                    || info.is_indirect
                    || info.ty_str.contains(['*', '&'])
                    || info.ty_str.contains("volatile")
                    || canonical(node_text(ty, &file.source)) != canonical(&info.ty_str)
                {
                    return;
                }
                result.getters.insert(
                    key,
                    Getter {
                        owner,
                        name,
                        field: field.into(),
                        file: file.path.clone(),
                        line: value.start_position().row + 1,
                        header_tokens: identifier_tokens(
                            &file.source[node.start_byte()..body.start_byte()],
                        )
                        .map(str::to_owned)
                        .collect(),
                    },
                );
            });
        }
        result.getters.retain(|key, getter| {
            definitions.get(key) == Some(&1) && getter.header_tokens.is_disjoint(&macro_names)
        });
        result
            .names
            .extend(result.getters.keys().map(|(_, n)| n.clone()));
        if result.names.is_empty() {
            return result;
        }
        // An address, macro, declaration-only overload or otherwise unknown
        // reference to a method name prevents proving all uses understood.
        for file in files {
            let Some(tree) = &file.tree else { continue };
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() == "pointer_expression"
                    && node_text(node, &file.source).trim_start().starts_with('&')
                    && !is_declaration_or_unevaluated(node)
                {
                    for token in identifier_tokens(node_text(node, &file.source)) {
                        result.block_name(token);
                    }
                }
                if node.kind() == "qualified_identifier"
                    && node.parent().is_some_and(|p| {
                        p.kind() == "call_expression"
                            && p.child_by_field_name("function") == Some(node)
                    })
                {
                    for token in identifier_tokens(node_text(node, &file.source)) {
                        result.block_name(token);
                    }
                }
                if node.kind() == "ERROR" {
                    for token in identifier_tokens(node_text(node, &file.source)) {
                        result.block_name(token);
                    }
                }
                if matches!(node.kind(), "preproc_def" | "preproc_function_def") {
                    for token in identifier_tokens(node_text(node, &file.source)) {
                        result.block_name(token);
                    }
                }
                if matches!(node.kind(), "field_declaration" | "declaration")
                    && let Some(name) = function_definition_name(node, file)
                {
                    result.block_name(&name);
                }
                if !matches!(node.kind(), "identifier" | "field_identifier") {
                    return;
                }
                let name = node_text(node, &file.source);
                if !result.names.contains(name) || is_declaration_or_unevaluated(node) {
                    return;
                }
                let Some(parent) = node.parent() else { return };
                let direct_call = parent.kind() == "call_expression"
                    && parent.child_by_field_name("function") == Some(node);
                let member_call = parent.kind() == "field_expression"
                    && parent.child_by_field_name("field") == Some(node)
                    && parent.parent().is_some_and(|p| {
                        p.kind() == "call_expression"
                            && p.child_by_field_name("function") == Some(parent)
                    });
                if !direct_call && !member_call && parent.kind() != "function_declarator" {
                    result.block_name(name);
                }
            });
        }
        result
    }

    fn block_name(&mut self, name: &str) {
        if self.names.contains(name) {
            self.blocked
                .extend(self.getters.keys().filter(|(_, n)| n == name).cloned());
        }
    }

    pub(crate) fn remove_address_only_reads(&self, evidence: &mut [CppEvidenceSet]) {
        for (key, getter) in &self.getters {
            if self.blocked.contains(key) || evidence[getter.owner].truncated_items != 0 {
                continue;
            }
            evidence[getter.owner].items.retain(|item| {
                !(item.file == getter.file
                    && item.line == getter.line
                    && item.function_name.as_deref() == Some(&getter.name)
                    && item.field_name.as_deref() == Some(&getter.field)
                    && item.access_kind == Some(CppAccessKind::Read))
            });
        }
    }
}

pub(super) fn collect_uses(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    bindings: &HashMap<String, Vec<Binding>>,
    functions: &[Function],
    escaping: &HashSet<(usize, usize)>,
    by_line: &mut HashMap<usize, Vec<SyntaxAccess>>,
) {
    if index.reference_returns.borrow().names.is_empty() {
        return;
    }
    let Some(tree) = &file.tree else { return };
    walk_nodes(tree.root_node(), &mut |call| {
        if call.kind() != "call_expression" || is_declaration_or_unevaluated(call) {
            return;
        }
        let Some(callee) = call.child_by_field_name("function") else {
            return;
        };
        let member = callee.kind() == "field_expression";
        let name_node = if member {
            callee.child_by_field_name("field")
        } else {
            Some(callee)
        };
        let Some(name_node) = name_node else { return };
        let name = node_text(name_node, &file.source);
        if !index.reference_returns.borrow().names.contains(name) {
            return;
        }
        let mut scope = call.parent();
        while let Some(parent) = scope {
            if parent.kind() == "template_declaration" {
                // A template parameter may shadow a concrete record's name.
                // Nominal source lookup cannot certify this receiver's type.
                index.reference_returns.borrow_mut().block_name(name);
                return;
            }
            scope = parent.parent();
        }
        let function = functions
            .iter()
            .rev()
            .find(|f| f.begin <= call.start_byte() && call.end_byte() <= f.end);
        let receiver = if member {
            callee.child_by_field_name("argument")
        } else {
            None
        };
        // Use lexical receiver binding; never infer the receiver from a
        // same-spelled variable in a different function or file.
        let owner = receiver
            .and_then(|r| {
                expression_record(
                    r,
                    file,
                    index,
                    bindings,
                    &HashMap::new(),
                    function.and_then(|f| f.owner),
                )
            })
            .or_else(|| {
                (!member && binding_at(bindings, name, call.start_byte()).is_none())
                    .then(|| function.and_then(|f| f.owner))
                    .flatten()
            });
        let Some(owner) = owner else {
            index.reference_returns.borrow_mut().block_name(name);
            return;
        };
        let key = (owner, name.to_owned());
        let getter = index.reference_returns.borrow().getters.get(&key).cloned();
        let Some(getter) = getter else { return };
        let block = || {
            index
                .reference_returns
                .borrow_mut()
                .blocked
                .insert(key.clone());
        };
        if call.has_error()
            || inside_error(call)
            || call
                .child_by_field_name("arguments")
                .is_none_or(|a| a.named_child_count() != 0)
        {
            block();
            return;
        }
        let Some(parent) = call.parent() else {
            block();
            return;
        };
        if parent.kind() == "expression_statement" {
            return;
        }
        let info = index
            .record(owner)
            .fields
            .iter()
            .find(|f| f.name == getter.field)
            .unwrap();
        let supported = match parent.kind() {
            "update_expression" | "assignment_expression" | "binary_expression" => true,
            "field_expression" => {
                info.is_atomic
                    && parent.child_by_field_name("argument") == Some(call)
                    && parent
                        .child_by_field_name("operator")
                        .is_some_and(|op| node_text(op, &file.source) == ".")
                    && parent.child_by_field_name("field").is_some_and(|method| {
                        matches!(
                            node_text(method, &file.source),
                            "load"
                                | "store"
                                | "exchange"
                                | "fetch_add"
                                | "fetch_sub"
                                | "fetch_and"
                                | "fetch_or"
                                | "fetch_xor"
                                | "compare_exchange_strong"
                                | "compare_exchange_weak"
                        )
                    })
                    && parent.parent().is_some_and(|outer| {
                        outer.kind() == "call_expression"
                            && outer.child_by_field_name("function") == Some(parent)
                    })
            }
            "argument_list" => {
                info.is_hot_sync && standard_guard_acquires_argument(call, &file.source)
            }
            "return_statement" => {
                let mut scope = parent.parent();
                let mut value_return = false;
                while let Some(node) = scope {
                    if node.kind() == "function_definition" {
                        value_return = node
                            .child_by_field_name("declarator")
                            .is_some_and(|d| d.kind() == "function_declarator")
                            && node.child_by_field_name("type").is_some_and(|t| {
                                matches!(t.kind(), "primitive_type" | "sized_type_specifier")
                            });
                        break;
                    }
                    if node.kind() == "lambda_expression" {
                        break;
                    }
                    scope = node.parent();
                }
                value_return
            }
            "init_declarator" => {
                parent
                    .child_by_field_name("declarator")
                    .is_some_and(|d| d.kind() == "identifier")
                    && parent
                        .parent()
                        .and_then(|d| d.child_by_field_name("type"))
                        .is_some_and(|t| {
                            matches!(t.kind(), "primitive_type" | "sized_type_specifier")
                        })
            }
            _ => false,
        };
        if !supported {
            block();
            return;
        }
        let Some(function) = function else {
            block();
            return;
        };
        let receiver_name = receiver.and_then(|r| receiver_identifier(r, &file.source));
        let binding = receiver_name
            .as_deref()
            .and_then(|name| binding_at(bindings, name, call.start_byte()));
        let owned =
            function.owner == Some(owner) && receiver_name.as_deref().is_none_or(|r| r == "this");
        by_line
            .entry(call.start_position().row + 1)
            .or_default()
            .push(SyntaxAccess {
                needs_line_fallback: false,
                record: owner,
                field: getter.field,
                kind: expression_access_kind(call, info, &file.source),
                start_byte: call.start_byte(),
                atomic: expression_is_atomic(call, info, &file.source),
                receiver: receiver_name.clone(),
                raw_pointer: callee
                    .child_by_field_name("operator")
                    .is_some_and(|op| node_text(op, &file.source) == "->"),
                initialization: owned
                    && function
                        .constructor_unpublished_until
                        .is_some_and(|end| call.start_byte() < end),
                in_record_constructor: owned && function.constructor_unpublished_until.is_some(),
                function: Some(function.name.clone()),
                loop_depth: Some(access_loop_depth(call)),
                thread_local: binding.is_some_and(|b| {
                    b.thread_local && !escaping.contains(&(b.declaration, b.begin))
                }),
                nonescaping_local: binding.is_some_and(|b| {
                    b.local_owner && !escaping.contains(&(b.declaration, b.begin))
                }),
                automatic_receiver: binding
                    .is_some_and(|b| b.local_owner && b.callable == enclosing_callable(call)),
                contiguous_element: false,
                element_index: None,
                element_member_path: Vec::new(),
            });
    });
}
