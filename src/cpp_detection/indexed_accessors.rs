//! Direct native-element returns used as the actual target of an atomic call.
//! The callee spelling is never the storage identity. Summaries are deliberately
//! bounded to one return and one pointer parameter; unresolved bindings add no
//! positive mutation/contiguity evidence.
use super::*;
use tree_sitter::Node;

type Key = (String, Option<usize>);

struct Summary {
    storage: usize,
    partition: usize,
    arity: usize,
    pointer_return: bool,
    file: String,
    line: usize,
}

#[derive(Default)]
pub(super) struct Summaries {
    entries: HashMap<Key, Summary>,
    macros: HashSet<String>,
    defined_callees: HashSet<String>,
}

fn unwrap(mut node: Node<'_>) -> Node<'_> {
    while node.kind() == "parenthesized_expression" {
        let Some(inner) = node.named_child(0) else {
            break;
        };
        node = inner;
    }
    node
}

fn ancestors(node: Node<'_>, kinds: &[&str]) -> bool {
    let mut parent = node.parent();
    while let Some(node) = parent {
        if kinds.contains(&node.kind()) {
            return true;
        }
        parent = node.parent();
    }
    false
}

impl Summaries {
    pub(super) fn collect(
        files: &[ParsedCppFile],
        index: &EvidenceIndex<'_>,
        cache_line_size: usize,
    ) -> Self {
        let mut result = Self::default();
        let mut definitions = HashMap::<Key, usize>::new();
        let mut declarations = HashSet::new();
        for file in files {
            let Some(tree) = &file.tree else { continue };
            walk_nodes(tree.root_node(), &mut |node| {
                if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                    && let Some(name) = node.child_by_field_name("name")
                {
                    result
                        .macros
                        .insert(node_text(name, &file.source).to_owned());
                }
                if node.kind() == "function_declarator"
                    && !ancestors(node, &["function_definition"])
                {
                    // A separately declared overload needs signature/visibility
                    // resolution. Do not borrow the sole available body.
                    if let Some(name) = node.child_by_field_name("declarator") {
                        declarations.insert((
                            node_text(name, &file.source)
                                .rsplit("::")
                                .next()
                                .unwrap_or("")
                                .to_owned(),
                            field_access::function_owner(node, file, index),
                        ));
                    }
                }
                if node.kind() != "function_definition" {
                    return;
                }
                let Some(name) = function_definition_name(node, file) else {
                    return;
                };
                result
                    .defined_callees
                    .insert(name.rsplit("::").next().unwrap_or(&name).to_owned());
                let owner = field_access::function_owner(node, file, index);
                let key = (name.rsplit("::").next().unwrap_or(&name).to_owned(), owner);
                *definitions.entry(key.clone()).or_default() += 1;
                if let Some(summary) = summarize(node, file, index, owner, cache_line_size) {
                    result.entries.insert(key, summary);
                }
            });
        }
        result.entries.retain(|key, _| {
            definitions.get(key) == Some(&1)
                && !result.macros.contains(&key.0)
                && !declarations.contains(key)
        });
        result
    }

    pub(super) fn candidates(
        &self,
        file: &ParsedCppFile,
        index: &EvidenceIndex<'_>,
        origins: &IndexPartitionOrigins,
        functions: &[FunctionRegion],
        locks: &HashMap<usize, Vec<String>>,
    ) -> Vec<IndexedWriteCandidate> {
        let mut output = Vec::new();
        if self.entries.is_empty()
            || !self
                .entries
                .keys()
                .any(|(name, _)| contains_identifier(&file.source, name))
        {
            return output;
        }
        let Some(tree) = &file.tree else {
            return output;
        };
        let calls = indexed_summary_calls::collect_spans(file, index)
            .into_iter()
            .map(|call| (call.begin, call))
            .collect::<HashMap<_, _>>();
        let bindings = native_bindings(file);
        walk_nodes(tree.root_node(), &mut |atomic| {
            if atomic.kind() != "call_expression" || atomic.has_error() {
                return;
            }
            let (Some(callee), Some(args)) = (
                atomic.child_by_field_name("function"),
                atomic.child_by_field_name("arguments"),
            ) else {
                return;
            };
            if !matches!(callee.kind(), "identifier" | "qualified_identifier") {
                return;
            }
            let atomic_name = node_text(callee, &file.source);
            if !known_atomic(atomic_name) {
                return;
            }
            let short = atomic_name.rsplit("::").next().unwrap_or(atomic_name);
            if self.macros.contains(short)
                || self.defined_callees.contains(short)
                || shadowed(&bindings, short, atomic.start_byte())
            {
                return;
            }
            for (position, target) in args
                .named_children(&mut args.walk())
                .filter(|arg| arg.kind() != "comment")
                .enumerate()
            {
                let Some(kind) = explicit_atomic_argument_access(atomic_name, position)
                    .filter(|kind| *kind != CppAccessKind::Read)
                else {
                    continue;
                };
                let target = unwrap(target);
                let address = target.kind() == "pointer_expression"
                    && target
                        .child_by_field_name("operator")
                        .is_some_and(|op| node_text(op, &file.source) == "&");
                let call = if address {
                    target.child_by_field_name("argument").map(unwrap)
                } else {
                    Some(target)
                };
                let Some(call) = call.filter(|node| node.kind() == "call_expression") else {
                    continue;
                };
                let Some(bound) = calls.get(&call.start_byte()) else {
                    continue;
                };
                let Some(summary) = self.entries.get(&(bound.name.clone(), bound.owner)) else {
                    continue;
                };
                let Some(callee) = call.child_by_field_name("function") else {
                    continue;
                };
                if address == summary.pointer_return
                    || bound.arguments.len() != summary.arity
                    || (callee.kind() == "identifier"
                        && shadowed(&bindings, &bound.name, call.start_byte()))
                {
                    continue;
                }
                let storage = bound.arguments[summary.storage].trim();
                if !native_at(&bindings, storage, call.start_byte()) {
                    continue;
                }
                let partition = &bound.arguments[summary.partition];
                let line = atomic.start_position().row + 1;
                if !origins.supports_parallel_argument(partition, line) {
                    continue;
                }
                output.push(IndexedWriteCandidate {
                    file: file.path.clone(), line,
                    snippet: node_text(atomic, &file.source).to_owned(),
                    function_name: enclosing_function_name(functions, line),
                    record_name: None, record_line: None, record_peer: None, record_storage: None,
                    field_name: Some(storage.to_owned()), alias_name: None, access_kind: kind,
                    has_direct_partition_evidence: true,
                    access_in_concurrent_context: origins.supports_runtime_identity(partition, line),
                    guard_ids: locks.get(&line).cloned().unwrap_or_default(),
                    evidence: vec![
                        format!("过程间写证据: atomic 参数 {position} 绑定到 '{}' 返回的原生元素；调用方存储 '{storage}'", bound.name),
                        format!("返回位置证据: {}:{}，storage 参数 {}，index 参数 {}", summary.file, summary.line, summary.storage, summary.partition),
                        "分区证据: 实际 index 实参追溯至 worker/API partition".to_owned(),
                    ],
                    storage_identity: None,
                });
            }
        });
        output
    }
}

fn summarize(
    node: Node<'_>,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    owner: Option<usize>,
    cache_line_size: usize,
) -> Option<Summary> {
    if node.has_error()
        || ancestors(
            node,
            &[
                "template_declaration",
                "lambda_expression",
                "function_definition",
            ],
        )
        || (owner.is_none()
            && ancestors(
                node,
                &[
                    "namespace_definition",
                    "struct_specifier",
                    "class_specifier",
                ],
            ))
        || owner.is_some_and(|owner| index.record(owner).has_base_classes)
    {
        return None;
    }
    let body = node.child_by_field_name("body")?;
    let header = &file.source[node.start_byte()..body.start_byte()];
    if identifier_tokens(header)
        .any(|token| matches!(token, "virtual" | "override" | "__device__" | "__global__"))
    {
        return None;
    }
    let outer = node.child_by_field_name("declarator")?;
    let pointer_return = outer.kind() == "pointer_declarator";
    if !pointer_return
        && (outer.kind() != "reference_declarator" || node_text(outer, &file.source).contains("&&"))
    {
        return None;
    }
    let declarator = outer.named_child(0)?;
    if declarator.kind() != "function_declarator" {
        return None;
    }
    let params = declarator.child_by_field_name("parameters")?;
    let params = params
        .named_children(&mut params.walk())
        .filter(|parameter| parameter.kind() != "comment")
        .collect::<Vec<_>>();
    let mut names = Vec::new();
    let mut pointers = Vec::new();
    for (position, parameter) in params.iter().enumerate() {
        if parameter.kind() != "parameter_declaration" {
            return None;
        }
        let declarator = parameter.child_by_field_name("declarator")?;
        let (name, pointer) = match declarator.kind() {
            "identifier" => (declarator, false),
            "pointer_declarator" => (declarator.child_by_field_name("declarator")?, true),
            _ => return None,
        };
        if name.kind() != "identifier" {
            return None;
        }
        names.push(node_text(name, &file.source));
        if pointer {
            pointers.push(position);
        }
    }
    let [storage] = pointers.as_slice() else {
        return None;
    };
    let statements = body
        .named_children(&mut body.walk())
        .filter(|n| n.kind() != "comment")
        .collect::<Vec<_>>();
    let [statement] = statements.as_slice() else {
        return None;
    };
    if statement.kind() != "return_statement" {
        return None;
    }
    let mut returned = unwrap(statement.named_child(0)?);
    if pointer_return {
        if returned.kind() != "pointer_expression"
            || node_text(returned.child_by_field_name("operator")?, &file.source) != "&"
        {
            return None;
        }
        returned = unwrap(returned.child_by_field_name("argument")?);
    }
    if returned.kind() != "subscript_expression"
        || node_text(returned.child_by_field_name("argument")?, &file.source) != names[*storage]
    {
        return None;
    }
    let indices = returned.child_by_field_name("indices")?;
    if indices.named_child_count() != 1 {
        return None;
    }
    let expression = indices.named_child(0)?;
    let text = node_text(expression, &file.source);
    let selected = names
        .iter()
        .enumerate()
        .filter(|(_, name)| contains_identifier(text, name))
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    let [partition] = selected.as_slice() else {
        return None;
    };
    if partition == storage {
        return None;
    }
    let partition_type = node_text(
        params[*partition].child_by_field_name("type")?,
        &file.source,
    );
    if !identifier_tokens(partition_type).all(|word| {
        matches!(
            word,
            "const"
                | "volatile"
                | "unsigned"
                | "signed"
                | "char"
                | "short"
                | "int"
                | "long"
                | "std"
                | "size_t"
                | "ptrdiff_t"
                | "uint32_t"
                | "int32_t"
                | "uint64_t"
                | "int64_t"
        )
    }) {
        return None;
    }
    let mut pure = true;
    walk_nodes(expression, &mut |part| {
        pure &= !matches!(
            part.kind(),
            "call_expression"
                | "subscript_expression"
                | "field_expression"
                | "assignment_expression"
                | "update_expression"
                | "conditional_expression"
                | "comma_expression"
                | "lambda_expression"
        );
        if part.kind() == "binary_expression" {
            let operator = part
                .child_by_field_name("operator")
                .map(|op| node_text(op, &file.source));
            for side in ["left", "right"] {
                if let Some(value) = part.child_by_field_name(side) {
                    let value = node_text(unwrap(value), &file.source)
                        .trim_end_matches(['u', 'U', 'l', 'L']);
                    let literal = value
                        .strip_prefix("0x")
                        .or_else(|| value.strip_prefix("0X"))
                        .and_then(|hex| u128::from_str_radix(hex, 16).ok())
                        .or_else(|| value.parse::<u128>().ok());
                    if matches!((operator, literal), (Some("*" | "&"), Some(0)))
                        || (side == "right"
                            && matches!(
                                (operator, literal),
                                (Some("%"), Some(0 | 1)) | (Some("/"), Some(0))
                            ))
                    {
                        pure = false;
                    }
                }
            }
        }
    });
    if !pure
        || identifier_tokens(text)
            .filter(|token| *token == names[*partition])
            .count()
            != 1
    {
        return None;
    }
    let ty = node_text(params[*storage].child_by_field_name("type")?, &file.source);
    let returned_type = node_text(node.child_by_field_name("type")?, &file.source);
    if ty.split_whitespace().collect::<String>()
        != returned_type.split_whitespace().collect::<String>()
    {
        // Returning a different reference type can invoke an element's
        // conversion operator and refer to entirely different storage.
        return None;
    }
    let expression = unwrap(expression);
    // Distinct selected native elements are separated by at least `step - 1`
    // complete elements. Every complete object occupies at least one byte,
    // so step >= B excludes a shared block without an ABI/type-size estimate.
    // A power-of-two step also preserves this spacing under unsigned wrap.
    if expression.kind() == "binary_expression"
        && expression
            .child_by_field_name("operator")
            .is_some_and(|op| node_text(op, &file.source) == "*")
        && ["left", "right"].iter().any(|side| {
            expression.child_by_field_name(side).is_some_and(|factor| {
                let factor =
                    node_text(unwrap(factor), &file.source).trim_end_matches(['u', 'U', 'l', 'L']);
                factor
                    .parse::<usize>()
                    .ok()
                    .is_some_and(|step| step.is_power_of_two() && step >= cache_line_size)
            })
        })
    {
        return None;
    }
    if field_access::type_record_in_scope(ty, file, index, owner)
        .is_some_and(|record| index.record(record).is_cache_aligned)
    {
        return None;
    }
    Some(Summary {
        storage: *storage,
        partition: *partition,
        arity: params.len(),
        pointer_return,
        file: file.path.clone(),
        line: node.start_position().row + 1,
    })
}

fn known_atomic(name: &str) -> bool {
    let name = name.trim_start_matches("::");
    let name = name.strip_prefix("std::").unwrap_or(name);
    matches!(
        name,
        "atomic_init"
            | "atomic_store"
            | "atomic_store_explicit"
            | "atomic_flag_clear"
            | "atomic_flag_clear_explicit"
            | "atomic_exchange"
            | "atomic_exchange_explicit"
            | "atomic_fetch_add"
            | "atomic_fetch_add_explicit"
            | "atomic_fetch_sub"
            | "atomic_fetch_sub_explicit"
            | "atomic_fetch_and"
            | "atomic_fetch_and_explicit"
            | "atomic_fetch_or"
            | "atomic_fetch_or_explicit"
            | "atomic_fetch_xor"
            | "atomic_fetch_xor_explicit"
            | "atomic_compare_exchange_strong"
            | "atomic_compare_exchange_strong_explicit"
            | "atomic_compare_exchange_weak"
            | "atomic_compare_exchange_weak_explicit"
            | "atomic_flag_test_and_set"
            | "atomic_flag_test_and_set_explicit"
            | "__atomic_load"
            | "__atomic_store"
            | "__atomic_store_n"
            | "__atomic_clear"
            | "__atomic_exchange"
            | "__atomic_exchange_n"
            | "__atomic_compare_exchange"
            | "__atomic_compare_exchange_n"
            | "__atomic_fetch_add"
            | "__atomic_fetch_sub"
            | "__atomic_fetch_and"
            | "__atomic_fetch_or"
            | "__atomic_fetch_xor"
            | "__atomic_fetch_nand"
            | "__atomic_add_fetch"
            | "__atomic_sub_fetch"
            | "__atomic_and_fetch"
            | "__atomic_or_fetch"
            | "__atomic_xor_fetch"
            | "__atomic_nand_fetch"
            | "__atomic_test_and_set"
            | "__sync_fetch_and_add"
            | "__sync_fetch_and_sub"
            | "__sync_fetch_and_or"
            | "__sync_fetch_and_and"
            | "__sync_fetch_and_xor"
            | "__sync_fetch_and_nand"
            | "__sync_add_and_fetch"
            | "__sync_sub_and_fetch"
            | "__sync_or_and_fetch"
            | "__sync_and_and_fetch"
            | "__sync_xor_and_fetch"
            | "__sync_nand_and_fetch"
            | "__sync_bool_compare_and_swap"
            | "__sync_val_compare_and_swap"
            | "__sync_lock_test_and_set"
            | "__sync_lock_release"
    )
}

struct NativeBinding {
    name: String,
    begin: usize,
    end: usize,
    native: bool,
}

fn native_bindings(file: &ParsedCppFile) -> Vec<NativeBinding> {
    let mut result = Vec::new();
    let Some(tree) = &file.tree else {
        return result;
    };
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(node.kind(), "declaration" | "parameter_declaration") {
            return;
        }
        let scope = field_access::binding_scope(node);
        // A prototype's parameter never declares caller storage.
        if node.kind() == "parameter_declaration"
            && !matches!(scope.kind(), "function_definition" | "lambda_expression")
        {
            return;
        }
        if node.kind() == "parameter_declaration" {
            let mut parent = node.parent();
            while let Some(ancestor) = parent {
                if ancestor == scope {
                    break;
                }
                if matches!(
                    ancestor.kind(),
                    "declaration" | "field_declaration" | "type_descriptor"
                ) {
                    return;
                }
                parent = ancestor.parent();
            }
        }
        for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
            let Some(name) = declarator_variable_name(declarator, &file.source) else {
                continue;
            };
            let native = !node.has_error() && native_indexed_declarator(declarator);
            result.push(NativeBinding {
                name,
                begin: declarator.start_byte(),
                end: scope.end_byte(),
                native,
            });
        }
    });
    result
}

fn binding_at<'a>(
    bindings: &'a [NativeBinding],
    name: &str,
    at: usize,
) -> Option<&'a NativeBinding> {
    bindings
        .iter()
        .filter(|b| b.name == name && b.begin < at && at < b.end)
        .max_by_key(|b| b.begin)
}
fn native_at(bindings: &[NativeBinding], name: &str, at: usize) -> bool {
    binding_at(bindings, name, at).is_some_and(|b| b.native)
}
fn shadowed(bindings: &[NativeBinding], name: &str, at: usize) -> bool {
    binding_at(bindings, name, at).is_some()
}
