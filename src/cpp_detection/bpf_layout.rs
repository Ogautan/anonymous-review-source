//! Bounded layout proof for mmap-backed BPF array partitions.
//! Unknown control flow and arithmetic invalidate the proof, not the candidate.
use super::super::parser::{ParsedCppFile, node_text, walk_nodes};
use super::call_argument_lists;
use std::collections::{HashMap, HashSet};
use tree_sitter::Node;

type Affine = (i64, i64, i64); // CPU coefficient, inclusive element-offset interval

pub(super) fn separated_accesses(file: &ParsedCppFile, block: usize) -> HashSet<(usize, String)> {
    let mut result = HashSet::new();
    let Some(tree) = &file.tree else {
        return result;
    };
    if !file.is_c || !matches!(block, 32 | 64 | 128) {
        return result;
    }
    let declared_calls = super::scalar_calls::collect(file);
    let map_writes = super::bpf_calls::collect(file);
    let mut overridden_helper = false;
    walk_nodes(tree.root_node(), &mut |n| {
        let name = if matches!(n.kind(), "preproc_def" | "preproc_function_def") {
            n.child_by_field_name("name")
        } else if n.kind() == "function_declarator" {
            n.child_by_field_name("declarator")
        } else {
            None
        };
        overridden_helper |= name.is_some_and(|n| {
            matches!(
                node_text(n, &file.source),
                "bpf_get_smp_processor_id"
                    | "bpf_ktime_get_ns"
                    | "bpf_map_update_elem"
                    | "bpf_map_lookup_elem"
            )
        });
    });
    if overridden_helper {
        return result;
    }
    let mut source = file.source.as_bytes().to_vec();
    walk_nodes(tree.root_node(), &mut |n| {
        if n.kind() == "comment" {
            for byte in &mut source[n.byte_range()] {
                if *byte != b'\n' {
                    *byte = b' ';
                }
            }
        }
    });
    let maps = scalar_maps(&String::from_utf8_lossy(&source), true);
    let ordinary_maps = scalar_maps(&String::from_utf8_lossy(&source), false)
        .difference(&maps)
        .cloned()
        .collect::<HashSet<_>>();
    let mut ordinary_calls = HashMap::<usize, (usize, String, i64, i64)>::new();
    let mut safe_calls = HashSet::new();
    if maps.is_empty() && ordinary_maps.is_empty() {
        return result;
    }
    let mut constants = HashMap::new();
    let mut invalid = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(
            node.kind(),
            "preproc_def" | "preproc_function_def" | "preproc_call"
        ) {
            return;
        }
        let Some(name) = node.child_by_field_name("name") else {
            if node_text(node, &file.source)
                .trim_start()
                .starts_with("#undef")
            {
                invalid.extend(
                    super::identifier_tokens(node_text(node, &file.source)).map(str::to_string),
                );
            }
            return;
        };
        let name = node_text(name, &file.source).to_string();
        let mut ancestor = node.parent();
        let mut conditional = false;
        while let Some(parent) = ancestor {
            conditional |= parent.kind().starts_with("preproc_if");
            ancestor = parent.parent();
        }
        let value = node
            .child_by_field_name("value")
            .and_then(|n| integer(node_text(n, &file.source)));
        if conditional || constants.contains_key(&name) || value.is_none() {
            invalid.insert(name.clone());
        }
        if let Some(value) = value {
            constants.insert(name, (0, value, value));
        }
    });
    constants.retain(|name, _| !invalid.contains(name));
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "function_definition" {
            return;
        }
        let Some(body) = node.child_by_field_name("body") else {
            return;
        };
        // An address-taken local may be modified through an alias even after a
        // new assignment. Never reconstruct a must-value for such a binding.
        let mut forbidden = HashSet::new();
        let mut native_locals = HashSet::new();
        walk_nodes(body, &mut |n| {
            if n.kind() == "pointer_expression"
                && node_text(n, &file.source).starts_with('&')
                && !readonly_map_input(n, file)
            {
                forbidden.extend(
                    super::identifier_tokens(node_text(n, &file.source)).map(str::to_string),
                );
            }
        });
        let mut local_constants = constants.clone();
        let mut visible_maps = maps.clone();
        visible_maps.extend(ordinary_maps.iter().cloned());
        // Parameters and local declarations must not inherit macro values.
        walk_nodes(node, &mut |n| {
            if matches!(n.kind(), "declaration" | "parameter_declaration") {
                for token in super::identifier_tokens(
                    node_text(n, &file.source).split('=').next().unwrap_or(""),
                ) {
                    local_constants.remove(token);
                    visible_maps.remove(token);
                }
            }
        });
        let mut values = HashMap::new();
        let mut steps = Vec::new();
        branch_steps(body, &mut steps, 0);
        let mut saved = Vec::new();
        for step in steps {
            let statement = match step {
                Step::Save => {
                    saved.push((values.clone(), native_locals.clone()));
                    continue;
                }
                Step::Restore => {
                    if let Some((v, n)) = saved.pop() {
                        values = v;
                        native_locals = n;
                    }
                    continue;
                }
                Step::Clear => {
                    values.clear();
                    continue;
                }
                Step::Condition(condition, refine) => {
                    invalidate_effects(condition, file, &mut values, &declared_calls, &map_writes);
                    if refine {
                        refine_upper_bound(
                            condition,
                            file,
                            &mut values,
                            &local_constants,
                            &native_locals,
                            &forbidden,
                        );
                    }
                    continue;
                }
                Step::Statement(statement) => statement,
            };
            if statement.has_error() {
                values.clear();
                continue;
            }
            // Non-mmap ARRAY values still have 8-byte slot alignment.
            // With one fixed slot per CPU and a block-multiple stride, every
            // possible 8-byte-aligned base phase separates the CPU slots.
            // Require every reference to this map to use the same partition
            // below; arbitrary offsets or remote-CPU writes invalidate it.
            walk_nodes(statement, &mut |call| {
                if call.kind() != "call_expression" {
                    return;
                }
                let Some(callee) = call.child_by_field_name("function") else {
                    return;
                };
                let callee = node_text(callee, &file.source);
                if !matches!(callee, "bpf_map_update_elem" | "bpf_map_lookup_elem") {
                    return;
                }
                if callee == "bpf_map_lookup_elem" && !lookup_stays_in_slot(call, file) {
                    return;
                }
                let Some(args) = call.child_by_field_name("arguments") else {
                    return;
                };
                let (Some(map), Some(key)) = (args.named_child(0), args.named_child(1)) else {
                    return;
                };
                let map_name = node_text(map, &file.source)
                    .trim()
                    .trim_start_matches('&')
                    .trim();
                if !ordinary_maps.contains(map_name) || !visible_maps.contains(map_name) {
                    return;
                }
                if key.kind() != "pointer_expression"
                    || !node_text(key, &file.source).starts_with('&')
                {
                    return;
                }
                let Some(key) = key.child_by_field_name("argument") else {
                    return;
                };
                let Some((stride, lower, upper)) = affine(key, file, &values, &local_constants, 0)
                else {
                    return;
                };
                if stride > 0
                    && lower == upper
                    && lower >= 0
                    && lower < stride
                    && stride
                        .checked_mul(8)
                        .is_some_and(|bytes| bytes >= block as i64 && bytes % block as i64 == 0)
                {
                    ordinary_calls.insert(
                        call.start_byte(),
                        (
                            call.start_position().row + 1,
                            map_name.to_string(),
                            stride,
                            lower,
                        ),
                    );
                }
            });
            match statement.kind() {
                "comment" => {}
                "declaration" => {
                    let native = statement.child_by_field_name("type").is_some_and(|t| {
                        matches!(
                            node_text(t, &file.source),
                            "u32"
                                | "__u32"
                                | "uint32_t"
                                | "unsigned int"
                                | "u64"
                                | "__u64"
                                | "uint64_t"
                        )
                    });
                    let mut cursor = statement.walk();
                    for decl in statement
                        .named_children(&mut cursor)
                        .filter(|n| matches!(n.kind(), "identifier" | "init_declarator"))
                    {
                        let name = decl.child_by_field_name("declarator").unwrap_or(decl);
                        if name.kind() != "identifier" {
                            // A pointer declaration does not overwrite other
                            // local scalar bindings. Its initializer effects
                            // are checked below, and address-taken indices are
                            // already forbidden throughout this function.
                            let mut binding = name;
                            while binding.kind() == "pointer_declarator" {
                                let Some(inner) = binding.child_by_field_name("declarator") else {
                                    break;
                                };
                                binding = inner;
                            }
                            if binding.kind() == "identifier" {
                                let name = node_text(binding, &file.source);
                                values.remove(name);
                                native_locals.remove(name);
                            } else {
                                values.clear();
                            }
                            continue;
                        }
                        let value = decl
                            .child_by_field_name("value")
                            .and_then(|n| affine(n, file, &values, &local_constants, 0));
                        let name = node_text(name, &file.source).to_string();
                        if native {
                            native_locals.insert(name.clone());
                        } else {
                            native_locals.remove(&name);
                        }
                        let value = if native_locals.contains(&name) && !forbidden.contains(&name) {
                            value
                        } else {
                            None
                        };
                        values.insert(name, value);
                    }
                    // Addresses and unknown calls can publish or modify locals.
                    invalidate_effects(statement, file, &mut values, &declared_calls, &map_writes);
                }
                "expression_statement" => {
                    let Some(expr) = statement.named_child(0) else {
                        continue;
                    };
                    if expr.kind() == "assignment_expression" {
                        if let (Some(lhs), Some(rhs), Some(op)) = (
                            expr.child_by_field_name("left"),
                            expr.child_by_field_name("right"),
                            expr.child_by_field_name("operator"),
                        ) {
                            if lhs.kind() == "identifier" && node_text(op, &file.source) == "=" {
                                let value = affine(rhs, file, &values, &local_constants, 0);
                                let name = node_text(lhs, &file.source).to_string();
                                let value = if native_locals.contains(&name)
                                    && !forbidden.contains(&name)
                                {
                                    value
                                } else {
                                    None
                                };
                                values.insert(name, value);
                            } else {
                                values.clear();
                            }
                        }
                    } else if expr.kind() == "call_expression" {
                        let mut side_effect = false;
                        walk_nodes(expr, &mut |n| {
                            side_effect |=
                                matches!(n.kind(), "assignment_expression" | "update_expression");
                        });
                        if side_effect {
                            values.clear();
                            continue;
                        }
                        let callee = expr
                            .child_by_field_name("function")
                            .map(|n| node_text(n, &file.source))
                            .unwrap_or("");
                        if map_writes.contains_key(callee)
                            && let Some(args) = expr.child_by_field_name("arguments")
                        {
                            let mut cursor = args.walk();
                            let args: Vec<_> = args.named_children(&mut cursor).collect();
                            let summary = &map_writes[callee];
                            if args.len() > summary.map_argument.max(summary.key_argument) {
                                let map = node_text(args[summary.map_argument], &file.source)
                                    .trim()
                                    .trim_start_matches('&')
                                    .trim();
                                let mut index = args[summary.key_argument];
                                if index.kind() == "pointer_expression"
                                    && node_text(index, &file.source).starts_with('&')
                                    && let Some(argument) = index.child_by_field_name("argument")
                                {
                                    index = argument;
                                }
                                if maps.contains(map)
                                    && visible_maps.contains(map)
                                    && let Some((stride, lower, upper)) =
                                        affine(index, file, &values, &local_constants, 0)
                                    && stride > 0
                                    && lower >= 0
                                    && upper < stride
                                    && let Some(bytes) = stride.checked_mul(8)
                                    && bytes >= block as i64
                                    && bytes % block as i64 == 0
                                {
                                    safe_calls.insert(expr.start_byte());
                                    result.insert((expr.start_position().row + 1, map.to_string()));
                                }
                            }
                        }
                    } else {
                        values.clear();
                    }
                    invalidate_effects(statement, file, &mut values, &declared_calls, &map_writes);
                }
                // Do not turn a conditional assignment or loop iteration into
                // a must-reaching definition. Fresh straight-line facts may
                // be established after this boundary.
                _ => values.clear(),
            }
        }
    });
    // Line-level candidate collection can merge several calls. Every call
    // to the same map on that line must independently carry the proof.
    walk_nodes(tree.root_node(), &mut |n| {
        if n.kind() != "call_expression" || safe_calls.contains(&n.start_byte()) {
            return;
        }
        let name = n
            .child_by_field_name("function")
            .map(|n| node_text(n, &file.source))
            .unwrap_or("");
        if map_writes.contains_key(name)
            && let Some(args) = n.child_by_field_name("arguments")
            && let Some(map) = args.named_child(map_writes[name].map_argument as u32)
        {
            let map = node_text(map, &file.source)
                .trim()
                .trim_start_matches('&')
                .trim();
            result.remove(&(n.start_position().row + 1, map.to_string()));
        }
    });
    let mut rejected = HashSet::new();
    let mut partitions = HashMap::new();
    for (_, map, stride, slot) in ordinary_calls.values() {
        if partitions
            .insert(map.clone(), (*stride, *slot))
            .is_some_and(|old| old != (*stride, *slot))
        {
            rejected.insert(map.clone());
        }
    }
    // Every expression reference must be the direct map argument of a proven
    // helper call, including lookups. Unknown helpers, aliasing and accesses
    // outside a straight-line proof must not borrow another call's partition.
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "identifier" {
            return;
        }
        let name = node_text(node, &file.source);
        if !ordinary_maps.contains(name) {
            return;
        }
        let mut ancestor = node.parent();
        let mut function_local = false;
        let mut proven = false;
        while let Some(parent) = ancestor {
            if parent.kind() == "call_expression"
                && ordinary_calls.contains_key(&parent.start_byte())
            {
                proven = true;
            }
            function_local |= parent.kind() == "function_definition";
            ancestor = parent.parent();
        }
        let global_reference = node.parent().is_some_and(|parent| {
            matches!(
                parent.kind(),
                "pointer_expression"
                    | "argument_list"
                    | "init_declarator"
                    | "assignment_expression"
            )
        });
        if (function_local || global_reference) && !proven {
            rejected.insert(name.to_string());
        }
    });
    for (_, (line, map, _, _)) in ordinary_calls {
        if !rejected.contains(&map) {
            result.insert((line, map));
        }
    }
    result
}

// A lookup exposes a pointer into the map. Limit the proof to scalar
// dereferences/null tests of that binding; pointer arithmetic or publication
// can access another CPU's slot and must keep the candidate.
fn lookup_stays_in_slot(call: Node<'_>, file: &ParsedCppFile) -> bool {
    let Some(binding) = call.parent() else {
        return false;
    };
    let Some(mut name) = (match binding.kind() {
        "assignment_expression" => binding.child_by_field_name("left"),
        "init_declarator" => binding.child_by_field_name("declarator"),
        _ => None,
    }) else {
        return false;
    };
    while name.kind() == "pointer_declarator" {
        let Some(inner) = name.child_by_field_name("declarator") else {
            return false;
        };
        name = inner;
    }
    if name.kind() != "identifier" {
        return false;
    }
    let name_text = node_text(name, &file.source);
    let mut function = call.parent();
    while function.is_some_and(|node| node.kind() != "function_definition") {
        function = function.and_then(|node| node.parent());
    }
    let Some(function) = function else {
        return false;
    };
    let mut safe = true;
    walk_nodes(function, &mut |node| {
        if node.kind() != "identifier"
            || node_text(node, &file.source) != name_text
            || node.id() == name.id()
        {
            return;
        }
        let Some(parent) = node.parent() else {
            safe = false;
            return;
        };
        let allowed = match parent.kind() {
            "pointer_declarator" => true,
            "pointer_expression" => node_text(parent, &file.source)
                .trim_start()
                .starts_with('*'),
            "unary_expression" => node_text(parent, &file.source)
                .trim_start()
                .starts_with('!'),
            "condition_clause" => true,
            "binary_expression" => parent
                .child_by_field_name("operator")
                .is_some_and(|op| matches!(node_text(op, &file.source), "==" | "!=")),
            _ => false,
        };
        safe &= allowed;
    });
    safe
}

// Branch-local facts are discarded at the join. In particular, an assignment
// in one arm cannot prove the value used after the conditional.
enum Step<'a> {
    Statement(Node<'a>),
    Save,
    Restore,
    Clear,
    Condition(Node<'a>, bool),
}

fn branch_steps<'a>(node: Node<'a>, steps: &mut Vec<Step<'a>>, depth: usize) {
    if depth > 16 || node.has_error() {
        steps.push(Step::Clear);
        return;
    }
    if node.kind() == "compound_statement" {
        steps.push(Step::Save);
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            branch_steps(child, steps, depth + 1);
        }
        steps.push(Step::Restore);
        steps.push(Step::Clear);
    } else if node.kind() == "if_statement" {
        if let Some(condition) = node.child_by_field_name("condition") {
            steps.push(Step::Condition(condition, false));
            if let Some(arm) = node.child_by_field_name("consequence") {
                steps.push(Step::Save);
                steps.push(Step::Condition(condition, true));
                branch_steps(arm, steps, depth + 1);
                steps.push(Step::Restore);
            }
            if let Some(arm) = node.child_by_field_name("alternative") {
                steps.push(Step::Save);
                if arm.kind() == "else_clause" {
                    if let Some(child) = arm.named_child(0) {
                        branch_steps(child, steps, depth + 1);
                    }
                } else {
                    branch_steps(arm, steps, depth + 1);
                }
                steps.push(Step::Restore);
            }
        }
        steps.push(Step::Clear);
    } else {
        steps.push(Step::Statement(node));
    }
}

fn refine_upper_bound(
    mut node: Node<'_>,
    file: &ParsedCppFile,
    values: &mut HashMap<String, Option<Affine>>,
    constants: &HashMap<String, Affine>,
    native: &HashSet<String>,
    forbidden: &HashSet<String>,
) {
    while matches!(node.kind(), "condition_clause" | "parenthesized_expression") {
        let Some(child) = node.named_child(0) else {
            return;
        };
        node = child;
    }
    if node.kind() != "binary_expression" {
        return;
    }
    let (Some(left), Some(right), Some(op)) = (
        node.child_by_field_name("left"),
        node.child_by_field_name("right"),
        node.child_by_field_name("operator"),
    ) else {
        return;
    };
    if left.kind() != "identifier" || node_text(op, &file.source) != "<" {
        return;
    }
    let name = node_text(left, &file.source);
    if !native.contains(name) || forbidden.contains(name) {
        return;
    }
    let Some((0, low, high)) = affine(right, file, values, constants, 0) else {
        return;
    };
    if low != high || high <= 0 {
        return;
    }
    // Only unsigned local values receive the implicit lower bound zero.
    // If an affine value was known already, do not discard its CPU term.
    if values.get(name).is_some_and(|v| v.is_some()) {
        return;
    }
    values.insert(name.to_string(), Some((0, 0, high - 1)));
}

// The kernel helper copies key/value input; it does not retain a pointer into
// the caller's stack or write the key. This exception is argument-position
// specific and must not apply to arbitrary address-taking calls.
fn readonly_map_input(node: Node<'_>, file: &ParsedCppFile) -> bool {
    let Some(args) = node.parent().filter(|p| p.kind() == "argument_list") else {
        return false;
    };
    let Some(call) = args.parent().filter(|p| p.kind() == "call_expression") else {
        return false;
    };
    let callee = call
        .child_by_field_name("function")
        .map(|n| node_text(n, &file.source))
        .unwrap_or("");
    (callee == "bpf_map_update_elem"
        && args.named_child_count() == 4
        && [1, 2]
            .into_iter()
            .any(|i| args.named_child(i).is_some_and(|n| n.id() == node.id())))
        || (callee == "bpf_map_lookup_elem"
            && args.named_child_count() == 2
            && args.named_child(1).is_some_and(|n| n.id() == node.id()))
}

fn invalidate_effects(
    node: Node<'_>,
    file: &ParsedCppFile,
    values: &mut HashMap<String, Option<Affine>>,
    declared_calls: &HashMap<String, super::scalar_calls::Contract>,
    map_writes: &HashMap<String, super::bpf_calls::MapWrite>,
) {
    walk_nodes(node, &mut |n| {
        if n.kind() == "assignment_expression"
            && n.parent()
                .is_some_and(|p| p.kind() != "expression_statement")
        {
            values.clear();
        }
        if n.kind() == "update_expression" {
            values.clear();
        }
        if n.kind() == "pointer_expression"
            && node_text(n, &file.source).starts_with('&')
            && !readonly_map_input(n, file)
        {
            for token in super::identifier_tokens(node_text(n, &file.source)) {
                if let Some(value) = values.get_mut(token) {
                    *value = None;
                }
            }
        }
        if n.kind() == "call_expression" {
            let name = n
                .child_by_field_name("function")
                .map(|n| node_text(n, &file.source))
                .unwrap_or("");
            if !matches!(
                name,
                "bpf_get_smp_processor_id"
                    | "bpf_ktime_get_ns"
                    | "bpf_map_update_elem"
                    | "bpf_map_lookup_elem"
            ) && !map_writes.contains_key(name)
                && !super::scalar_calls::declared_c_call(declared_calls, n, &file.source)
            {
                values.clear();
            }
        }
    });
}

fn integer(text: &str) -> Option<i64> {
    let text = text.trim().trim_end_matches(['u', 'U', 'l', 'L']);
    if text.is_empty() || !text.bytes().all(|c| c.is_ascii_digit()) {
        return None;
    }
    // Avoid interpreting C octal as decimal.
    if text.len() > 1 && text.starts_with('0') {
        return None;
    }
    text.parse().ok()
}

fn affine(
    node: Node<'_>,
    file: &ParsedCppFile,
    values: &HashMap<String, Option<Affine>>,
    constants: &HashMap<String, Affine>,
    depth: usize,
) -> Option<Affine> {
    if depth > 16 {
        return None;
    }
    let recurse = |n| affine(n, file, values, constants, depth + 1);
    match node.kind() {
        "identifier" => {
            let name = node_text(node, &file.source);
            values
                .get(name)
                .copied()
                .unwrap_or_else(|| constants.get(name).copied())
        }
        "number_literal" => integer(node_text(node, &file.source)).map(|n| (0, n, n)),
        "parenthesized_expression" => recurse(node.named_child(0)?),
        "call_expression"
            if node_text(node.child_by_field_name("function")?, &file.source)
                == "bpf_get_smp_processor_id"
                && node.child_by_field_name("arguments")?.named_child_count() == 0 =>
        {
            Some((1, 0, 0))
        }
        "binary_expression" => {
            let (a, lo, hi) = recurse(node.child_by_field_name("left")?)?;
            let (c, low, high) = recurse(node.child_by_field_name("right")?)?;
            match node_text(node.child_by_field_name("operator")?, &file.source) {
                "+" => Some((
                    a.checked_add(c)?,
                    lo.checked_add(low)?,
                    hi.checked_add(high)?,
                )),
                "-" => Some((
                    a.checked_sub(c)?,
                    lo.checked_sub(high)?,
                    hi.checked_sub(low)?,
                )),
                "*" if a == 0 && lo == hi && lo >= 0 => Some((
                    lo.checked_mul(c)?,
                    lo.checked_mul(low)?,
                    lo.checked_mul(high)?,
                )),
                "*" if c == 0 && low == high && low >= 0 => Some((
                    a.checked_mul(low)?,
                    lo.checked_mul(low)?,
                    hi.checked_mul(low)?,
                )),
                "/" if a == 0 && lo == hi && c == 0 && low == high && low > 0 => {
                    Some((0, lo.checked_div(low)?, lo.checked_div(low)?))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn scalar_maps(source: &str, require_mmap: bool) -> HashSet<String> {
    let mut maps = HashSet::new();
    let mut seen = HashSet::new();
    let mut block = String::new();
    let mut active = false;
    for line in source.lines().map(str::trim) {
        if line.starts_with("struct {") {
            block.clear();
            active = true;
        }
        if !active {
            continue;
        }
        block.push_str(line);
        block.push(' ');
        if line.starts_with('}') && line.contains("SEC(") {
            let Some(map_name) = super::identifier_tokens(line).next() else {
                active = false;
                continue;
            };
            if !seen.insert(map_name.to_string()) {
                maps.remove(map_name);
                active = false;
                continue;
            }
            let uints = call_argument_lists(&block, "__uint");
            let types = call_argument_lists(&block, "__type");
            let property = |name: &str, value: &str| {
                uints.iter().any(|args| {
                    args.len() == 2 && args[0].trim() == name && args[1].trim() == value
                })
            };
            // Kernel ARRAY values occupy 8-byte-rounded slots; mmap-backed
            // values start at a page boundary. Do not infer base alignment for
            // an ordinary map or the size of an unknown record value.
            if !block.contains('#')
                && property("type", "BPF_MAP_TYPE_ARRAY")
                && (!require_mmap || property("map_flags", "BPF_F_MMAPABLE"))
                && types.iter().any(|args| {
                    args.len() == 2
                        && args[0].trim() == "value"
                        && matches!(
                            args[1].trim(),
                            "u64" | "__u64" | "uint64_t" | "u32" | "__u32" | "uint32_t"
                        )
                })
                && let Some(name) = super::identifier_tokens(line).next()
            {
                maps.insert(name.to_string());
            }
            active = false;
        }
    }
    maps
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpp_detection::{parser::parse_cpp_files, types::CppFile};

    fn separated(width: &str, body: &str, block: usize, flags: &str) -> bool {
        let source = format!(
            r#"
static void array_incr(void *map, u32 key) {{
 u64 *value = bpf_map_lookup_elem(map, &key);
 if (value) __sync_fetch_and_add(value, 1);
}}
#define GROUP_SIZE {width}
struct {{
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __uint(map_flags, {flags});
 __type(value, u64);
}} counters SEC(".maps");
int sample() {{
 {body}
}}
"#
        );
        let files = parse_cpp_files(vec![CppFile {
            path: "sample.bpf.c".into(),
            source,
        }]);
        !separated_accesses(&files[0], block).is_empty()
    }

    #[test]
    fn affine_groups_use_bytes_and_effective_block_size() {
        let body = "u32 offset = GROUP_SIZE * bpf_get_smp_processor_id();\nu32 idx = offset + 3;\narray_incr(&counters, idx);";
        for (block, expected) in [(32, true), (64, true), (128, false)] {
            assert_eq!(separated("8", body, block, "BPF_F_MMAPABLE"), expected);
        }
        assert!(!separated("1", body, 64, "BPF_F_MMAPABLE"));
        assert!(!separated("8", body, 64, "0"));
        assert!(!separated(
            "8",
            &body.replace("+ 3", "+ 8"),
            64,
            "BPF_F_MMAPABLE"
        ));
    }

    #[test]
    fn control_flow_aliases_and_unknown_arithmetic_do_not_prove_separation() {
        for middle in [
            "if (enabled) idx = bpf_get_smp_processor_id();",
            "u32 *p = &idx; idx = offset; *p = 1;",
            "idx /= 8;",
            "idx = scramble(idx);",
            "idx++;",
            "idx = (u8)offset;",
            "u32 other = (idx = bpf_get_smp_processor_id());",
        ] {
            let body = format!(
                "u32 offset = GROUP_SIZE * bpf_get_smp_processor_id();\nu32 idx = offset;\n{middle}\narray_incr(&counters, idx);"
            );
            assert!(!separated("8", &body, 64, "BPF_F_MMAPABLE"), "{middle}");
        }
        assert!(!separated(
            "8",
            "u8 idx = GROUP_SIZE * bpf_get_smp_processor_id();\narray_incr(&counters, idx);",
            64,
            "BPF_F_MMAPABLE"
        ));
    }
    #[test]
    fn same_line_calls_and_conditional_constants_are_not_merged_into_a_proof() {
        let body = "u32 idx = GROUP_SIZE * bpf_get_smp_processor_id();\narray_incr(&counters, idx); array_incr(&counters, bpf_get_smp_processor_id());";
        assert!(!separated("8", body, 64, "BPF_F_MMAPABLE"));
        let body =
            "u32 idx = GROUP_SIZE * bpf_get_smp_processor_id();\narray_incr(&counters, idx);";
        for width in [
            "8\n#undef GROUP_SIZE\n#define GROUP_SIZE 1",
            "8\n#if SMALL\n#undef GROUP_SIZE\n#define GROUP_SIZE 1\n#endif",
        ] {
            assert!(!separated(width, body, 64, "BPF_F_MMAPABLE"));
        }
        assert!(!separated(
            "8",
            body,
            64,
            "0 /* __uint(map_flags, BPF_F_MMAPABLE) */"
        ));
        let body = "u32 counters = 0;\nu32 idx = GROUP_SIZE * bpf_get_smp_processor_id();\narray_incr(&counters, idx);";
        assert!(!separated("8", body, 64, "BPF_F_MMAPABLE"));
    }
    #[test]
    fn guarded_unsigned_offset_stays_inside_its_cpu_group() {
        let body = "u32 op = unknown();\nu32 idx;\nif (op < GROUP_SIZE / 2) {\n idx = GROUP_SIZE * bpf_get_smp_processor_id() + op;\n array_incr(&counters, idx);\n}";
        assert!(separated("8", body, 64, "BPF_F_MMAPABLE"));
        assert!(!separated("8", body, 128, "BPF_F_MMAPABLE"));
        for altered in [
            body.replace("op < GROUP_SIZE / 2", "op < GROUP_SIZE * 2"),
            body.replace("op < GROUP_SIZE / 2", "flag"),
            body.replace("u32 op", "int op"),
            body.replace(" idx =", " op = unknown(); idx ="),
        ] {
            assert!(!separated("8", &altered, 64, "BPF_F_MMAPABLE"), "{altered}");
        }
        let after = "u32 idx;\nif (flag) { idx = GROUP_SIZE * bpf_get_smp_processor_id(); }\narray_incr(&counters, idx);";
        assert!(!separated("8", after, 64, "BPF_F_MMAPABLE"));
    }
    #[test]
    fn kernel_time_and_map_input_do_not_publish_stack_indices() {
        let body = "u32 cpu = bpf_get_smp_processor_id();\nu64 ts = bpf_ktime_get_ns();\nu32 idx = GROUP_SIZE * cpu;\nbpf_map_update_elem(&counters, &idx, &ts, 0);";
        assert!(separated("8", body, 64, "BPF_F_MMAPABLE"));
        assert!(!separated("8", body, 128, "BPF_F_MMAPABLE"));
        assert!(!separated("1", body, 64, "BPF_F_MMAPABLE"));
        assert!(!separated(
            "8",
            &body.replace("u32 idx", "publish(&cpu); u32 idx"),
            64,
            "BPF_F_MMAPABLE"
        ));
    }

    #[test]
    fn readonly_lookup_preserves_unescaped_partition_indices() {
        let body = "u32 idx = GROUP_SIZE * bpf_get_smp_processor_id();\nu64 *value = bpf_map_lookup_elem(&counters, &idx);\narray_incr(&counters, idx);";
        assert!(separated("8", body, 64, "BPF_F_MMAPABLE"));
        assert!(!separated("8", body, 128, "BPF_F_MMAPABLE"));
        for altered in [
            body.replace("bpf_map_lookup_elem", "unknown_lookup"),
            body.replace("u64 *value", "publish(&idx); u64 *value"),
            body.replace("&idx);", "&(idx = 0));"),
        ] {
            assert!(!separated("8", &altered, 64, "BPF_F_MMAPABLE"), "{altered}");
        }
    }
}
