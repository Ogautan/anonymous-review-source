use std::collections::{HashMap, HashSet};
use std::path::Path;

use regex::Regex;

use super::layout::{
    clean_type_name, element_type_name, extract_align_bytes, is_hot_container_name,
};
use super::parser::{ParsedCppFile, node_text, walk_nodes};
use super::types::{
    AtomicAliasArrayCandidate, CppAccessKind, CppApiEvidence, CppEvidenceItem, CppEvidenceKind,
    CppEvidenceSet, CppStructInfo, IndexedWriteCandidate, StaticHotStateCandidate,
};

#[path = "execution_roles.rs"]
mod execution_roles;

#[path = "field_access.rs"]
mod field_access;

#[path = "indexed_field_distance.rs"]
mod indexed_field_distance;

#[path = "storage_identity.rs"]
mod storage_identity;

#[path = "indexed_storage.rs"]
mod indexed_storage;

#[path = "partition_descriptors.rs"]
mod partition_descriptors;

#[path = "pthread_partitions.rs"]
mod pthread_partitions;

#[path = "returned_callbacks.rs"]
mod returned_callbacks;

#[path = "internal_index_api.rs"]
mod internal_index_api;

#[path = "indexed_calls.rs"]
mod indexed_calls;

#[path = "indexed_accessors.rs"]
mod indexed_accessors;

#[path = "indexed_summary_calls.rs"]
mod indexed_summary_calls;
#[path = "spawn_setup.rs"]
mod spawn_setup;

#[path = "indexed_macros.rs"]
mod indexed_macros;
#[path = "lock_macros.rs"]
mod lock_macros;

#[path = "scalar_macros.rs"]
pub(super) mod scalar_macros;

#[path = "bpf_calls.rs"]
mod bpf_calls;
#[path = "bpf_layout.rs"]
mod bpf_layout;

#[path = "scalar_calls.rs"]
pub(super) mod scalar_calls;

#[path = "synchronous_callbacks.rs"]
mod synchronous_callbacks;

pub fn collect_cpp_evidence(
    files: &[ParsedCppFile],
    structs: &[CppStructInfo],
) -> Vec<CppEvidenceSet> {
    collect_cpp_evidence_with_commands(files, structs, &[])
}

pub(super) fn collect_cpp_evidence_with_commands(
    files: &[ParsedCppFile],
    structs: &[CppStructInfo],
    commands: &[super::types::CppCompileCommand],
) -> Vec<CppEvidenceSet> {
    let runtime_views = super::unevaluated::views(files, commands);
    let files = runtime_views.as_ref();
    let linkage_views = internal_index_api::views(files, commands);
    let files = linkage_views.as_ref();
    let macro_lock_views = lock_macros::views(files, commands);
    let mut evidence = vec![CppEvidenceSet::default(); structs.len()];
    let mut index = EvidenceIndex::new(structs);
    let reference_returns = field_access::ReferenceReturns::collect(files, &index);
    index.reference_returns = std::cell::RefCell::new(reference_returns);
    let declaration_files = files
        .iter()
        .map(|file| (file.path.as_str(), file))
        .collect::<HashMap<_, _>>();
    for (owner, record) in structs.iter().enumerate() {
        if declaration_files
            .get(record.file.as_str())
            .is_some_and(|file| field_access::record_construction_is_inert(file, record))
        {
            index.inert_value_records.insert(owner);
        }
    }
    let included_globals = directly_included_record_globals(files, &index);
    let initialization =
        super::initialization::collect_initialization_facts_with_commands(files, commands);
    let mut execution_roles = execution_roles::Builder::default();
    let mut inline_methods = Vec::new();
    let mut inline_precision_by_file = HashMap::new();
    for (record_idx, record) in structs.iter().enumerate() {
        collect_api_evidence_for_struct(record_idx, record, &mut evidence);
    }

    for file in files {
        let mut concurrent_lines = concurrent_context_lines(file);
        let concurrent_call_paths = if concurrent_lines.is_empty() {
            HashMap::new()
        } else {
            field_access::propagate_shared_method_context(file, &index, &mut concurrent_lines)
        };
        let mut variable_types = included_globals
            .get(&file.path)
            .cloned()
            .unwrap_or_default();
        for (name, candidates) in collect_variable_types(file, &index) {
            variable_types.insert(name, candidates);
        }
        let implicit_records = collect_implicit_record_lines(file, &index);
        let declaration_lines = field_declaration_lines(file);
        let initialization_ranges = initialization
            .get(&file.path)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let syntax_accesses =
            field_access::collect(file, &index, &variable_types, initialization_ranges);
        let wait_receivers = bound_condition_variable_waits(file, &index, &syntax_accesses);
        let mut locksets_by_line = collect_scoped_locksets_with_waits(file, &wait_receivers);
        if let Some(view) = macro_lock_views.get(&file.path) {
            let globals = global_scalar_mutex_names(view);
            // The transformed view is only a lock proof. Its byte offsets and
            // synthetic releases must not enter ordinary access extraction.
            // No condition-wait restoration is inferred across rewritten bytes.
            for (line, guards) in collect_scoped_locksets(view) {
                let added = guards
                    .into_iter()
                    .filter(|guard| {
                        globals
                            .get(guard)
                            .is_some_and(|ranges| ranges.iter().any(|range| range.contains(&line)))
                    })
                    .map(|guard| format!("cpp_global_mutex:{}:{guard}", file.path));
                locksets_by_line.entry(line).or_default().extend(added);
            }
        }
        let shared_reachable_variables =
            collect_shared_ownership_evidence(file, &index, &concurrent_lines, &mut evidence);
        let access_context = FieldAccessContext {
            variable_types: &variable_types,
            implicit_records: &implicit_records,
            declaration_lines: &declaration_lines,
            concurrent_lines: &concurrent_lines,
            concurrent_call_paths: &concurrent_call_paths,
            locksets_by_line: &locksets_by_line,
            shared_reachable_variables: &shared_reachable_variables,
        };
        collect_type_usage_evidence(file, &index, &mut evidence);
        let syntax_accesses = collect_field_access_evidence(
            file,
            &index,
            &access_context,
            &mut evidence,
            syntax_accesses,
        );
        // The condition variable's own wait operation is not continuously
        // protected by the mutex that wait releases. Line-based predicate
        // guards must not accidentally protect that receiver on the same line.
        // Keep this conservative for additional outer guards too.
        for (record, line, field) in &wait_receivers.receiver_accesses {
            for item in &mut evidence[*record].items {
                if item.file == file.path
                    && item.line == *line
                    && item.field_name.as_ref() == Some(field)
                {
                    item.guard_ids.clear();
                }
            }
        }
        execution_roles.collect_file(file, &index, &syntax_accesses, &locksets_by_line);
        let (file_methods, file_precision) =
            collect_inline_methods_for_file(file, &index, &syntax_accesses, &evidence);
        inline_methods.extend(file_methods);
        if !file_precision.records.is_empty() || !file_precision.bound_receivers.is_empty() {
            inline_precision_by_file.insert(file.path.clone(), file_precision);
        }
        collect_object_storage_evidence(file, &index, &mut evidence);
    }

    index
        .reference_returns
        .borrow()
        .remove_address_only_reads(&mut evidence);
    propagate_inline_member_updates(
        files,
        structs,
        &index,
        &mut evidence,
        &inline_methods,
        &inline_precision_by_file,
    );
    execution_roles.finish(structs, &mut evidence);
    evidence
}

/// Bind externally declared objects through the actual direct include edge.
/// A unique spelling elsewhere in the project is insufficient: unrelated
/// headers, ambiguous include basenames and local shadows must not donate a
/// record identity. Lexical declarations still take precedence in field_access.
fn directly_included_record_globals(
    files: &[ParsedCppFile],
    index: &EvidenceIndex<'_>,
) -> HashMap<String, HashMap<String, Vec<usize>>> {
    let mut by_path = HashMap::new();
    let mut by_name: HashMap<String, Vec<usize>> = HashMap::new();
    let mut declarations = Vec::with_capacity(files.len());
    for (file_idx, file) in files.iter().enumerate() {
        by_path.insert(std::path::PathBuf::from(&file.path), file_idx);
        if let Some(name) = std::path::Path::new(&file.path).file_name() {
            by_name
                .entry(name.to_string_lossy().into_owned())
                .or_default()
                .push(file_idx);
        }
        let mut globals: HashMap<String, Vec<usize>> = HashMap::new();
        if let Some(tree) = &file.tree {
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() != "declaration" {
                    return;
                }
                let text = node_text(node, &file.source);
                if !identifier_tokens(text).any(|word| word == "extern")
                    || identifier_tokens(text)
                        .any(|word| matches!(word, "thread_local" | "__thread"))
                {
                    return;
                }
                let mut ancestor = node.parent();
                while let Some(scope) = ancestor {
                    if !matches!(
                        scope.kind(),
                        "translation_unit"
                            | "preproc_if"
                            | "preproc_ifdef"
                            | "preproc_else"
                            | "preproc_elif"
                            | "linkage_specification"
                            | "declaration_list"
                    ) {
                        return;
                    }
                    ancestor = scope.parent();
                }
                let Some(ty) = node.child_by_field_name("type") else {
                    return;
                };
                let type_text = node_text(ty, &file.source);
                let mut records = identifier_tokens(type_text)
                    .filter_map(|name| index.unambiguous_record_index(name, &file.path))
                    .collect::<HashSet<_>>();
                if type_text.contains("::") {
                    let qualified = type_text.split_whitespace().collect::<String>();
                    records.retain(|idx| {
                        index.record(*idx).qualified_name.trim_start_matches("::")
                            == qualified.trim_start_matches("::")
                    });
                }
                let mut cursor = node.walk();
                for declarator in node.children_by_field_name("declarator", &mut cursor) {
                    if let Some(name) = declarator_variable_name(declarator, &file.source) {
                        // Unknown declarations block a conflicting typed one.
                        let candidates = globals.entry(name).or_default();
                        candidates.extend(records.iter().copied());
                        if records.len() != 1 {
                            candidates.push(usize::MAX);
                        }
                    }
                }
            });
        }
        declarations.push(globals);
    }
    let mut result = HashMap::new();
    for file in files {
        let mut globals: HashMap<String, Vec<usize>> = HashMap::new();
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "preproc_include" {
                return;
            }
            let Some(path) = node.child_by_field_name("path") else {
                return;
            };
            let text = node_text(path, &file.source);
            let name = text.trim_matches(['"', '<', '>']);
            if name == text {
                return;
            }
            let local = std::path::Path::new(&file.path)
                .parent()
                .unwrap_or(std::path::Path::new(""))
                .join(name);
            let selected = by_path.get(&local).copied().or_else(|| {
                let basename = std::path::Path::new(name).file_name()?.to_str()?;
                let matches = by_name
                    .get(basename)?
                    .iter()
                    .copied()
                    .filter(|idx| std::path::Path::new(&files[*idx].path).ends_with(name))
                    .collect::<Vec<_>>();
                (matches.len() == 1).then(|| matches[0])
            });
            if let Some(selected) = selected {
                for (name, candidates) in &declarations[selected] {
                    globals.entry(name.clone()).or_default().extend(candidates);
                }
            }
        });
        for candidates in globals.values_mut() {
            candidates.sort_unstable();
            candidates.dedup();
            if candidates.contains(&usize::MAX) {
                candidates.clear();
            }
        }
        if !globals.is_empty() {
            result.insert(file.path.clone(), globals);
        }
    }
    result
}

#[derive(Clone)]
struct InlineMethod {
    owner: usize,
    name: String,
    file: String,
    begin_line: usize,
    end_line: usize,
    body_start_byte: usize,
    body_end_byte: usize,
    lambda_ranges: Vec<(usize, usize)>,
    lambda_byte_ranges: Vec<(usize, usize)>,
}

#[derive(Default)]
struct InlineSyntaxPrecision {
    // Exact expression binding before evidence compaction. A read elsewhere
    // on the same source line must not authorize this receiver's call.
    bound_receivers: HashSet<(usize, usize, String)>,
    records: HashSet<usize>,
    effects: HashMap<(usize, String, usize, usize), (CppAccessKind, usize)>,
}

fn collect_inline_methods_for_file(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    syntax_accesses: &HashMap<usize, Vec<field_access::SyntaxAccess>>,
    evidence: &[CppEvidenceSet],
) -> (Vec<InlineMethod>, InlineSyntaxPrecision) {
    let mut methods = Vec::new();
    let Some(tree) = &file.tree else {
        return (methods, InlineSyntaxPrecision::default());
    };
    let mut precision = InlineSyntaxPrecision::default();
    let mut candidate_methods = HashSet::new();
    let mut candidate_method_names = HashSet::new();
    for access in syntax_accesses.values().flatten() {
        let Some(function) = access.function.as_ref() else {
            continue;
        };
        if access.initialization
            || access.thread_local
            || access.nonescaping_local
            || access
                .receiver
                .as_deref()
                .is_some_and(|receiver| receiver != "this")
        {
            continue;
        }
        candidate_methods.insert((access.record, function.clone()));
        candidate_method_names.insert(function.clone());
    }
    for (owner, evidence_set) in evidence.iter().enumerate() {
        for item in &evidence_set.items {
            let (Some(function), Some(_field), Some(_kind)) = (
                item.function_name.as_ref(),
                item.field_name.as_ref(),
                item.access_kind.as_ref(),
            ) else {
                continue;
            };
            if item.initialization_phase
                || item.through_thread_local
                || item.through_nonescaping_local
            {
                continue;
            }
            candidate_methods.insert((owner, function.clone()));
            candidate_method_names.insert(function.clone());
        }
    }
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "call_expression"
            && let Some(method) = node.child_by_field_name("function")
            && method.kind() == "field_expression"
            && method
                .child_by_field_name("operator")
                .is_some_and(|op| node_text(op, &file.source) == ".")
            && let Some(receiver) = method.child_by_field_name("argument")
            && matches!(receiver.kind(), "identifier" | "field_expression")
        {
            for access in syntax_accesses
                .get(&(receiver.start_position().row + 1))
                .into_iter()
                .flatten()
            {
                if access.start_byte == receiver.start_byte()
                    && !access.contiguous_element
                    && access.kind == CppAccessKind::Read
                {
                    precision.bound_receivers.insert((
                        access.start_byte,
                        access.record,
                        access.field.clone(),
                    ));
                }
            }
        }

        if node.kind() != "function_definition" {
            return;
        }
        let Some(name) = function_definition_name(node, file) else {
            return;
        };
        let method_name = name.rsplit("::").next().unwrap_or(&name).to_owned();
        if !candidate_method_names.contains(&method_name) {
            return;
        }
        let (Some(owner), Some(body)) = (
            field_access::function_owner(node, file, index),
            node.child_by_field_name("body"),
        ) else {
            return;
        };
        if !candidate_methods.contains(&(owner, method_name.clone()))
            && !evidence[owner]
                .items
                .iter()
                .any(|item| item.function_name.as_deref() == Some(method_name.as_str()))
        {
            return;
        }
        let mut lambda_ranges = Vec::new();
        let mut lambda_byte_ranges = Vec::new();
        walk_nodes(body, &mut |nested| {
            if nested.kind() == "lambda_expression" {
                lambda_ranges.push((
                    nested.start_position().row + 1,
                    nested.end_position().row + 1,
                ));
                lambda_byte_ranges.push((nested.start_byte(), nested.end_byte()));
            }
        });
        methods.push(InlineMethod {
            owner,
            name: method_name,
            file: file.path.clone(),
            begin_line: body.start_position().row + 1,
            end_line: body.end_position().row + 1,
            body_start_byte: body.start_byte(),
            body_end_byte: body.end_byte(),
            lambda_ranges,
            lambda_byte_ranges,
        });
    });
    let mut latest_method_end = HashMap::new();
    for method in &methods {
        if evidence[method.owner].truncated_items > 0 {
            precision.records.insert(method.owner);
        }
        let key = (method.owner, method.name.clone());
        if latest_method_end
            .get(&key)
            .is_some_and(|latest_end| method.begin_line <= *latest_end)
        {
            precision.records.insert(method.owner);
        }
        latest_method_end
            .entry(key)
            .and_modify(|latest_end| *latest_end = (*latest_end).max(method.end_line))
            .or_insert(method.end_line);
    }
    if precision.records.is_empty() {
        return (methods, precision);
    }

    let mut accesses_by_method = HashMap::new();
    for accesses in syntax_accesses.values() {
        for access in accesses {
            if !precision.records.contains(&access.record) || access.start_byte == 0 {
                continue;
            }
            let Some(function) = access.function.as_ref() else {
                continue;
            };
            accesses_by_method
                .entry((access.record, function.clone()))
                .or_insert_with(Vec::new)
                .push(access);
        }
    }
    for method in &methods {
        if !precision.records.contains(&method.owner) {
            continue;
        }
        let Some(accesses) = accesses_by_method.get(&(method.owner, method.name.clone())) else {
            continue;
        };
        let mut effect = None;
        let mut effect_line = None;
        for access in accesses {
            if access.start_byte < method.body_start_byte
                || access.start_byte >= method.body_end_byte
                || access.initialization
                || access.contiguous_element
                || access.thread_local
                || access.nonescaping_local
                || access
                    .receiver
                    .as_deref()
                    .is_some_and(|receiver| receiver != "this")
                || method
                    .lambda_byte_ranges
                    .iter()
                    .any(|(begin, end)| (*begin..*end).contains(&access.start_byte))
            {
                continue;
            }
            if effect.as_ref().is_none_or(|existing| {
                access_kind_strength(&access.kind) > access_kind_strength(existing)
            }) {
                effect = Some(access.kind.clone());
                effect_line = Some(
                    file.source[..access.start_byte.min(file.source.len())]
                        .bytes()
                        .filter(|byte| *byte == b'\n')
                        .count()
                        + 1,
                );
            }
        }
        if let (Some(effect), Some(line)) = (effect, effect_line) {
            precision.effects.insert(
                (
                    method.owner,
                    method.name.clone(),
                    method.body_start_byte,
                    method.body_end_byte,
                ),
                (effect, line),
            );
        }
    }
    (methods, precision)
}

/// One-hop effect specialization for an inline subobject. Only a resolved
/// member callable with a concrete access in its own body supplies the effect;
/// names such as Ref/update and the presence of an atomic type are insufficient.
fn propagate_inline_member_updates(
    files: &[ParsedCppFile],
    records: &[CppStructInfo],
    index: &EvidenceIndex<'_>,
    evidence: &mut [CppEvidenceSet],
    methods: &[InlineMethod],
    precision_by_file: &HashMap<String, InlineSyntaxPrecision>,
) {
    if methods.is_empty() {
        return;
    }
    let source_by_path = files
        .iter()
        .map(|file| (file.path.as_str(), file.source.as_str()))
        .collect::<HashMap<_, _>>();

    // Raw syntax facts were summarized before the per-record evidence budget
    // evicted their presentation items. A missing syntax effect falls back
    // to the retained evidence for conservative compatibility.
    let mut summaries = HashMap::<(usize, String), (Vec<(String, usize)>, CppAccessKind)>::new();
    let mut unresolved = HashSet::new();
    for method in methods {
        let precise_owner = precision_by_file
            .get(&method.file)
            .is_some_and(|precision| precision.records.contains(&method.owner));
        let mut effect = None;
        let mut effect_line = None;
        if precise_owner {
            if let Some((kind, line)) = precision_by_file.get(&method.file).and_then(|precision| {
                precision.effects.get(&(
                    method.owner,
                    method.name.clone(),
                    method.body_start_byte,
                    method.body_end_byte,
                ))
            }) {
                effect = Some(kind.clone());
                effect_line = Some(*line);
            }
        } else {
            for access in evidence[method.owner].items.iter() {
                if access.file != method.file
                    || access.function_name.as_deref() != Some(method.name.as_str())
                    || access.line < method.begin_line
                    || access.line > method.end_line
                    || access.initialization_phase
                    || access.kind == CppEvidenceKind::ContiguousElementAccess
                    || access.through_thread_local
                    || access.through_nonescaping_local
                    || method
                        .lambda_ranges
                        .iter()
                        .any(|(begin, end)| (*begin..=*end).contains(&access.line))
                {
                    continue;
                }
                let Some(field) = access.field_name.as_deref() else {
                    continue;
                };
                let Some(kind) = access.access_kind.as_ref() else {
                    continue;
                };
                if !line_access_is_self_bound(
                    source_by_path
                        .get(method.file.as_str())
                        .and_then(|source| source.lines().nth(access.line.saturating_sub(1)))
                        .unwrap_or(""),
                    field,
                ) {
                    continue;
                }
                if effect.as_ref().is_none_or(|existing| {
                    access_kind_strength(kind) > access_kind_strength(existing)
                }) {
                    effect = Some(kind.clone());
                    effect_line = Some(access.line);
                }
            }
        }
        let key = (method.owner, method.name.clone());
        let Some(effect) = effect else {
            unresolved.insert(key);
            continue;
        };
        let origin = (
            method.file.clone(),
            effect_line.unwrap_or(method.begin_line),
        );
        if let Some((origins, common)) = summaries.get_mut(&key) {
            if *common != effect {
                if *common != CppAccessKind::Read && effect != CppAccessKind::Read {
                    *common = CppAccessKind::Write;
                } else {
                    unresolved.insert(key.clone());
                }
            }
            origins.push(origin);
        } else {
            summaries.insert(key, (vec![origin], effect));
        }
    }
    summaries.retain(|key, _| !unresolved.contains(key));
    if summaries.is_empty() {
        return;
    }

    let method_names = summaries
        .keys()
        .map(|(_, name)| name.as_str())
        .collect::<HashSet<_>>();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        // Avoid a second full tree walk for files that cannot contain one of
        // the resolved member calls. This lexical prefilter is permissive:
        // comments and strings may cause extra work, but no real call is
        // discarded because whitespace between '.', the name, and '(' is
        // accepted.
        if !source_has_named_member_call(&file.source, &method_names) {
            continue;
        }
        let lexical_bindings = collect_lexical_binding_ranges(file);
        walk_nodes(tree.root_node(), &mut |call| {
            if call.kind() != "call_expression" {
                return;
            }
            let Some(method) = call
                .child_by_field_name("function")
                .filter(|n| n.kind() == "field_expression")
            else {
                return;
            };
            if method
                .child_by_field_name("operator")
                .is_none_or(|op| node_text(op, &file.source) != ".")
            {
                return;
            }
            let (Some(receiver), Some(method_name)) = (
                method.child_by_field_name("argument"),
                method.child_by_field_name("field"),
            ) else {
                return;
            };
            if !matches!(receiver.kind(), "field_expression" | "identifier") {
                return;
            }
            let member = if receiver.kind() == "identifier" {
                receiver
            } else {
                let Some(member) = receiver.child_by_field_name("field") else {
                    return;
                };
                member
            };
            let member = node_text(member, &file.source);
            let method_name = node_text(method_name, &file.source);
            if !method_names.contains(method_name) {
                return;
            }
            if receiver.kind() == "identifier"
                && receiver_is_lexically_bound(call, receiver, &file.source, &lexical_bindings)
            {
                return;
            }
            let line = receiver.start_position().row + 1;
            for &outer in index.records_by_field.get(member).into_iter().flatten() {
                if !precision_by_file.get(&file.path).is_some_and(|precision| {
                    precision.bound_receivers.contains(&(
                        receiver.start_byte(),
                        outer,
                        member.to_owned(),
                    ))
                }) {
                    continue;
                }
                let occurrences = evidence[outer]
                    .items
                    .iter()
                    .filter(|item| {
                        item.file == file.path
                            && item.line == line
                            && item.field_name.as_deref() == Some(member)
                            && item.access_kind == Some(CppAccessKind::Read)
                            && item.kind != CppEvidenceKind::ContiguousElementAccess
                    })
                    .count();
                // A method effect describes the callee, not the receiver at
                // this call. Require an existing bound access to this outer
                // object; a same-spelled member in another record is not an
                // alias. Missing/budget-evicted access facts stay unresolved.
                if occurrences != 1 {
                    continue;
                }
                let Some(field) = records[outer]
                    .fields
                    .iter()
                    .find(|field| field.name == member && !field.is_indirect && !field.is_array)
                else {
                    continue;
                };
                let type_name = field
                    .ty_str
                    .split('<')
                    .next()
                    .unwrap_or(&field.ty_str)
                    .trim()
                    .trim_start_matches("const ")
                    .trim_start_matches("struct ")
                    .trim_start_matches("class ")
                    .trim();
                let owner = if type_name.contains("::") {
                    let matches = index
                        .record_indices_for_name(type_name.rsplit("::").next().unwrap_or(type_name))
                        .into_iter()
                        .flatten()
                        .copied()
                        .filter(|candidate| {
                            records[*candidate].qualified_name.trim_start_matches("::")
                                == type_name.trim_start_matches("::")
                        })
                        .collect::<Vec<_>>();
                    if matches.len() == 1 {
                        Some(matches[0])
                    } else {
                        None
                    }
                } else {
                    index.unambiguous_record_index(type_name, &records[outer].file)
                };
                let Some(owner) = owner else { continue };
                let Some((origins, effect)) = summaries.get(&(owner, method_name.to_owned()))
                else {
                    continue;
                };
                let facts = &mut evidence[outer];
                for access in facts.items.iter_mut().filter(|access| {
                    access.file == file.path
                        && access.line == line
                        && access.field_name.as_deref() == Some(member)
                        && access.access_kind == Some(CppAccessKind::Read)
                }) {
                    access.access_kind = Some(effect.clone());
                    access.kind = CppEvidenceKind::InlineMemberAccess;
                    access.description.push_str(&format!(
                        "; 内联子对象方法 {}::{} 各已解析重载的共同 {:?} 效应来自 {}",
                        records[owner].name,
                        method_name,
                        effect,
                        origins
                            .iter()
                            .map(|(file, line)| format!("{file}:{line}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }
            }
        });
    }
}

fn source_has_named_member_call(source: &str, names: &HashSet<&str>) -> bool {
    let bytes = source.as_bytes();
    let mut offset = 0usize;
    while let Some(relative) = source[offset..].find('.') {
        let dot = offset + relative;
        let mut cursor = dot + 1;
        while bytes
            .get(cursor)
            .is_some_and(|byte| byte.is_ascii_whitespace())
        {
            cursor += 1;
        }
        let start = cursor;
        if bytes
            .get(cursor)
            .is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_')
        {
            cursor += 1;
            while bytes
                .get(cursor)
                .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
            {
                cursor += 1;
            }
            let name = &source[start..cursor];
            while bytes
                .get(cursor)
                .is_some_and(|byte| byte.is_ascii_whitespace())
            {
                cursor += 1;
            }
            if bytes.get(cursor) == Some(&b'(') && names.contains(name) {
                return true;
            }
        }
        offset = dot + 1;
    }
    false
}

/// A bare receiver can be either an implicit member or a local object with
/// the same spelling. The ordinary field-access pass resolves this through
/// lexical bindings; the bounded call-site recovery must preserve that
/// distinction when the receiver item was evicted by the evidence budget.
fn receiver_is_lexically_bound(
    call: tree_sitter::Node<'_>,
    receiver: tree_sitter::Node<'_>,
    source: &str,
    bindings: &HashMap<String, Vec<(usize, usize, usize)>>,
) -> bool {
    let name = node_text(receiver, source);
    let call_start = call.start_byte();
    bindings.get(name).is_some_and(|ranges| {
        ranges.iter().any(|(declaration, begin, end)| {
            *declaration <= call_start && *begin <= call_start && call_start < *end
        })
    })
}

fn collect_lexical_binding_ranges(
    file: &ParsedCppFile,
) -> HashMap<String, Vec<(usize, usize, usize)>> {
    let mut bindings = HashMap::new();
    let Some(tree) = &file.tree else {
        return bindings;
    };
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(
            node.kind(),
            "declaration" | "parameter_declaration" | "optional_parameter_declaration"
        ) {
            return;
        }
        let scope = field_access::binding_scope(node);
        let mut cursor = node.walk();
        for declarator in node.children_by_field_name("declarator", &mut cursor) {
            let Some(name) = declarator_variable_name(declarator, &file.source) else {
                continue;
            };
            bindings.entry(name).or_insert_with(Vec::new).push((
                node.start_byte(),
                scope.start_byte(),
                scope.end_byte(),
            ));
        }
    });
    bindings
}

fn line_access_is_self_bound(line: &str, field: &str) -> bool {
    let accesses = field_access_tokens(line)
        .into_iter()
        .filter(|(_, name)| *name == field)
        .collect::<Vec<_>>();
    if accesses.is_empty() {
        return true;
    }
    !accesses
        .iter()
        .any(|(receiver, _)| receiver.is_some_and(|receiver| receiver != "this"))
}

struct EvidenceIndex<'a> {
    records: &'a [CppStructInfo],
    records_by_name: HashMap<&'a str, Vec<usize>>,
    records_by_field: HashMap<&'a str, Vec<usize>>,
    records_by_file_name: HashMap<&'a str, HashMap<&'a str, Vec<usize>>>,
    inert_value_records: HashSet<usize>,
    reference_returns: std::cell::RefCell<field_access::ReferenceReturns>,
}

struct FieldAccessContext<'a> {
    variable_types: &'a HashMap<String, Vec<usize>>,
    implicit_records: &'a HashMap<usize, usize>,
    declaration_lines: &'a HashSet<usize>,
    concurrent_lines: &'a HashSet<usize>,
    concurrent_call_paths: &'a HashMap<usize, Vec<String>>,
    locksets_by_line: &'a HashMap<usize, Vec<String>>,
    shared_reachable_variables: &'a HashSet<String>,
}

impl<'a> EvidenceIndex<'a> {
    fn new(records: &'a [CppStructInfo]) -> Self {
        let mut records_by_name: HashMap<&'a str, Vec<usize>> = HashMap::new();
        let mut records_by_field: HashMap<&'a str, Vec<usize>> = HashMap::new();
        let mut records_by_file_name: HashMap<&'a str, HashMap<&'a str, Vec<usize>>> =
            HashMap::new();
        for (idx, record) in records.iter().enumerate() {
            records_by_name
                .entry(record.name.as_str())
                .or_default()
                .push(idx);
            records_by_file_name
                .entry(record.file.as_str())
                .or_default()
                .entry(record.name.as_str())
                .or_default()
                .push(idx);
            for field in &record.fields {
                records_by_field
                    .entry(field.name.as_str())
                    .or_default()
                    .push(idx);
            }
        }

        Self {
            inert_value_records: HashSet::new(),
            reference_returns: std::cell::RefCell::default(),
            records,
            records_by_name,
            records_by_field,
            records_by_file_name,
        }
    }

    fn record(&self, idx: usize) -> &'a CppStructInfo {
        &self.records[idx]
    }

    fn record_indices_for_name(&self, name: &str) -> Option<&[usize]> {
        self.records_by_name.get(name).map(Vec::as_slice)
    }

    fn unambiguous_record_index(&self, name: &str, usage_file: &str) -> Option<usize> {
        let candidates = self.record_indices_for_name(name)?;
        if candidates.len() == 1 {
            return candidates.first().copied();
        }
        if let Some(local) = self
            .records_by_file_name
            .get(usage_file)
            .and_then(|records| records.get(name))
        {
            return (local.len() == 1).then_some(local[0]);
        }

        // Generated or vendored trees sometimes contain the same short record
        // name in independent submodules.  An out-of-line method should bind
        // to the declaration in its own directory when that choice is unique;
        // a project-wide short-name guess remains forbidden on ties.
        let usage_parent = Path::new(usage_file).parent()?;
        let mut ranked = candidates
            .iter()
            .map(|candidate| {
                let declaration_parent = Path::new(&self.records[*candidate].file).parent();
                let score = declaration_parent.map_or((false, 0), |parent| {
                    (
                        parent == usage_parent,
                        usage_parent
                            .components()
                            .zip(parent.components())
                            .take_while(|(left, right)| left == right)
                            .count(),
                    )
                });
                (*candidate, score)
            })
            .collect::<Vec<_>>();
        ranked.sort_unstable_by_key(|(_, score)| std::cmp::Reverse(*score));
        let (best, score) = *ranked.first()?;
        (score.1 > 0 && ranked.get(1).is_none_or(|(_, peer)| *peer < score)).then_some(best)
    }

    fn record_indices_for_field(&self, field: &str) -> Option<&[usize]> {
        self.records_by_field.get(field).map(Vec::as_slice)
    }

    fn is_known_field(&self, field: &str) -> bool {
        self.records_by_field.contains_key(field)
    }
}

pub fn collect_indexed_write_candidates(
    files: &[ParsedCppFile],
    structs: &[CppStructInfo],
    cache_line_size: usize,
) -> Vec<IndexedWriteCandidate> {
    collect_indexed_write_candidates_with_commands(files, structs, cache_line_size, &[])
}

pub(super) fn collect_indexed_write_candidates_with_commands(
    files: &[ParsedCppFile],
    structs: &[CppStructInfo],
    cache_line_size: usize,
    commands: &[super::types::CppCompileCommand],
) -> Vec<IndexedWriteCandidate> {
    let runtime_views = super::unevaluated::views(files, commands);
    let files = runtime_views.as_ref();
    let linkage_views = internal_index_api::views(files, commands);
    let files = linkage_views.as_ref();
    let lock_views = lock_macros::views(files, commands);
    let storage_index = storage_identity::StorageIndex::new(files);
    let mut candidates = Vec::new();
    let fresh_indexed =
        super::initialization::collect_fresh_indexed_accesses_with_commands(files, commands);
    let alignment_macros = super::initialization::alignment_macro_visibility(files);
    let memory_arguments = super::initialization::discarded_memory_arguments(files, commands);
    let mut ordinary_callees = HashSet::new();
    for file in files {
        if let Some(tree) = &file.tree {
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() == "call_expression"
                    && let Some(callee) = node.child_by_field_name("function")
                    && callee.kind() == "identifier"
                {
                    ordinary_callees.insert(node_text(callee, &file.source).to_owned());
                }
            });
        }
    }
    let atomic_indexed_mutators = collect_atomic_indexed_mutators(files);
    let ownership_index = EvidenceIndex::new(structs);
    let private_methods = declared_private_index_methods(files, structs);
    let indexed_accessor_summaries =
        indexed_accessors::Summaries::collect(files, &ownership_index, cache_line_size);
    let project_thread_local_symbols = files
        .iter()
        .flat_map(thread_local_symbols)
        .collect::<HashSet<_>>();
    // A field/array is commonly declared in a header and mutated in another
    // translation unit.  Keep the positive storage proof project-wide; the
    // access site still has to name the exact symbol and mutation target.
    let project_contiguous_symbols = files
        .iter()
        .flat_map(|file| collect_contiguous_indexed_symbols(file, false))
        .collect::<HashSet<_>>();
    let project_record_fields = structs
        .iter()
        .flat_map(|record| record.fields.iter().map(|field| field.name.clone()))
        .collect::<HashSet<_>>();
    let mut aligned_types: HashSet<String> = structs
        .iter()
        .filter(|record| record.is_cache_aligned || record.has_cache_padding)
        .map(|record| record.name.clone())
        .collect();
    aligned_types.extend(source_aligned_type_names(files, cache_line_size));
    discard_ambiguous_alignment_names(files, &mut aligned_types);
    let isolated_element_types = aligned_types
        .iter()
        .filter(|name| {
            // Internal padding alone is not a guarantee about the next object's
            // boundary. A recovered record must itself have type alignment.
            structs
                .iter()
                .filter(|record| record.name.as_str() == name.as_str())
                .all(|record| record.is_cache_aligned)
        })
        .cloned()
        .collect();
    let indexed_mutator_summaries = collect_indexed_mutator_summaries(
        files,
        &isolated_element_types,
        &ownership_index,
        &memory_arguments,
        &lock_views,
        &storage_index,
    );
    let mut aligned_records_by_file: HashMap<&str, Vec<&CppStructInfo>> = HashMap::new();
    for record in structs
        .iter()
        .filter(|record| record.is_cache_aligned || record.has_cache_padding)
    {
        aligned_records_by_file
            .entry(record.file.as_str())
            .or_default()
            .push(record);
    }
    let descriptor_annotations = partition_descriptors::DeclarationAnnotations::collect(files);
    let callback_integer_aliases = returned_callbacks::integer_aliases(files);
    for file in files {
        let lines: Vec<&str> = file.source.lines().collect();
        let storage_aliases = ScopedIndexedAliases::collect(file, true);
        let member_aliases = ScopedIndexedAliases::collect(file, false);
        let functions = collect_function_regions(file);
        // A pthread callback is an execution domain in its own right.  Some
        // C/POSIX benchmarks pass the worker slot through a global/local
        // integer or a member of the callback argument instead of calling a
        // recognizable runtime identity intrinsic. Keep the callback names
        // so an indexed mutation can recover that bounded worker partition
        // without treating every loop inside an arbitrary parallel region as
        // independently selected storage.
        let pthread_worker_names = call_argument_lists(&file.source, "pthread_create")
            .into_iter()
            .filter_map(|arguments| {
                arguments
                    .get(2)
                    .and_then(|argument| callable_identifier(argument))
            })
            .collect::<HashSet<_>>();
        let local_callable_shadows = static_access_local_shadows(file);
        let bound_summary_calls = indexed_summary_calls::collect(file, &ownership_index);
        let serial_spawn_assignments =
            spawn_setup::serial_indexed_assignments(file, &ownership_index, &private_methods);
        let atomic_aliases = bound_indexed_atomic_aliases(file);
        let descriptor_fields = descriptor_annotations.api_fields(file);
        let mut index_origins =
            collect_index_partition_origins_with_descriptors(file, &functions, &descriptor_fields);
        returned_callbacks::seed(
            file,
            &callback_integer_aliases,
            &ownership_index,
            &mut index_origins,
        );
        remove_private_api_partition_seeds(
            file,
            &ownership_index,
            &private_methods,
            &mut index_origins,
        );
        propagate_tls_api_partitions(file, &functions, &mut index_origins);
        let array_declarations = array_declaration_sites(file);
        let inline_array_rows = inline_array_row_bindings(file);
        let bpf_array_maps = bpf_array_map_symbols(file);
        let bpf_writes = bpf_calls::collect(file);
        let bpf_separated = bpf_layout::separated_accesses(file, cache_line_size);
        let concurrent_lines = concurrent_context_lines(file);
        let mut locksets_by_line = collect_scoped_locksets(file);
        if let Some(view) = lock_views.get(&file.path) {
            let globals = global_scalar_mutex_names(view);
            for (line, guards) in collect_scoped_locksets(view) {
                let added = guards.into_iter().filter(|g| {
                    globals
                        .get(g)
                        .is_some_and(|ranges| ranges.iter().any(|range| range.contains(&line)))
                });
                locksets_by_line.entry(line).or_default().extend(added);
            }
        }
        candidates.extend(indexed_accessor_summaries.candidates(
            file,
            &ownership_index,
            &index_origins,
            &functions,
            &locksets_by_line,
        ));
        let mut contiguous_symbols = contiguous_indexed_symbols(file);
        let local_noncontiguous_uses = unproved_local_index_storage(file);
        let mut unproved_member_uses = None;
        let pointee_only_accesses = indexed_storage::pointee_only_accesses(file);
        contiguous_symbols.extend(project_contiguous_symbols.iter().cloned());
        contiguous_symbols.extend(
            storage_aliases
                .bindings
                .iter()
                .filter(|(_, _, _, target)| {
                    target
                        .as_ref()
                        .is_some_and(|name| project_contiguous_symbols.contains(name))
                })
                .map(|(name, _, _, _)| name.clone()),
        );
        let non_contiguous_symbols = non_contiguous_indexed_symbols(file);
        let thread_local_symbols = thread_local_symbols(file);
        let protected_symbols = protected_indexed_symbols(&lines, &aligned_types);
        let header_protected_symbols =
            visible_isolated_extern_arrays(files, file, &isolated_element_types);
        let aligned_receiver_fields = cache_aligned_receiver_fields(
            file,
            aligned_records_by_file
                .get(file.path.as_str())
                .map(Vec::as_slice)
                .unwrap_or_default(),
        );
        for (idx, line) in lines.iter().enumerate() {
            for (callee, mutated_fields) in &indexed_mutator_summaries {
                // A same-spelled local callable cannot borrow a free
                // function's mutation summary. Keep qualified/mixed lines
                // conservative until individual call spans are attached.
                if !line.contains(['.', ':'])
                    && !line.contains("->")
                    && (local_callable_shadows.get(callee).is_some_and(|ranges| {
                        ranges
                            .iter()
                            .any(|(begin, end, _)| *begin < idx + 1 && idx + 1 < *end)
                    }) || functions.iter().any(|function| {
                        function.body_start_line <= idx + 1
                            && idx < function.body_end_line
                            && function_parameters(function)
                                .iter()
                                .any(|name| name == callee)
                    }))
                {
                    continue;
                }
                let calls = call_argument_lists(line, callee);
                if calls.is_empty() {
                    continue;
                }
                if callable_name(line).is_some_and(|name| name == *callee) && line.contains('{') {
                    continue;
                }
                for (field, summary) in mutated_fields {
                    let Some(bound_calls) =
                        bound_summary_calls.get(&(idx + 1, callee.clone(), summary.owner))
                    else {
                        continue;
                    };
                    let partitioned_call = bound_calls.iter().any(|arguments| {
                        summary.parameters.iter().any(|position| {
                            let Some(argument) = arguments.get(*position) else {
                                return false;
                            };
                            index_origins.supports_parallel_argument(argument, idx + 1)
                                || ((concurrent_lines.contains(&(idx + 1))
                                    || atomic_indexed_mutators.contains(&(
                                        callee.clone(),
                                        field.clone(),
                                        *position,
                                    )))
                                    && functions.iter().any(|function| {
                                        function.body_start_line <= idx + 1
                                            && idx < function.body_end_line
                                            && function_parameters(function)
                                                .iter()
                                                .any(|parameter| argument.trim() == parameter)
                                    }))
                        })
                    });
                    if !partitioned_call {
                        continue;
                    }
                    if let Some(owner) = summary.owner
                        && index_origins
                            .parallel_inductions
                            .iter()
                            .any(|(start, end, _)| *start <= idx + 1 && idx < *end)
                        && !parallel_call_has_shared_receiver(
                            file,
                            callee,
                            idx + 1,
                            owner,
                            &ownership_index,
                            &index_origins,
                        )
                    {
                        continue;
                    }
                    if !project_contiguous_symbols.contains(field)
                        || project_thread_local_symbols.contains(field)
                    {
                        continue;
                    }
                    candidates.push(IndexedWriteCandidate {
                        file: file.path.clone(),
                        line: idx + 1,
                        snippet: line.trim().to_string(),
                        function_name: enclosing_function_name(&functions, idx + 1),
                        record_name: None,
                        record_line: None,
                    record_peer: None,
                    record_storage: None,
                        field_name: Some(field.clone()),
                        alias_name: None,
                        access_kind: summary.kind.clone(),
                        has_direct_partition_evidence: true,
                        access_in_concurrent_context: concurrent_lines.contains(&(idx + 1)),
                        guard_ids: locksets_by_line.get(&(idx + 1)).into_iter().flatten()
                            .chain(summary.guard_ids.iter()).cloned().collect(),
                        evidence: vec![
                            format!("过程间写证据: 被调函数 '{callee}' 写入连续字段 '{field}[partition]'{}", if summary.kind == CppAccessKind::Write { " [plain-store-summary]" } else { "" }),
                            "调用点证据: 实参追溯至 worker partition 或位于并行区域".to_string(),
                            "布局证据: 被写元素类型未证明为 cache-line padded".to_string(),
                        ],
                        storage_identity: summary.storage_identity.clone(),
                    });
                }
            }
            for (callee, summary) in &bpf_writes {
                for arguments in call_argument_lists(line, callee) {
                    if arguments.len() <= summary.map_argument.max(summary.key_argument) {
                        continue;
                    }
                    let Some(map) = identifier_tokens(&arguments[summary.map_argument]).last()
                    else {
                        continue;
                    };
                    let index_expression = arguments[summary.key_argument]
                        .trim()
                        .trim_start_matches('&');
                    if !bpf_array_maps.contains(map)
                        || !index_origins.supports(index_expression, idx + 1)
                        || bpf_separated.contains(&(idx + 1, map.to_string()))
                    {
                        continue;
                    }
                    candidates.push(IndexedWriteCandidate {
                        file: file.path.clone(),
                        line: idx + 1,
                        snippet: line.trim().to_string(),
                        function_name: enclosing_function_name(&functions, idx + 1),
                        record_name: None,
                        record_line: None,
                        record_peer: None,
                        record_storage: None,
                        field_name: Some(map.to_string()),
                        alias_name: None,
                        access_kind: summary.kind.clone(),
                        has_direct_partition_evidence: true,
                        access_in_concurrent_context: true,
                        guard_ids: Vec::new(),
                        evidence: vec![
                            "存储证据: BPF_MAP_TYPE_ARRAY 的值槽位按 key 连续存放".to_string(),
                            format!(
                                "分区证据: map key '{index_expression}' 追溯至 CPU/worker identity"
                            ),
                            "布局证据: 相邻 key 未按 cache-line 等效宽度拉开".to_string(),
                        ],
                        storage_identity: None,
                    });
                }
            }
            // Alias propagation starts at a binding/assignment.  Do not join a
            // function signature without a semicolon to the first statement in
            // its body: that used to turn a read-only indexed reference into a
            // synthetic alias rooted at the function name.
            let logical_statement = (line.contains('=') || line.contains("atomic_ref"))
                .then(|| logical_statement(&lines, idx, 6));
            let partitioned_alias = logical_statement
                .as_deref()
                .and_then(|statement| {
                    partitioned_region_alias(
                        statement,
                        &index_origins,
                        idx + 1,
                        concurrent_lines.contains(&(idx + 1)),
                        &inline_array_rows,
                    )
                })
                .or_else(|| atomic_aliases.get(&(idx + 1)).cloned());
            if let Some((storage, alias)) = partitioned_alias
                && (contiguous_symbols.contains(&storage)
                    || logical_statement
                        .as_deref()
                        .is_some_and(|statement| statement.contains(&format!("{storage}.at("))))
                && !protected_symbols.contains(&storage)
                && !thread_local_symbols.contains(&storage)
                && let Some(access_kind) = pointer_alias_mutation(&lines, idx, &alias, &functions)
            {
                let (field_name, storage_alias) =
                    if let Some(backing) = storage_aliases.resolve(&storage, idx + 1) {
                        (backing.clone(), Some(storage.clone()))
                    } else if project_record_fields.contains(&storage) {
                        (storage.clone(), None)
                    } else {
                        (
                            member_aliases
                                .resolve(&storage, idx + 1)
                                .cloned()
                                .unwrap_or_else(|| storage.clone()),
                            None,
                        )
                    };
                candidates.push(IndexedWriteCandidate {
                    file: file.path.clone(),
                    line: idx + 1,
                    snippet: logical_statement
                        .as_deref()
                        .unwrap_or(line)
                        .trim()
                        .to_string(),
                    function_name: enclosing_function_name(&functions, idx + 1),
                    record_name: None,
                    record_line: None,
                    record_peer: None,
                    record_storage: None,
                    field_name: Some(field_name),
                    alias_name: storage_alias.or_else(|| Some(alias.clone())),
                    access_kind,
                    has_direct_partition_evidence: true,
                    access_in_concurrent_context: concurrent_lines.contains(&(idx + 1))
                        || partitioned_alias_has_runtime_identity(
                            logical_statement.as_deref().unwrap_or(line),
                            &index_origins,
                            idx + 1,
                        ),
                    guard_ids: locksets_by_line
                        .get(&(idx + 1))
                        .cloned()
                        .unwrap_or_default(),
                    evidence: vec![
                        format!(
                            "分区证据: 连续存储 '{}' 的元素/切片绑定到别名 '{}'",
                            storage, alias
                        ),
                        "写证据: 分区别名随后发生直接、原子或调用传播写入".to_string(),
                        "布局证据: 分区边界/元素 stride 未证明按 cache line 隔离".to_string(),
                    ],
                    storage_identity: None,
                });
                continue;
            }
            if let Some((storage, stride, alias)) =
                logical_statement.as_deref().and_then(|statement| {
                    partitioned_pointer_stride(statement, &index_origins, idx + 1)
                })
                && contiguous_symbols.contains(&storage)
                && let Some(access_kind) = pointer_alias_mutation(&lines, idx, &alias, &functions)
            {
                candidates.push(IndexedWriteCandidate {
                    file: file.path.clone(),
                    line: idx + 1,
                    snippet: logical_statement
                        .as_deref()
                        .unwrap_or(line)
                        .trim()
                        .to_string(),
                    function_name: enclosing_function_name(&functions, idx + 1),
                    record_name: None,
                    record_line: None,
                    record_peer: None,
                    record_storage: None,
                    // The stride is a read-only offset, not the storage being
                    // mutated through the partition pointer.
                    field_name: Some(storage.clone()),
                    alias_name: Some(alias.clone()),
                    access_kind,
                    has_direct_partition_evidence: true,
                    access_in_concurrent_context: index_origins.supports_runtime_identity(
                        logical_statement.as_deref().unwrap_or(line),
                        idx + 1,
                    ),
                    guard_ids: locksets_by_line
                        .get(&(idx + 1))
                        .cloned()
                        .unwrap_or_default(),
                    evidence: vec![
                        format!("存储证据: 连续区域 '{storage}' 通过 index × stride 派生对象指针"),
                        format!("分区证据: 指针别名 '{alias}' 的索引追溯至 worker/API partition"),
                        format!("布局证据: stride '{stride}' 未证明按 cache line 取整"),
                    ],
                    storage_identity: None,
                });
                continue;
            }
            if let Some((storage, alias)) = per_thread_pointer_region(line)
                && contiguous_symbols.contains(&storage)
                && !protected_symbols.contains(&storage)
                && !thread_local_symbols.contains(&storage)
                && let Some(access_kind) = pointer_alias_mutation(&lines, idx, &alias, &functions)
            {
                candidates.push(IndexedWriteCandidate {
                    file: file.path.clone(),
                    line: idx + 1,
                    snippet: line.trim().to_string(),
                    function_name: enclosing_function_name(&functions, idx + 1),
                    record_name: None,
                    record_line: None,
                    record_peer: None,
                    record_storage: None,
                    field_name: Some(storage),
                    alias_name: Some(alias.clone()),
                    access_kind,
                    has_direct_partition_evidence: true,
                    access_in_concurrent_context: true,
                    guard_ids: locksets_by_line
                        .get(&(idx + 1))
                        .cloned()
                        .unwrap_or_default(),
                    evidence: vec![
                        "并发证据: runtime thread id 选择连续存储中的独立 region".to_string(),
                        format!("写证据: region pointer alias '{alias}' 随后发生变异"),
                        "布局证据: per-thread region stride 未证明按 cache line 取整".to_string(),
                    ],
                    storage_identity: None,
                });
                continue;
            }
            if is_comment_only_line(line) || !(line.contains('[') || line.contains('(')) {
                continue;
            }
            let mutations: Vec<_> = indexed_mutations(line)
                .into_iter()
                .filter(|(symbol, _, _)| {
                    !pointee_only_accesses.contains(&(idx + 1, symbol.clone()))
                })
                .filter(|(symbol, _, _)| {
                    !serial_spawn_assignments.contains(&(idx + 1, symbol.clone()))
                })
                .filter(|(symbol, _, _)| !array_declarations.contains(&(idx + 1, symbol.clone())))
                .filter(|(symbol, _, _)| {
                    !local_noncontiguous_uses.contains(&(idx + 1, symbol.clone()))
                })
                .filter(|(symbol, _, _)| {
                    !unproved_member_uses
                        .get_or_insert_with(|| {
                            indexed_storage::unproved_member_accesses(file, &ownership_index)
                        })
                        .contains(&(idx + 1, symbol.clone()))
                })
                .collect();
            let function_mutation = function_indexed_mutation(line);
            let synchronization_targets = [
                "pthread_mutex_lock",
                "pthread_mutex_unlock",
                "pthread_spin_lock",
                "pthread_spin_unlock",
                "mtx_lock",
                "mtx_unlock",
            ]
            .iter()
            .flat_map(|callee| call_argument_lists(line, callee))
            .filter_map(|arguments| arguments.into_iter().next())
            .flat_map(|target| indexed_accesses(&target))
            .filter(|(_, expression)| identifier_tokens(expression).next().is_some())
            .filter(|(symbol, _)| {
                // A function-private mutex array is not an externally shared
                // synchronization API merely because it calls pthread locks.
                // This guard only constrains the extra API path; actual worker
                // partition or parallel evidence is still handled separately.
                !array_declarations.iter().any(|(declaration, name)| {
                    name == symbol
                        && *declaration <= idx + 1
                        && functions.iter().any(|function| {
                            function.body_start_line <= *declaration
                                && idx < function.body_end_line
                                && *declaration <= function.body_end_line
                        })
                        && !identifier_tokens(lines[declaration.saturating_sub(1)])
                            .any(|token| matches!(token, "static" | "extern"))
                })
            })
            .collect::<HashSet<_>>();
            if mutations.is_empty() && function_mutation.is_none() {
                continue;
            }
            let thread_indexed = mutations
                .iter()
                .find(|(symbol, expression, _)| {
                    index_origins.supports_parallel_argument(expression, idx + 1)
                        || (concurrent_lines.contains(&(idx + 1))
                            && index_origins.supports_parallel_argument(symbol, idx + 1))
                        || synchronization_targets.contains(&(symbol.clone(), expression.clone()))
                })
                .map(|(symbol, expression, kind)| {
                    (
                        Some(symbol.clone()),
                        Some(expression.as_str()),
                        kind.clone(),
                    )
                })
                .or(function_mutation.filter(|(_, expression, _)| {
                    expression.is_some_and(|expression| index_origins.supports(expression, idx + 1))
                }));
            let in_parallel_region = concurrent_lines.contains(&(idx + 1));
            // A runtime identity or a callable's explicit partition argument
            // supports independent roles, including externally invoked APIs.
            // A spelling such as "slot" in a local loop is not that evidence.
            if !in_parallel_region && thread_indexed.is_none() {
                continue;
            }
            let (field_name, index_expression, access_kind) = thread_indexed.unwrap_or_else(|| {
                let (symbol, _, kind) = mutations[0].clone();
                (Some(symbol), None, kind)
            });
            let function_name = enclosing_function_name(&functions, idx + 1);
            let pthread_worker_callback = function_name
                .as_deref()
                .is_some_and(|name| pthread_worker_names.contains(name));
            let worker_member_alias = pthread_worker_callback
                && field_name.as_deref().is_some_and(|field| {
                    functions
                        .iter()
                        .find(|function| function.name == function_name.clone().unwrap_or_default())
                        .is_some_and(|function| {
                            let start = function.body_start_line.saturating_sub(1).min(lines.len());
                            let end = function.body_end_line.min(lines.len()).max(start);
                            lines[start..end].iter().any(|line| {
                                line.contains(&format!("->{field}"))
                                    || line.contains(&format!(".{field}"))
                            })
                        })
                });
            let synchronization_slot =
                field_name
                    .as_ref()
                    .zip(index_expression)
                    .is_some_and(|(symbol, expression)| {
                        synchronization_targets.contains(&(symbol.clone(), expression.to_string()))
                    });
            let (field_name, field_alias) = field_name.map_or((None, None), |name| {
                if project_record_fields.contains(&name) {
                    (Some(name), None)
                } else if let Some(backing) = storage_aliases.resolve(&name, idx + 1) {
                    (Some(backing.clone()), Some(name))
                } else if let Some(member) = member_aliases.resolve(&name, idx + 1) {
                    (Some(member.clone()), Some(name))
                } else {
                    (Some(name), None)
                }
            });
            let has_member_alias = field_alias.is_some();
            if field_name.as_ref().is_some_and(|name| {
                protected_symbols.contains(name)
                    || (field_alias.is_none() && header_protected_symbols.contains(name))
                    || !contiguous_symbols.contains(name)
                    || non_contiguous_symbols.contains(name)
                    || thread_local_symbols.contains(name)
            }) || line_accesses_cache_aligned_record(line, &aligned_receiver_fields)
            {
                continue;
            }
            candidates.push(IndexedWriteCandidate {
                file: file.path.clone(),
                line: idx + 1,
                snippet: line.trim().to_string(),
                function_name,
                record_name: None,
                record_line: None,
                    record_peer: None,
                    record_storage: None,
                storage_identity: field_name.as_deref().and_then(|name| storage_index.access(&file.path, idx + 1, name)),
                field_name,
                alias_name: field_alias,
                access_kind,
                has_direct_partition_evidence: index_expression.is_some()
                    || worker_member_alias
                    || (pthread_worker_callback
                        && index_expression
                            .as_ref()
                            .is_some_and(|expression| looks_like_worker_slot_expression(expression))
                        && has_member_alias),
                access_in_concurrent_context: in_parallel_region
                    || index_expression.is_some_and(|expression| {
                        index_origins.supports_runtime_identity(expression, idx + 1)
                    }),
                guard_ids: locksets_by_line
                    .get(&(idx + 1))
                    .cloned()
                    .unwrap_or_default(),
                evidence: vec![
                    if synchronization_slot {
                        "同步槽位证据: 已知锁 API 修改动态选择的连续同步槽位；这是 API 风险，不等同于 runtime 线程编号".to_string()
                    } else if index_expression.is_some() {
                        "分区证据: 索引追溯至 runtime identity、调用参数或线程分区定义；外部调用参数表示 API 潜在风险".to_string()
                    } else {
                        "并发证据: 并行上下文附近存在索引写入".to_string()
                    },
                    "布局证据: 连续数组/容器元素可能共享缓存行".to_string(),
                ],
            });
        }
        let needs_pthread_flow = file.source.contains("pthread_create");
        let needs_partition_flow = has_parallel_source_marker(&file.source);
        if needs_pthread_flow || needs_partition_flow {
            if needs_pthread_flow {
                let mut owned_inline_writes = HashSet::new();
                candidates.extend(collect_pthread_worker_field_candidates(
                    file,
                    structs,
                    &functions,
                    &locksets_by_line,
                    cache_line_size,
                    &mut owned_inline_writes,
                ));
                // A bucket alias in a worker-owned record is not one shared
                // bucket array. Keep only the recovered cross-record pair.
                candidates.retain(|c| {
                    c.file != file.path
                        || c.record_name.is_some()
                        || !c.field_name.as_ref().is_some_and(|field| {
                            owned_inline_writes.contains(&(c.line, field.clone()))
                        })
                });
            }
            if needs_partition_flow {
                let shared_symbols = global_shared_array_symbols(file);
                candidates.extend(collect_partitioned_loop_candidates(
                    file,
                    &functions,
                    &shared_symbols,
                    &locksets_by_line,
                    cache_line_size,
                ));
                candidates.extend(collect_owner_guarded_block_candidates(
                    file,
                    &functions,
                    &shared_symbols,
                    &locksets_by_line,
                    cache_line_size,
                ));
            }
        }
        let ownership_file = alignment_macros
            .get(&file.path)
            .and_then(|macros| ownership_parse_without_alignment_macros(file, macros));
        let private_arrays = private_array_ranges(
            ownership_file.as_ref().unwrap_or(file),
            memory_arguments.get(&file.path),
        );
        candidates.retain(|candidate| {
            candidate.file != file.path
                || (!device_only_function_at(&functions, candidate.line)
                    && !fresh_indexed.get(&file.path).is_some_and(|accesses| {
                        accesses.iter().any(|(name, line, begin, end)| {
                            candidate.line == *line
                                && (candidate.field_name.as_ref() == Some(name)
                                    || candidate.alias_name.as_ref() == Some(name))
                                && !automatic_storage_scope_may_fork(&file.source[*begin..*end])
                        })
                    })
                    && !private_arrays.iter().any(|(name, start, end)| {
                        candidate.field_name.as_ref() == Some(name)
                            && *start <= candidate.line
                            && candidate.line <= *end
                    }))
        });
        if let Some(tree) = &file.tree {
            let mut literal_stores = HashMap::<(usize, String), bool>::new();
            let mut terminal_stores = HashMap::<(usize, String), bool>::new();
            let entries = [
                ("pthread_create", 2usize),
                ("thrd_create", 1),
                ("g_thread_new", 1),
            ]
            .into_iter()
            .flat_map(|(api, position)| {
                call_argument_lists(&file.source, api)
                    .into_iter()
                    .filter_map(move |args| {
                        args.get(position).and_then(|arg| callable_identifier(arg))
                    })
            })
            .filter(|entry| !ordinary_callees.contains(entry))
            .collect::<HashSet<_>>();
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() != "assignment_expression" {
                    return;
                }
                let Some(right) = node.child_by_field_name("right") else {
                    return;
                };
                let literal = matches!(
                    right.kind(),
                    "number_literal" | "null" | "nullptr" | "true" | "false" | "char_literal"
                ) || (right.kind() == "unary_expression"
                    && right
                        .child_by_field_name("argument")
                        .is_some_and(|argument| argument.kind() == "number_literal"));
                for (symbol, _, kind) in indexed_mutations(node_text(node, &file.source)) {
                    let key = (node.start_position().row + 1, symbol);
                    let value = literal && kind == CppAccessKind::Write;
                    literal_stores
                        .entry(key.clone())
                        .and_modify(|old| *old &= value)
                        .or_insert(value);
                    let terminal = value && terminal_thread_entry_store(node, file, &entries);
                    terminal_stores
                        .entry(key)
                        .and_modify(|old| *old &= terminal)
                        .or_insert(terminal);
                }
            });
            for candidate in candidates
                .iter_mut()
                .filter(|candidate| candidate.file == file.path)
            {
                if candidate.field_name.as_ref().is_some_and(|symbol| {
                    literal_stores.get(&(candidate.line, symbol.clone())) == Some(&true)
                }) {
                    candidate
                        .evidence
                        .push("写值证据: 直接槽位字面量赋值 [literal-slot-store]".to_owned());
                }
                if candidate.field_name.as_ref().is_some_and(|symbol| {
                    terminal_stores.get(&(candidate.line, symbol.clone())) == Some(&true)
                }) {
                    candidate.evidence.push("阶段证据: 已绑定线程入口的退出路径单次槽位写；不作为持续工作期写入 [terminal-thread-store]".to_owned());
                }
            }
        }
    }
    // Retain the access-site witness and additionally emit a declaration-site
    // witness when the access resolves to a typed member. A unique spelling is
    // not an ownership proof: a local array, map or parameter may have exactly
    // the same name as an unrelated record member in another translation unit.
    // Some
    // users review the executable access while others review the physical
    // layout declaration; both are legitimate views of the same root cause.
    let mut declaration_candidates = Vec::new();
    let index = EvidenceIndex::new(structs);
    let member_bindings = files
        .iter()
        .filter(|file| {
            candidates
                .iter()
                .any(|candidate| candidate.file == file.path)
        })
        .map(|file| {
            let variables = collect_variable_types(file, &index);
            (
                file.path.as_str(),
                field_access::collect(file, &index, &variables, &[]),
            )
        })
        .collect::<HashMap<_, _>>();
    for candidate in &candidates {
        if candidate.record_name.is_some() {
            continue;
        }
        let Some(field_name) = candidate.field_name.as_deref() else {
            continue;
        };
        let owners = structs
            .iter()
            .enumerate()
            .filter_map(|(record_index, record)| {
                if !member_bindings
                    .get(candidate.file.as_str())
                    .and_then(|lines| lines.get(&candidate.line))
                    .is_some_and(|accesses| {
                        accesses.iter().any(|access| {
                            access.record == record_index
                                && access.field == field_name
                                && access.kind != CppAccessKind::Read
                        })
                    })
                {
                    return None;
                }
                record
                    .fields
                    .iter()
                    .find(|field| {
                        field.name == field_name && super::types::has_contiguous_elements(field)
                    })
                    .map(|field| (record, field))
            })
            .collect::<Vec<_>>();
        if let [(record, field)] = owners.as_slice() {
            if record.file == candidate.file {
                continue;
            }
            let mut declaration = candidate.clone();
            declaration.file = record.file.clone();
            declaration.line = field.line;
            declaration.record_name = Some(record.name.clone());
            declaration.record_line = Some(record.line);
            declaration.evidence.push(format!(
                "访问位置: {}:{} 对该连续字段执行分区写入",
                candidate.file, candidate.line
            ));
            declaration_candidates.push(declaration);
        }
    }
    candidates.extend(declaration_candidates);
    // Positional call bindings already identify caller storage. Do not feed
    // them back through the legacy same-spelling declaration projection.
    candidates.extend(indexed_calls::collect_bound_indexed_calls(
        files,
        &storage_index,
    ));

    let mut seen = HashSet::new();
    // Prefer the bound owner over a same-line unqualified fallback; preserve
    // distinct bound owners instead of silently choosing the first spelling.
    let bound = candidates
        .iter()
        .filter(|c| c.record_name.is_some())
        .map(|c| (c.file.clone(), c.line, c.field_name.clone()))
        .collect::<HashSet<_>>();
    candidates.retain(|candidate| {
        if candidate.record_name.is_none()
            && bound.contains(&(
                candidate.file.clone(),
                candidate.line,
                candidate.field_name.clone(),
            ))
        {
            return false;
        }
        seen.insert((
            candidate.file.clone(),
            candidate.line,
            candidate.field_name.clone(),
            candidate.record_name.clone(),
            candidate.record_line,
            candidate.record_storage.clone(),
            candidate
                .record_peer
                .as_ref()
                .map(|p| (p.field.clone(), p.line)),
        ))
    });
    let isolated =
        indexed_field_distance::isolated_arrays(files, structs, &candidates, cache_line_size);
    candidates.retain(|candidate| {
        candidate.record_name.is_some()
            || candidate.alias_name.is_some()
            || !candidate
                .field_name
                .as_ref()
                .is_some_and(|name| isolated.contains(name))
    });
    candidates
}

fn terminal_thread_entry_store(
    node: tree_sitter::Node<'_>,
    file: &ParsedCppFile,
    entries: &HashSet<String>,
) -> bool {
    let Some(statement) = node.parent().filter(|n| n.kind() == "expression_statement") else {
        return false;
    };
    let Some(block) = statement
        .parent()
        .filter(|n| n.kind() == "compound_statement")
    else {
        return false;
    };
    let mut ancestor = Some(block);
    let mut function = None;
    while let Some(parent) = ancestor {
        if parent.kind() == "lambda_expression" {
            return false;
        }
        if parent.kind() == "function_definition" {
            function = Some(parent);
            break;
        }
        ancestor = parent.parent();
    }
    let Some(function) = function else {
        return false;
    };
    let Some(name) = function_definition_name(function, file).filter(|name| entries.contains(name))
    else {
        return false;
    };
    let Some(body) = function
        .child_by_field_name("body")
        .filter(|body| !body.has_error())
    else {
        return false;
    };
    let mut unsupported = false;
    walk_nodes(body, &mut |n| {
        unsupported |= matches!(n.kind(), "goto_statement" | "labeled_statement")
    });
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |n| {
            unsupported |= n.kind() == "call_expression"
                && n.child_by_field_name("function")
                    .is_some_and(|callee| node_text(callee, &file.source) == name);
            if n.kind() != "identifier" || node_text(n, &file.source) != name {
                return;
            }
            let Some(mut parent) = n.parent() else {
                unsupported = true;
                return;
            };
            if parent.kind() == "function_declarator"
                && parent.child_by_field_name("declarator") == Some(n)
            {
                return;
            }
            let mut argument = n;
            if parent.kind() == "pointer_expression"
                && node_text(parent, &file.source).starts_with('&')
            {
                argument = parent;
                let Some(next) = parent.parent() else {
                    unsupported = true;
                    return;
                };
                parent = next;
            }
            let thread_callback = parent.kind() == "argument_list"
                && parent
                    .parent()
                    .and_then(|call| call.child_by_field_name("function"))
                    .and_then(|callee| match node_text(callee, &file.source) {
                        "pthread_create" => Some(2),
                        "thrd_create" | "g_thread_new" => Some(1),
                        _ => None,
                    })
                    .is_some_and(|position| parent.named_child(position) == Some(argument));
            // Aliases, address-taking outside a thread creation call and
            // ordinary calls may invoke this body repeatedly on a hot path.
            unsupported |= !thread_callback;
        });
    }
    if unsupported {
        return false;
    }
    let siblings = block.named_children(&mut block.walk()).collect::<Vec<_>>();
    let Some(position) = siblings.iter().position(|n| *n == statement) else {
        return false;
    };
    let [exit] = &siblings[position + 1..] else {
        return false;
    };
    if exit.kind() == "return_statement" {
        return true;
    }
    if exit.kind() != "break_statement" {
        return false;
    }
    let mut ancestor = block.parent();
    let mut loop_node = None;
    while let Some(parent) = ancestor {
        if matches!(parent.kind(), "switch_statement" | "lambda_expression") {
            return false;
        }
        if matches!(
            parent.kind(),
            "while_statement" | "for_statement" | "do_statement" | "for_range_loop"
        ) {
            loop_node = Some(parent);
            break;
        }
        if parent == body {
            break;
        }
        ancestor = parent.parent();
    }
    let Some(loop_node) = loop_node.filter(|n| n.parent() == Some(body)) else {
        return false;
    };
    let statements = body.named_children(&mut body.walk()).collect::<Vec<_>>();
    let Some(position) = statements.iter().position(|n| *n == loop_node) else {
        return false;
    };
    matches!(&statements[position + 1..], [last] if last.kind() == "return_statement")
}

/// A loop-derived argument alone says nothing about a member's backing
/// instance. For this recovery path bind a value receiver declared before the
/// parallel loop to the unique method owner. Pointer/alias receivers remain
/// unresolved here, as do objects constructed independently inside the loop.
fn parallel_call_has_shared_receiver(
    file: &ParsedCppFile,
    callee: &str,
    line: usize,
    owner: usize,
    index: &EvidenceIndex<'_>,
    origins: &IndexPartitionOrigins,
) -> bool {
    let Some(tree) = &file.tree else { return false };
    let Some(start) = origins
        .parallel_inductions
        .iter()
        .filter(|(start, end, _)| *start <= line && line <= *end)
        .map(|(start, _, _)| *start)
        .min()
    else {
        return false;
    };
    let preceding = file.source.lines().take(start - 1).collect::<Vec<_>>();
    let directive = preceding
        .iter()
        .rev()
        .take(8)
        .map(|line| line.trim())
        .find(|line| !line.is_empty() && !matches!(*line, "#endif" | "#ifdef _OPENMP"))
        .unwrap_or("");
    let mut shared = false;
    walk_nodes(tree.root_node(), &mut |call| {
        if call.kind() != "call_expression" || call.start_position().row + 1 != line {
            return;
        }
        let Some(function) = call
            .child_by_field_name("function")
            .filter(|n| n.kind() == "field_expression")
        else {
            return;
        };
        if function
            .child_by_field_name("field")
            .is_none_or(|n| node_text(n, &file.source) != callee)
        {
            return;
        }
        let Some(receiver) = function
            .child_by_field_name("argument")
            .filter(|n| n.kind() == "identifier")
        else {
            return;
        };
        let name = node_text(receiver, &file.source);
        if ["private", "firstprivate", "lastprivate", "reduction"]
            .iter()
            .any(|clause| {
                call_argument_lists(directive, clause)
                    .iter()
                    .flatten()
                    .any(|argument| contains_identifier(argument, name))
            })
        {
            return;
        }
        let mut bindings = Vec::new();
        walk_nodes(tree.root_node(), &mut |decl| {
            if !matches!(decl.kind(), "declaration" | "parameter_declaration")
                || decl.start_byte() > call.start_byte()
            {
                return;
            }
            let scope = field_access::binding_scope(decl);
            if scope.start_byte() > call.start_byte() || scope.end_byte() < call.end_byte() {
                return;
            }
            let mut cursor = decl.walk();
            for shape in decl.children_by_field_name("declarator", &mut cursor) {
                let binding_name = shape
                    .child_by_field_name("declarator")
                    .filter(|_| shape.kind() == "function_declarator")
                    .map(|n| node_text(n, &file.source).to_owned())
                    .or_else(|| declarator_variable_name(shape, &file.source));
                if binding_name.as_deref() == Some(name) {
                    bindings.push((
                        scope.end_byte() - scope.start_byte(),
                        decl.start_byte(),
                        decl,
                        shape,
                    ));
                }
            }
        });
        bindings.sort_by_key(|(scope, pos, _, _)| (*scope, std::cmp::Reverse(*pos)));
        let Some((_, _, decl, shape)) = bindings.first().copied() else {
            return;
        };
        let shape = shape
            .child_by_field_name("declarator")
            .filter(|_| shape.kind() == "init_declarator")
            .unwrap_or(shape);
        if !(shape.kind() == "identifier" || value_initialized_receiver(shape, file))
            || decl.kind() != "declaration"
            || decl.start_position().row + 1 >= start
            || identifier_tokens(node_text(decl, &file.source))
                .any(|n| matches!(n, "thread_local" | "__thread"))
        {
            return;
        }
        let Some(ty) = decl.child_by_field_name("type") else {
            return;
        };
        let outer = node_text(ty, &file.source)
            .split('<')
            .next()
            .unwrap_or("")
            .trim();
        shared |= index.unambiguous_record_index(outer, &file.path) == Some(owner)
            && signature_type_matches_scope(
                file,
                decl.start_position().row + 1,
                &index.records[owner],
            );
    });
    shared
}

// Without symbol lookup tree-sitter can parse `Record value(count, f())`
// as a function declaration. A preceding lexical *value* binding for an
// otherwise bare parameter type disambiguates direct initialization. Keep
// actual prototypes and unresolved type/value names out of receiver proofs.
fn value_initialized_receiver(shape: tree_sitter::Node<'_>, file: &ParsedCppFile) -> bool {
    if shape.kind() != "function_declarator"
        || shape.has_error()
        || shape
            .child_by_field_name("declarator")
            .is_none_or(|n| n.kind() != "identifier")
    {
        return false;
    }
    let Some(parameters) = shape.child_by_field_name("parameters") else {
        return false;
    };
    parameters
        .named_children(&mut parameters.walk())
        .any(|parameter| {
            if parameter.kind() != "parameter_declaration" || parameter.named_child_count() != 1 {
                return false;
            }
            let Some(ty) = parameter
                .child_by_field_name("type")
                .filter(|n| n.kind() == "type_identifier")
            else {
                return false;
            };
            let name = node_text(ty, &file.source);
            let mut ancestor = shape.parent();
            while let Some(scope) = ancestor {
                if scope.kind() == "compound_statement" {
                    let preceding = scope
                        .named_children(&mut scope.walk())
                        .filter(|n| n.end_byte() < shape.start_byte())
                        .collect::<Vec<_>>();
                    for declaration in preceding.into_iter().rev() {
                        if matches!(declaration.kind(), "alias_declaration" | "type_definition")
                            && contains_identifier(node_text(declaration, &file.source), name)
                        {
                            return false;
                        }
                        if declaration.kind() != "declaration" {
                            continue;
                        }
                        for declarator in declaration
                            .children_by_field_name("declarator", &mut declaration.walk())
                        {
                            let inner = if matches!(
                                declarator.kind(),
                                "init_declarator" | "function_declarator"
                            ) {
                                declarator
                                    .child_by_field_name("declarator")
                                    .unwrap_or(declarator)
                            } else {
                                declarator
                            };
                            if node_text(inner, &file.source) == name {
                                return inner.kind() == "identifier"
                                    && declarator.kind() != "function_declarator";
                            }
                            if contains_identifier(node_text(declarator, &file.source), name) {
                                return false;
                            }
                        }
                    }
                }
                // Do not borrow a binding across an unhandled header scope.
                if matches!(
                    scope.kind(),
                    "function_definition"
                        | "for_statement"
                        | "for_range_loop"
                        | "if_statement"
                        | "switch_statement"
                        | "catch_clause"
                        | "lambda_expression"
                ) {
                    return false;
                }
                ancestor = scope.parent();
            }
            false
        })
}

fn global_scalar_mutex_names(file: &ParsedCppFile) -> HashMap<String, Vec<std::ops::Range<usize>>> {
    let mut names = HashMap::<String, Vec<std::ops::Range<usize>>>::new();
    let Some(tree) = &file.tree else {
        return names;
    };
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "declaration" || node.has_error() {
            return;
        }
        let mut parent = node.parent();
        while let Some(scope) = parent {
            if !matches!(
                scope.kind(),
                "translation_unit"
                    | "linkage_specification"
                    | "declaration_list"
                    | "preproc_if"
                    | "preproc_ifdef"
                    | "preproc_else"
                    | "preproc_elif"
            ) {
                return;
            }
            parent = scope.parent();
        }
        if identifier_tokens(node_text(node, &file.source))
            .any(|word| matches!(word, "thread_local" | "__thread" | "_Thread_local"))
        {
            return;
        }
        let Some(ty) = node.child_by_field_name("type") else {
            return;
        };
        if !matches!(
            node_text(ty, &file.source),
            "pthread_mutex_t" | "mtx_t" | "std::mutex" | "std::recursive_mutex"
        ) {
            return;
        }
        let mut cursor = node.walk();
        for decl in node.children_by_field_name("declarator", &mut cursor) {
            let decl = if decl.kind() == "init_declarator" {
                decl.child_by_field_name("declarator")
            } else {
                Some(decl)
            };
            if let Some(decl) = decl.filter(|d| d.kind() == "identifier") {
                let range = lock_macros::branch_range(node);
                let start = file.source[..range.start]
                    .bytes()
                    .filter(|b| *b == b'\n')
                    .count()
                    + 1;
                let end = if range.end == usize::MAX {
                    usize::MAX
                } else {
                    file.source[..range.end]
                        .bytes()
                        .filter(|b| *b == b'\n')
                        .count()
                        + 1
                };
                names
                    .entry(node_text(decl, &file.source).to_string())
                    .or_default()
                    .push(start..end);
            }
        }
    });
    let mut shadows = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(node.kind(), "declaration" | "parameter_declaration") {
            return;
        }
        let mut parent = node.parent();
        let mut local = false;
        while let Some(scope) = parent {
            if matches!(scope.kind(), "function_definition" | "lambda_expression") {
                local = true;
                break;
            }
            parent = scope.parent();
        }
        if !local {
            return;
        }
        for decl in node.children_by_field_name("declarator", &mut node.walk()) {
            if let Some(name) = declarator_variable_name(decl, &file.source) {
                shadows.insert(name);
            }
        }
    });
    names.retain(|name, _| !shadows.contains(name));
    names
}

struct IndexedMutationSummary {
    storage_identity: Option<String>,
    // Intersection over the callee's writes to this storage, restricted to
    // source-bound process-shared scalar mutex objects.
    guard_ids: Vec<String>,
    owner: Option<usize>,
    parameters: HashSet<usize>,
    kind: CppAccessKind,
}

fn collect_indexed_mutator_summaries(
    files: &[ParsedCppFile],
    aligned_types: &HashSet<String>,
    ownership: &EvidenceIndex<'_>,
    memory_arguments: &HashMap<String, HashSet<usize>>,
    lock_views: &HashMap<String, ParsedCppFile>,
    storage_index: &storage_identity::StorageIndex,
) -> HashMap<String, HashMap<String, IndexedMutationSummary>> {
    let mut summaries: HashMap<String, HashMap<String, IndexedMutationSummary>> = HashMap::new();
    let mut definitions: HashMap<String, usize> = HashMap::new();
    for file in files {
        let lock_file = lock_views.get(&file.path).unwrap_or(file);
        let locksets = collect_scoped_locksets(lock_file);
        let shared_guards = global_scalar_mutex_names(lock_file);
        let pointee_only_accesses = indexed_storage::pointee_only_accesses(file);
        let mut owners = HashMap::new();
        if let Some(tree) = &file.tree {
            walk_nodes(tree.root_node(), &mut |n| {
                if n.kind() == "function_definition"
                    && let Some(body) = n.child_by_field_name("body")
                    && let Some(owner) = field_access::function_owner(n, file, ownership)
                    && let Some(name) = function_definition_name(n, file)
                {
                    owners.insert((body.start_position().row + 1, name), owner);
                }
            });
        }
        let lines = file.source.lines().collect::<Vec<_>>();
        let private_arrays = private_array_ranges(file, memory_arguments.get(&file.path));
        // Summaries must not erase protection known at the callee's storage
        // declaration. Only typed array elements qualify: aligning the base
        // address of a scalar array does not isolate its elements.
        let functions = collect_function_regions(file);
        let mut declarations = HashMap::<String, Vec<bool>>::new();
        for (line, symbol) in array_declaration_sites(file) {
            let global = !functions
                .iter()
                .any(|f| f.body_start_line <= line && line <= f.body_end_line);
            let typed = lines.get(line.saturating_sub(1)).is_some_and(|text| {
                text.split_once('[').is_some_and(|(prefix, _)| {
                    let tokens = identifier_tokens(prefix).collect::<Vec<_>>();
                    !prefix.contains(['*', '&', '<', '('])
                        && tokens.last().is_some_and(|name| *name == symbol)
                        && tokens
                            .iter()
                            .rev()
                            .nth(1)
                            .is_some_and(|ty| aligned_types.contains(*ty))
                })
            });
            declarations
                .entry(symbol)
                .or_default()
                .push(global && typed);
        }
        let mut protected = declarations
            .into_iter()
            .filter_map(|(symbol, proofs)| matches!(proofs.as_slice(), [true]).then_some(symbol))
            .collect::<HashSet<_>>();
        protected.extend(visible_isolated_extern_arrays(files, file, aligned_types));
        for function in functions {
            *definitions.entry(function.name.clone()).or_default() += 1;
            let parameters = function_parameters(&function);
            if parameters.is_empty() {
                continue;
            }
            let start = function.body_start_line.saturating_sub(1).min(lines.len());
            let end = function.body_end_line.min(lines.len()).max(start);
            let mut function_guards = HashMap::<String, Vec<String>>::new();
            for line_index in start..end {
                let line = lines[line_index];
                let statement = if identifier_tokens(line)
                    .any(|callee| explicit_atomic_argument_access(callee, 0).is_some())
                {
                    logical_statement(&lines, line_index, end.saturating_sub(line_index).min(16))
                } else {
                    line.to_string()
                };
                let mut mutations = indexed_mutations(&statement);
                for (field, index) in indexed_accesses(&statement) {
                    if let Some(kind) = macro_field_mutation(&statement, &field)
                        && kind != CppAccessKind::Read
                    {
                        mutations.push((field, index, kind));
                    }
                }
                for (field, index, kind) in mutations {
                    // Formal pointer/array targets require actual-argument
                    // binding; their bare names are not project-wide storage.
                    if parameters.contains(&field)
                        || pointee_only_accesses.contains(&(line_index + 1, field.clone()))
                        || protected.contains(&field)
                        || private_arrays.iter().any(|(name, start, end)| {
                            name == &field && *start <= line_index + 1 && line_index < *end
                        })
                    {
                        continue;
                    }
                    let guards = locksets
                        .get(&(line_index + 1))
                        .into_iter()
                        .flatten()
                        .filter(|guard| {
                            shared_guards.get(*guard).is_some_and(|ranges| {
                                ranges.iter().any(|range| range.contains(&(line_index + 1)))
                            })
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    function_guards
                        .entry(field.clone())
                        .and_modify(|common| common.retain(|g| guards.contains(g)))
                        .or_insert(guards);
                    for (position, parameter) in parameters.iter().enumerate() {
                        if contains_identifier(&index, parameter) {
                            let summary = summaries
                                .entry(function.name.clone())
                                .or_default()
                                .entry(field.clone())
                                .or_insert_with(|| IndexedMutationSummary {
                                    storage_identity: storage_index.access(
                                        &file.path,
                                        line_index + 1,
                                        &field,
                                    ),
                                    guard_ids: Vec::new(),
                                    owner: owners
                                        .get(&(function.body_start_line, function.name.clone()))
                                        .copied(),
                                    parameters: HashSet::new(),
                                    kind: kind.clone(),
                                });
                            if summary.storage_identity
                                != storage_index.access(&file.path, line_index + 1, &field)
                            {
                                summary.storage_identity = None;
                            }
                            summary.parameters.insert(position);
                            if access_kind_strength(&kind) > access_kind_strength(&summary.kind) {
                                summary.kind = kind.clone();
                            }
                        }
                    }
                }
            }
            if let Some(fields) = summaries.get_mut(&function.name) {
                for (field, summary) in fields {
                    // Instance/member locks need receiver binding at the call
                    // site; a coincident global spelling cannot certify them.
                    if summary.owner.is_none() {
                        summary.guard_ids = function_guards.remove(field).unwrap_or_default();
                    }
                }
            }
        }
    }
    // These summaries do not yet resolve overloads or receiver types. A bare
    // name shared by multiple definitions cannot identify a mutation target:
    // e.g. Log::add must not inherit Counters::add's atomic array write.
    // Direct indexed accesses remain available independently of this summary.
    summaries.retain(|name, _| definitions.get(name) == Some(&1));
    summaries
}

/// Resolve a narrow cross-file layout fact through a visible declaration,
/// rather than transferring protection between project-wide equal spellings.
fn visible_isolated_extern_arrays(
    files: &[ParsedCppFile],
    file: &ParsedCppFile,
    isolated_types: &HashSet<String>,
) -> HashSet<String> {
    let Some(tree) = &file.tree else {
        return HashSet::new();
    };
    let functions = collect_function_regions(file);
    let mut local_bindings = HashSet::new();
    let mut receiver_scopes = functions.iter().any(|f| f.signature.contains("::"));
    walk_nodes(tree.root_node(), &mut |node| {
        receiver_scopes |= matches!(node.kind(), "class_specifier" | "namespace_definition");
        if node.kind() == "function_definition" {
            let mut ancestor = node.parent();
            while let Some(parent) = ancestor {
                receiver_scopes |= parent.kind() == "struct_specifier";
                ancestor = parent.parent();
            }
        }
        if matches!(
            node.kind(),
            "declaration" | "field_declaration" | "parameter_declaration"
        ) {
            for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
                if declarator.kind() != "function_declarator"
                    && let Some(name) = declarator_variable_name(declarator, &file.source)
                {
                    local_bindings.insert(name);
                }
            }
        }
    });
    // The current name binding is limited to free-function/global C-style
    // storage. Implicit receivers or namespace lookup require richer identity.
    if receiver_scopes {
        return HashSet::new();
    }
    let first_body = functions
        .iter()
        .map(|f| f.body_start_line)
        .min()
        .unwrap_or(0);
    let mut headers = Vec::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "preproc_include"
            || node.parent().is_none_or(|p| p.kind() != "translation_unit")
            || node.end_position().row + 1 > first_body
        {
            return;
        }
        let Some(path) = node.child_by_field_name("path") else {
            return;
        };
        let path = node_text(path, &file.source);
        let Some(relative) = path.strip_prefix('"').and_then(|p| p.strip_suffix('"')) else {
            return;
        };
        let Some(parent) = Path::new(&file.path).parent() else {
            return;
        };
        let path = parent.join(relative);
        if let Some(header) = files.iter().find(|f| Path::new(&f.path) == path) {
            headers.push(header);
        }
    });
    let mut declarations = HashMap::<String, Vec<bool>>::new();
    for header in headers {
        let Some(tree) = &header.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "declaration"
                || node.parent().is_none_or(|p| p.kind() != "translation_unit")
            {
                return;
            }
            let text = node_text(node, &header.source).trim();
            let Some((prefix, _)) = text.split_once('[') else {
                return;
            };
            let tokens = identifier_tokens(prefix).collect::<Vec<_>>();
            let Some(symbol) = tokens.last() else { return };
            let isolated = text.starts_with("extern ")
                && !prefix.contains(['*', '&', '<', '(', ':'])
                && tokens.len() == 3
                && isolated_types.contains(tokens[1]);
            declarations
                .entry((*symbol).to_owned())
                .or_default()
                .push(isolated);
        });
    }
    let locals = array_declaration_sites(file)
        .into_iter()
        .map(|(_, name)| name)
        .collect::<HashSet<_>>();
    declarations
        .into_iter()
        .filter_map(|(symbol, proofs)| {
            (proofs.iter().all(|proof| *proof)
                && !locals.contains(&symbol)
                && !local_bindings.contains(&symbol)
                && !functions
                    .iter()
                    .any(|f| function_parameters(f).contains(&symbol))
                && !file.source.lines().any(|line| {
                    field_access_tokens(line)
                        .into_iter()
                        .any(|(receiver, field)| receiver.is_some() && field == symbol)
                }))
            .then_some(symbol)
        })
        .collect()
}

// API partition evidence belongs to one atomic target and one scalar index
// parameter. An unrelated atomic operation in the same function cannot lend
// this evidence to other fields, argument positions, or descriptor pointers.
fn collect_atomic_indexed_mutators(files: &[ParsedCppFile]) -> HashSet<(String, String, usize)> {
    let mut summaries = HashSet::new();
    for file in files {
        let lines = file.source.lines().collect::<Vec<_>>();
        for function in collect_function_regions(file) {
            let parameters = function_parameters(&function);
            if parameters.is_empty() {
                continue;
            }
            let start = function.body_start_line.saturating_sub(1).min(lines.len());
            let end = function.body_end_line.min(lines.len()).max(start);
            for line_index in start..end {
                let line = lines[line_index];
                if !(line.contains("atomic") || line.contains("__sync_")) {
                    continue;
                }
                let statement =
                    logical_statement(&lines, line_index, end.saturating_sub(line_index).min(16));
                for call in identifier_tokens(&statement).collect::<HashSet<_>>() {
                    for arguments in call_argument_lists(&statement, call) {
                        let Some(target) = arguments.first() else {
                            continue;
                        };
                        // Only the actual atomic destination supplies this fallback;
                        // expected/output/value operands are different locations.
                        let target_call = format!("{call}({target})");
                        for (field, index) in indexed_accesses(target) {
                            if !macro_field_mutation(&target_call, &field)
                                .is_some_and(|kind| kind != CppAccessKind::Read)
                            {
                                continue;
                            }
                            for (position, parameter) in parameters.iter().enumerate() {
                                // Complex descriptor/data lookups require an actual
                                // caller/runtime origin, not a bare API parameter.
                                if index.trim() == parameter {
                                    summaries.insert((
                                        function.name.clone(),
                                        field.clone(),
                                        position,
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    summaries
}

#[derive(Debug, Clone)]
struct FunctionRegion {
    name: String,
    declarator: String,
    signature: String,
    body_start_line: usize,
    body_end_line: usize,
}

fn collect_function_regions(file: &ParsedCppFile) -> Vec<FunctionRegion> {
    let mut functions = Vec::new();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "function_definition" {
                return;
            }
            let Some(declarator) = node.child_by_field_name("declarator") else {
                return;
            };
            let Some(body) = node.child_by_field_name("body") else {
                return;
            };
            let declarator_text = node_text(declarator, &file.source);
            let Some(name) = function_definition_name(node, file) else {
                return;
            };
            let signature = file.source[node.start_byte()..body.start_byte()].to_string();
            functions.push(FunctionRegion {
                name,
                declarator: declarator_text.to_string(),
                signature,
                body_start_line: body.start_position().row + 1,
                body_end_line: body.end_position().row + 1,
            });
        });
    }
    let fallback = collect_legacy_function_regions(file, &functions);
    functions.extend(fallback);
    functions.sort_unstable_by_key(|function| function.body_start_line);
    functions
}

fn enclosing_function_name(functions: &[FunctionRegion], line: usize) -> Option<String> {
    functions
        .iter()
        .filter(|function| function.body_start_line <= line && line <= function.body_end_line)
        .max_by_key(|function| function.body_start_line)
        .map(|function| function.name.clone())
}

// GPU lanes are not CPU coherence participants. Restrict this exclusion to
// explicit execution-space declarations: a dual host/device function can still
// be called by CPU workers, and a project's filename is not execution evidence.
fn device_only_function_at(functions: &[FunctionRegion], line: usize) -> bool {
    functions
        .iter()
        .filter(|function| function.body_start_line <= line && line <= function.body_end_line)
        .min_by_key(|function| function.body_end_line - function.body_start_line)
        .is_some_and(|function| {
            let tokens = identifier_tokens(&function.signature).collect::<HashSet<_>>();
            tokens.contains("__global__")
                || (tokens.contains("__device__") && !tokens.contains("__host__"))
        })
}

fn non_contiguous_indexed_symbols(file: &ParsedCppFile) -> HashSet<String> {
    let mut symbols = HashSet::new();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(node.kind(), "declaration" | "field_declaration") {
                return;
            }
            let Some(type_node) = node.child_by_field_name("type") else {
                return;
            };
            if !is_non_contiguous_index_type(node_text(type_node, &file.source)) {
                return;
            }
            let mut cursor = node.walk();
            for declarator in node.children_by_field_name("declarator", &mut cursor) {
                if let Some(symbol) = declarator_variable_name(declarator, &file.source) {
                    symbols.insert(symbol);
                }
            }
        });
    }
    for line in file.source.lines() {
        if is_non_contiguous_index_type(line)
            && let Some(symbol) = extract_static_candidate_name(line)
        {
            symbols.insert(symbol);
        }
    }
    symbols
}

fn contiguous_indexed_symbols(file: &ParsedCppFile) -> HashSet<String> {
    collect_contiguous_indexed_symbols(file, true)
}

/// A local receiver must obtain layout evidence from its own declaration,
/// not a same-named pointer in another function or a shadowed outer scope.
fn unproved_local_index_storage(file: &ParsedCppFile) -> HashSet<(usize, String)> {
    let Some(tree) = &file.tree else {
        return HashSet::new();
    };
    let source = &file.source;
    let aliases = contiguous_type_aliases(source);
    let mut bindings = HashMap::<String, Vec<(usize, usize, bool)>>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(node.kind(), "declaration" | "parameter_declaration") || node.has_error() {
            return;
        }
        let parameter = node.kind() == "parameter_declaration";
        let mut scope = node.parent();
        let mut end = None;
        while let Some(parent) = scope {
            if parameter
                && matches!(
                    parent.kind(),
                    "declaration" | "parameter_declaration" | "type_descriptor"
                )
            {
                // A prototype/function-pointer parameter is not a local
                // binding in the surrounding function body.
                return;
            }
            if matches!(
                parent.kind(),
                "function_definition" | "lambda_expression" | "catch_clause"
            ) || (!parameter
                && matches!(
                    parent.kind(),
                    "compound_statement" | "for_statement" | "for_range_loop" | "if_statement"
                ))
            {
                end = Some(parent.end_byte());
                break;
            }
            if matches!(parent.kind(), "translation_unit" | "field_declaration_list") {
                break;
            }
            scope = parent.parent();
        }
        let Some(end) = end else { return };
        let ty = node
            .child_by_field_name("type")
            .map(|n| node_text(n, source))
            .unwrap_or("");
        for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
            let Some(name) = declarator_variable_name(declarator, source) else {
                continue;
            };
            let mut shape = declarator;
            let mut native = false;
            loop {
                native |= matches!(shape.kind(), "pointer_declarator" | "array_declarator");
                let Some(inner) = shape.child_by_field_name("declarator") else {
                    break;
                };
                shape = inner;
            }
            let mut contiguous = native
                || is_contiguous_index_type(ty)
                || identifier_tokens(ty).any(|word| aliases.contains(word));
            if ty.trim() == "auto" && !native {
                // Preserve an existing alias deduction until the initializer
                // can be rebound here. An untyped callback parameter has no
                // initializer and cannot borrow that exception.
                if declarator.child_by_field_name("value").is_some() {
                    // Still install a binding so an outer opaque receiver
                    // cannot veto this inner alias. This is not new layout
                    // evidence; the existing collector must supply it.
                    contiguous = true;
                }
            }
            contiguous &= !is_non_contiguous_index_type(ty);
            bindings
                .entry(name)
                .or_default()
                .push((declarator.start_byte(), end, contiguous));
        }
    });
    let mut uses = HashMap::<(usize, String), bool>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "subscript_expression" {
            return;
        }
        let Some(receiver) = node
            .child_by_field_name("argument")
            .filter(|n| n.kind() == "identifier")
        else {
            return;
        };
        let name = node_text(receiver, source);
        let unproved = bindings
            .get(name)
            .and_then(|entries| {
                entries
                    .iter()
                    .filter(|(begin, end, _)| {
                        *begin < receiver.start_byte() && receiver.end_byte() < *end
                    })
                    .max_by_key(|(begin, _, _)| *begin)
            })
            .is_some_and(|(_, _, contiguous)| !contiguous);
        uses.entry((receiver.start_position().row + 1, name.to_owned()))
            .and_modify(|all| *all &= unproved)
            .or_insert(unproved);
    });
    uses.into_iter()
        .filter_map(|(key, unproved)| unproved.then_some(key))
        .collect()
}

fn collect_contiguous_indexed_symbols(
    file: &ParsedCppFile,
    include_local: bool,
) -> HashSet<String> {
    let mut symbols = HashSet::new();
    let native_element_pointers = native_subscript_initializers(file);
    let contiguous_aliases = contiguous_type_aliases(&file.source);
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(
                node.kind(),
                "declaration" | "field_declaration" | "parameter_declaration"
            ) {
                return;
            }
            if !include_local {
                // Parameters and function-local storage cannot establish the
                // layout of an unrelated same-named receiver in another TU.
                if node.kind() == "parameter_declaration" {
                    return;
                }
                let mut scope = node.parent();
                while let Some(parent) = scope {
                    if matches!(
                        parent.kind(),
                        "function_definition" | "lambda_expression" | "compound_statement"
                    ) {
                        return;
                    }
                    scope = parent.parent();
                }
            }
            let type_text = node
                .child_by_field_name("type")
                .map(|type_node| node_text(type_node, &file.source))
                .unwrap_or("");
            if is_non_contiguous_index_type(type_text) {
                return;
            }
            let known_container = is_contiguous_index_type(type_text)
                || identifier_tokens(type_text).any(|token| contiguous_aliases.contains(token));
            let mut cursor = node.walk();
            for declarator in node.children_by_field_name("declarator", &mut cursor) {
                let pointer_or_array = native_indexed_declarator(declarator)
                    || native_element_pointers.contains(&declarator.start_byte())
                    || (type_text.trim() == "auto"
                        && declarator
                            .child_by_field_name("value")
                            .is_some_and(|value| {
                                value.kind() == "new_expression"
                                    || (value.kind() == "cast_expression"
                                        && value
                                            .child_by_field_name("type")
                                            .is_some_and(native_indexed_declarator))
                            }));
                if (known_container || pointer_or_array)
                    && let Some(symbol) = declarator_variable_name(declarator, &file.source)
                {
                    symbols.insert(symbol);
                }
            }
        });
        return symbols;
    }

    if !include_local {
        // The text fallback has no trustworthy declaration scope.
        return symbols;
    }
    for line in file.source.lines() {
        let type_like = is_contiguous_index_type(line)
            || (line.contains('[')
                && line.split('[').next().is_some_and(|prefix| {
                    identifier_tokens(prefix).count() >= 2
                        && !prefix.contains('=')
                        && !prefix.contains("++")
                        && !prefix.contains("--")
                }));
        if type_like && let Some(symbol) = extract_static_candidate_name(line) {
            symbols.insert(symbol);
        }
    }
    symbols
}

// Follow only the declarator shape. Operators and subscripts in an
// initializer do not establish the declared object's storage topology.
fn native_indexed_declarator(mut node: tree_sitter::Node<'_>) -> bool {
    loop {
        if matches!(
            node.kind(),
            "pointer_declarator"
                | "array_declarator"
                | "abstract_pointer_declarator"
                | "abstract_array_declarator"
        ) {
            return true;
        }
        if node.kind() == "function_declarator" {
            return false;
        }
        let Some(inner) = node.child_by_field_name("declarator") else {
            return false;
        };
        node = inner;
    }
}

/// Recover auto p = rows[i] only when the selected lexical declaration has
/// at least two native pointer/array layers. No overloaded subscript or
/// same-named declaration in a different scope supplies this result type.
/// Bind the alias before observed parallel use; per-worker row selection
/// alone does not establish cache-block proximity between different rows.
fn native_subscript_initializers(file: &ParsedCppFile) -> HashSet<usize> {
    // The proof below only accepts a source-spelled auto declaration. Avoid
    // building concurrency and binding facts for files that cannot use it.
    if !file.source.contains("auto") {
        return HashSet::new();
    }
    let Some(tree) = &file.tree else {
        return HashSet::new();
    };
    let concurrent = concurrent_context_lines(file);
    let mut bindings =
        HashMap::<String, Vec<(tree_sitter::Node<'_>, tree_sitter::Node<'_>, usize)>>::new();
    let mut aliases = Vec::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(node.kind(), "declaration" | "parameter_declaration") || node.has_error() {
            return;
        }
        let parameter = node.kind() == "parameter_declaration";
        let mut scope = node;
        while let Some(parent) = scope.parent() {
            scope = parent;
            if matches!(
                scope.kind(),
                "function_definition"
                    | "lambda_expression"
                    | "translation_unit"
                    | "declaration_list"
                    | "field_declaration_list"
                    | "preproc_if"
                    | "preproc_ifdef"
                    | "catch_clause"
            ) || (!parameter
                && matches!(
                    scope.kind(),
                    "compound_statement" | "for_statement" | "for_range_loop" | "if_statement"
                ))
                || (parameter
                    && matches!(
                        scope.kind(),
                        "declaration" | "parameter_declaration" | "type_descriptor"
                    ))
            {
                break;
            }
        }
        let auto_type = node
            .child_by_field_name("type")
            .is_some_and(|ty| node_text(ty, &file.source) == "auto");
        for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
            let Some(name) = declarator_variable_name(declarator, &file.source) else {
                continue;
            };
            let mut shape = declarator;
            let mut depth = 0;
            loop {
                depth += usize::from(matches!(
                    shape.kind(),
                    "pointer_declarator" | "array_declarator"
                ));
                if shape.kind() == "function_declarator" {
                    depth = 0;
                    break;
                }
                let Some(inner) = shape.child_by_field_name("declarator") else {
                    break;
                };
                shape = inner;
            }
            bindings
                .entry(name)
                .or_default()
                .push((declarator, scope, depth));
            if auto_type
                && !concurrent.contains(&(declarator.start_position().row + 1))
                && concurrent.iter().any(|line| {
                    declarator.end_position().row + 1 < *line
                        && *line <= scope.end_position().row + 1
                })
                && let Some(value) = declarator.child_by_field_name("value")
                && value.kind() == "subscript_expression"
                && let Some(base) = value
                    .child_by_field_name("argument")
                    .filter(|n| n.kind() == "identifier")
            {
                aliases.push((declarator.start_byte(), base));
            }
        }
    });
    aliases
        .into_iter()
        .filter_map(|(declaration, base)| {
            let entries = bindings.get(node_text(base, &file.source))?;
            let (_, _, depth) = entries
                .iter()
                .filter(|(decl, scope, _)| {
                    decl.start_byte() < base.start_byte()
                        && scope.start_byte() <= base.start_byte()
                        && base.end_byte() < scope.end_byte()
                })
                .max_by_key(|(decl, _, _)| decl.start_byte())?;
            (*depth >= 2).then_some(declaration)
        })
        .collect()
}

fn contiguous_type_aliases(source: &str) -> HashSet<String> {
    let mut aliases = HashSet::new();
    let mut statement = String::new();
    for raw_line in source.lines() {
        let line = raw_line.split("//").next().unwrap_or(raw_line).trim();
        if statement.is_empty() && !(line.starts_with("using ") || line.starts_with("typedef ")) {
            continue;
        }
        if !statement.is_empty() {
            statement.push(' ');
        }
        statement.push_str(line);
        if !line.contains(';') {
            continue;
        }
        if is_contiguous_index_type(&statement) {
            let alias = if statement.starts_with("using ") {
                statement
                    .strip_prefix("using ")
                    .and_then(|tail| tail.split('=').next())
                    .and_then(|name| identifier_tokens(name).last())
            } else {
                statement
                    .trim_end_matches(';')
                    .split_whitespace()
                    .last()
                    .and_then(|name| identifier_tokens(name).last())
            };
            if let Some(alias) = alias {
                aliases.insert(alias.to_string());
            }
        }
        statement.clear();
    }
    aliases
}

fn is_contiguous_index_type(type_text: &str) -> bool {
    let compact = type_text
        .split_whitespace()
        .filter(|word| {
            !matches!(
                *word,
                "const"
                    | "volatile"
                    | "typename"
                    | "static"
                    | "extern"
                    | "mutable"
                    | "thread_local"
                    | "typedef"
            )
        })
        .collect::<String>()
        .to_ascii_lowercase();
    let kinds = [
        "std::vector<",
        "std::array<",
        "std::span<",
        "span<",
        "absl::fixedarray<",
        "folly::small_vector<",
        "llvm::smallvector<",
        "boost::container::small_vector<",
        "kokkos::view<",
        "view<",
    ];
    // A template argument does not define its owner's storage topology:
    // Opaque<std::vector<T>> need not be contiguous or even expose vector
    // elements. Keep matching declaration/alias text, but only at type depth
    // zero and at a qualified-name boundary.
    let mut depth = 0usize;
    for (offset, ch) in compact.char_indices() {
        let start = if compact[..offset].ends_with("::") {
            offset - 2
        } else {
            offset
        };
        if depth == 0
            && (start == 0
                || !compact.as_bytes()[start - 1].is_ascii_alphanumeric()
                    && !matches!(compact.as_bytes()[start - 1], b'_' | b':'))
            && (kinds.iter().any(|kind| compact[offset..].starts_with(kind))
                || conditional_may_have_contiguous_type(&compact[offset..]))
        {
            return true;
        }
        match ch {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    false
}

fn conditional_may_have_contiguous_type(text: &str) -> bool {
    let (arguments, needs_type) = if let Some(rest) = text.strip_prefix("std::conditional<") {
        (rest, true)
    } else if let Some(rest) = text.strip_prefix("std::conditional_t<") {
        (rest, false)
    } else {
        return false;
    };
    let mut depth = 0usize;
    let mut begin = 0;
    let mut parts = Vec::new();
    for (offset, ch) in arguments.char_indices() {
        match ch {
            '<' => depth += 1,
            '>' if depth > 0 => depth -= 1,
            ',' if depth == 0 => {
                parts.push(&arguments[begin..offset]);
                begin = offset + 1;
            }
            '>' => {
                parts.push(&arguments[begin..offset]);
                if parts.len() != 3 || needs_type && !arguments[offset + 1..].starts_with("::type")
                {
                    return false;
                }
                // A may-layout capability, not an isolation proof. Unknown
                // conditions can select either arm; literals select one.
                return match parts[0] {
                    "true" | "1" => is_contiguous_index_type(parts[1]),
                    "false" | "0" => is_contiguous_index_type(parts[2]),
                    _ => is_contiguous_index_type(parts[1]) || is_contiguous_index_type(parts[2]),
                };
            }
            _ => {}
        }
    }
    false
}

fn thread_local_symbols(file: &ParsedCppFile) -> HashSet<String> {
    file.source
        .lines()
        .filter(|line| line.contains("thread_local") || line.contains("__thread"))
        .filter_map(extract_static_candidate_name)
        .collect()
}

fn symbol_may_escape_line(line: &str, symbol: &str) -> bool {
    let compact = line.replace(char::is_whitespace, "");
    compact.contains(&format!("&{symbol}"))
        || compact.contains(&format!("std::move({symbol})"))
        || compact.contains(&format!("return{symbol}"))
        || compact.starts_with(&format!("{symbol}="))
        || lambda_capture_contains(line, symbol)
        || symbol_occurs_inside_call_arguments(line, symbol)
}

fn lambda_capture_contains(line: &str, symbol: &str) -> bool {
    let Some(open) = line.find('[') else {
        return false;
    };
    let Some(close) = line[open + 1..].find(']') else {
        return false;
    };
    token_occurs(&line[open + 1..open + 1 + close], symbol)
}

fn symbol_occurs_inside_call_arguments(line: &str, symbol: &str) -> bool {
    let bytes = line.as_bytes();
    let mut depth = 0i32;
    let mut start = None;
    for (offset, byte) in bytes.iter().enumerate() {
        match byte {
            b'(' => {
                if depth == 0 {
                    start = Some(offset + 1);
                }
                depth += 1;
            }
            b')' if depth > 0 => {
                depth -= 1;
                if depth == 0
                    && let Some(start) = start.take()
                    && token_occurs(&line[start..offset], symbol)
                {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Recover scalar RAII locksets at source lines. This is intentionally a
/// positive proof: computed/per-element guards such as `locks[index]` are not
/// accepted because two candidate locations may then use two different locks.
// Bind the receiver to an actual standard condition-variable field. A method
// merely named wait on an unknown object does not restore a lock.
#[derive(Default)]
struct BoundConditionWaits {
    calls: HashSet<usize>,
    predicates: HashSet<usize>,
    receiver_accesses: HashSet<(usize, usize, String)>,
}

fn bound_condition_variable_waits(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    syntax: &HashMap<usize, Vec<field_access::SyntaxAccess>>,
) -> BoundConditionWaits {
    let mut waits = BoundConditionWaits::default();
    if !file.source.contains("wait") {
        return waits;
    }
    let Some(tree) = &file.tree else { return waits };
    let mut macros = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if matches!(node.kind(), "preproc_def" | "preproc_function_def")
            && let Some(name) = node.child_by_field_name("name")
        {
            macros.insert(node_text(name, &file.source));
        }
    });
    walk_nodes(tree.root_node(), &mut |call| {
        if call.kind() != "call_expression" {
            return;
        }
        let Some(function) = call
            .child_by_field_name("function")
            .filter(|node| node.kind() == "field_expression")
        else {
            return;
        };
        let Some(method) = function.child_by_field_name("field") else {
            return;
        };
        let predicate_position = match node_text(method, &file.source) {
            "wait" => 1,
            "wait_for" | "wait_until" => 2,
            _ => return,
        };
        let Some(arguments) = call.child_by_field_name("arguments") else {
            return;
        };
        if ![predicate_position, predicate_position + 1].contains(&arguments.named_child_count())
            || identifier_tokens(node_text(function, &file.source))
                .any(|name| macros.contains(name))
        {
            return;
        }
        let Some(receiver) = function.child_by_field_name("argument") else {
            return;
        };
        let Some(accesses) = syntax.get(&(receiver.start_position().row + 1)) else {
            return;
        };
        let terminal = receiver.child_by_field_name("field").unwrap_or(receiver);
        let matching = accesses
            .iter()
            .filter(|access| {
                access.start_byte == receiver.start_byte()
                    && access.field == node_text(terminal, &file.source)
            })
            .collect::<Vec<_>>();
        if matching.is_empty() {
            return;
        }
        if matching.iter().all(|access| {
            index.record(access.record).fields.iter().any(|field| {
                field.name == access.field
                    && !field.is_indirect
                    && !field.is_array
                    && field.ty_str.trim() == "std::condition_variable"
            })
        }) {
            waits.calls.insert(call.start_byte());
            for access in &matching {
                waits.receiver_accesses.insert((
                    access.record,
                    receiver.start_position().row + 1,
                    access.field.clone(),
                ));
            }
            if arguments.named_child_count() == predicate_position + 1
                && let Some(predicate) = arguments.named_child(predicate_position as u32)
                && predicate.kind() == "lambda_expression"
                && !predicate.has_error()
                && !identifier_tokens(node_text(predicate, &file.source)).any(|token| {
                    macros.contains(token) || matches!(token, "co_await" | "co_yield" | "co_return")
                })
            {
                waits.predicates.insert(predicate.start_byte());
            }
        }
    });
    waits
}

fn collect_scoped_locksets(file: &ParsedCppFile) -> HashMap<usize, Vec<String>> {
    collect_scoped_locksets_with_waits(file, &BoundConditionWaits::default())
}

fn collect_scoped_locksets_with_waits(
    file: &ParsedCppFile,
    waits: &BoundConditionWaits,
) -> HashMap<usize, Vec<String>> {
    let mut by_line = HashMap::new();
    if ![
        "lock_guard",
        "unique_lock",
        "scoped_lock",
        "pthread_mutex_lock",
        "mtx_lock",
        "gpr_mu_lock",
        "PyMutex_Lock",
        "g_mutex_lock",
        "uv_mutex_lock",
    ]
    .iter()
    .any(|token| file.source.contains(token))
    {
        return by_line;
    }
    let Some(tree) = &file.tree else {
        // A textual brace count cannot establish lock dominance or lifetime.
        return by_line;
    };
    walk_nodes(tree.root_node(), &mut |block| {
        if block.kind() != "compound_statement" || block.has_error() {
            return;
        }
        // A label can admit control flow that bypasses a preceding acquisition.
        let mut has_jump_entry = false;
        walk_nodes(block, &mut |node| {
            has_jump_entry |= matches!(
                node.kind(),
                "labeled_statement" | "goto_statement" | "case_statement"
            );
        });
        if has_jump_entry {
            return;
        }
        let mut cursor = block.walk();
        let statements = block.named_children(&mut cursor).collect::<Vec<_>>();
        for (index, statement) in statements.iter().enumerate() {
            let (guards, owner) = if statement.kind() == "declaration" {
                let guards = scoped_lock_guard_ids(node_text(*statement, &file.source));
                let owner = statement
                    .child_by_field_name("declarator")
                    .and_then(|declarator| scoped_lock_declaration_owner(declarator, &file.source));
                (guards, owner)
            } else if let Some((true, guard)) = explicit_lock_operation(*statement, &file.source) {
                (vec![guard], None)
            } else if let Some(guard) = checked_lock_acquisition(*statement, &file.source) {
                (vec![guard], None)
            } else {
                continue;
            };
            let bound_wait = |call: tree_sitter::Node<'_>| {
                waits.calls.contains(&call.start_byte())
                    && statement.child_by_field_name("type").is_some_and(|ty| {
                        field_access::without_template_arguments(node_text(ty, &file.source)).trim()
                            == "std::unique_lock"
                    })
                    && call
                        .child_by_field_name("arguments")
                        .and_then(|arguments| arguments.named_child(0))
                        .is_some_and(|argument| {
                            argument.kind() == "identifier"
                                && owner
                                    .as_ref()
                                    .is_some_and(|owner| node_text(argument, &file.source) == owner)
                        })
            };
            for guard in guards {
                if !scalar_guard_may_be_shared(&guard, *statement, &file.source) {
                    continue;
                }
                let start_line = statement.end_position().row + 2;
                let mut end_line = block.end_position().row;
                let mut deferred_ranges = Vec::new();
                for later in statements.iter().skip(index + 1) {
                    walk_nodes(*later, &mut |node| {
                        if node.kind() == "lambda_expression"
                            && !is_sequential_algorithm_callback(node, &file.source)
                            && !(waits.predicates.contains(&node.start_byte())
                                && node
                                    .parent()
                                    .and_then(|args| args.parent())
                                    .is_some_and(bound_wait))
                        {
                            deferred_ranges
                                .push((node.start_position().row + 1, node.end_position().row + 1));
                        }
                        if let Some((false, released)) = explicit_lock_operation(node, &file.source)
                            && (released == guard
                                || owner.as_ref().is_some_and(|owner| *owner == released))
                        {
                            if let Some(branch) = terminating_error_branch(node, *later) {
                                // This release cannot reach the continuation.
                                // Exclude the whole branch as well: code inside
                                // it may run after releasing the mutex.
                                deferred_ranges.push((
                                    branch.start_position().row + 1,
                                    branch.end_position().row + 1,
                                ));
                                return;
                            }
                            // Even a conditional release invalidates a must-held
                            // proof for every subsequent line in this scope.
                            end_line = end_line.min(node.start_position().row);
                        }
                        if let Some(owner) = &owner
                            && node.kind() == "call_expression"
                            && node
                                .child_by_field_name("arguments")
                                .is_some_and(|arguments| {
                                    token_occurs(node_text(arguments, &file.source), owner)
                                })
                        {
                            if bound_wait(node) {
                                // The standard wait reacquires this lock before
                                // invoking its predicate and before returning.
                                // Nested unknown callbacks and explicit releases
                                // still independently invalidate their ranges.
                                return;
                            }
                            // Passing/moving a unique_lock to an unknown callee
                            // can transfer ownership or unlock it.
                            end_line = end_line.min(node.start_position().row);
                        }
                        if let Some(owner) = &owner
                            && node.kind() == "assignment_expression"
                            && node
                                .child_by_field_name("left")
                                .is_some_and(|left| node_text(left, &file.source).trim() == owner)
                        {
                            end_line = end_line.min(node.start_position().row);
                        }
                    });
                }
                for line_no in start_line..=end_line {
                    if !deferred_ranges
                        .iter()
                        .any(|(start, end)| (*start..=*end).contains(&line_no))
                    {
                        by_line
                            .entry(line_no)
                            .or_insert_with(Vec::new)
                            .push(guard.clone());
                    }
                }
            }
        }
    });
    inherit_local_callback_locksets(file, &mut by_line);
    for guards in by_line.values_mut() {
        guards.sort();
        guards.dedup();
    }
    by_line
}

/// Inline a nonescaping local callback's must-held guards only when every
/// direct call agrees. An unlocked call, deferred body or possible release
/// prevents this proof; callable type/name alone never supplies a guard.
fn inherit_local_callback_locksets(
    file: &ParsedCppFile,
    by_line: &mut HashMap<usize, Vec<String>>,
) {
    if by_line.is_empty() {
        return;
    }
    let Some(tree) = &file.tree else { return };
    let functions = collect_function_regions(file);
    let origins = collect_index_partition_origins(file, &functions);
    let concurrent = concurrent_context_lines(file);
    let mut guard_owners = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "declaration"
            && !scoped_lock_guard_ids(node_text(node, &file.source)).is_empty()
            && let Some(owner) = node
                .child_by_field_name("declarator")
                .and_then(|d| scoped_lock_declaration_owner(d, &file.source))
        {
            guard_owners.insert(owner);
        }
    });
    let mut additions = Vec::new();
    walk_nodes(tree.root_node(), &mut |lambda| {
        if lambda.kind() != "lambda_expression"
            || !local_callback_has_only_sequential_data_calls(lambda, file, &origins, &concurrent)
        {
            return;
        }
        let Some(binding) = lambda.parent() else {
            return;
        };
        let Some(name) = binding
            .child_by_field_name("declarator")
            .or_else(|| binding.child_by_field_name("left"))
        else {
            return;
        };
        let name = node_text(name, &file.source);
        let Some(body) = lambda.child_by_field_name("body") else {
            return;
        };
        if guard_owners
            .iter()
            .any(|owner| token_occurs(node_text(body, &file.source), owner))
        {
            return;
        }
        let mut unsafe_body = false;
        walk_nodes(body, &mut |node| {
            unsafe_body |= node.kind() == "lambda_expression"
                // An unmodelled callee may release a captured/global guard
                // without spelling that guard at this call site. Start with
                // leaf callback bodies rather than assuming call purity.
                || node.kind() == "call_expression"
                || matches!(
                    explicit_lock_operation(node, &file.source),
                    Some((false, _))
                );
        });
        if unsafe_body {
            return;
        }
        let mut enclosing = binding.parent();
        while enclosing.is_some_and(|node| node.kind() != "function_definition") {
            enclosing = enclosing.and_then(|node| node.parent());
        }
        let Some(enclosing) = enclosing else { return };
        let mut common: Option<HashSet<String>> = None;
        walk_nodes(enclosing, &mut |call| {
            if call.kind() != "call_expression"
                || call
                    .child_by_field_name("function")
                    .is_none_or(|callee| node_text(callee, &file.source) != name)
            {
                return;
            }
            let guards = by_line
                .get(&(call.start_position().row + 1))
                .into_iter()
                .flatten()
                .cloned()
                .collect::<HashSet<_>>();
            let mut argument_effect = false;
            if let Some(arguments) = call.child_by_field_name("arguments") {
                walk_nodes(arguments, &mut |node| {
                    argument_effect |= matches!(
                        node.kind(),
                        "call_expression"
                            | "assignment_expression"
                            | "update_expression"
                            | "lambda_expression"
                    );
                });
            }
            let guards = if argument_effect {
                HashSet::new()
            } else {
                guards
            };
            match &mut common {
                Some(common) => common.retain(|guard| guards.contains(guard)),
                None => common = Some(guards),
            }
        });
        let Some(common) = common.filter(|guards| !guards.is_empty()) else {
            return;
        };
        // Access to the guard itself could pass it to an unmodelled releaser.
        if common.iter().any(|guard| {
            identifier_tokens(guard)
                .filter(|token| *token != "this")
                .any(|token| token_occurs(node_text(body, &file.source), token))
        }) {
            return;
        }
        // Line facts cannot distinguish multiple statements on a brace line.
        for line in body.start_position().row + 2..=body.end_position().row {
            additions.push((line, common.clone()));
        }
    });
    for (line, guards) in additions {
        by_line.entry(line).or_default().extend(guards);
    }
}

fn statement_always_exits_function(node: tree_sitter::Node<'_>) -> bool {
    match node.kind() {
        "return_statement" | "throw_statement" => true,
        "compound_statement" => node
            .named_child_count()
            .checked_sub(1)
            .and_then(|index| node.named_child(index as u32))
            .is_some_and(statement_always_exits_function),
        _ => false,
    }
}

/// These overloads invoke the supplied predicate/function synchronously on the
/// caller thread. Argument count excludes execution-policy overloads; unknown
/// wrappers and stored lambdas remain deferred rather than borrowing a lock.
fn is_sequential_algorithm_callback(node: tree_sitter::Node<'_>, source: &str) -> bool {
    let Some(arguments) = node.parent().filter(|n| n.kind() == "argument_list") else {
        return false;
    };
    let Some(call) = arguments.parent().filter(|n| n.kind() == "call_expression") else {
        return false;
    };
    let Some(callee) = call.child_by_field_name("function") else {
        return false;
    };
    let count = match node_text(callee, source) {
        "std::erase_if" => 2,
        "std::for_each" | "std::find_if" | "std::find_if_not" | "std::count_if" | "std::all_of"
        | "std::any_of" | "std::none_of" | "std::remove_if" => 3,
        _ => return false,
    };
    arguments.named_child_count() == count
        && arguments.named_child((count - 1) as u32) == Some(node)
}

fn terminating_error_branch<'a>(
    mut node: tree_sitter::Node<'a>,
    limit: tree_sitter::Node<'a>,
) -> Option<tree_sitter::Node<'a>> {
    while node != limit {
        let parent = node.parent()?;
        // A catch in the same function can resume execution after a throw.
        if parent.kind() == "try_statement" {
            return None;
        }
        if parent.kind() == "if_statement"
            && parent.child_by_field_name("consequence") == Some(node)
            && statement_always_exits_function(node)
        {
            // Do not use a locally caught exception as a function exit.
            let mut ancestor = Some(parent);
            while let Some(scope) = ancestor {
                if scope.kind() == "try_statement" {
                    return None;
                }
                if scope.kind() == "function_definition" {
                    break;
                }
                ancestor = scope.parent();
            }
            return Some(node);
        }
        node = parent;
    }
    None
}

/// A zero-success lock checked by an exiting error branch dominates the
/// continuation. No inference from logging, arbitrary predicates or try-lock.
fn checked_lock_acquisition(node: tree_sitter::Node<'_>, source: &str) -> Option<String> {
    if node.kind() != "if_statement" || node.child_by_field_name("alternative").is_some() {
        return None;
    }
    let failure = node.child_by_field_name("consequence")?;
    if !statement_always_exits_function(failure) {
        return None;
    }
    let mut ancestor = node.parent();
    while let Some(scope) = ancestor {
        if scope.kind() == "try_statement" {
            return None;
        }
        if scope.kind() == "function_definition" {
            break;
        }
        ancestor = scope.parent();
    }
    let mut condition = node.child_by_field_name("condition")?;
    while matches!(
        condition.kind(),
        "condition_clause" | "parenthesized_expression"
    ) {
        if condition.named_child_count() != 1 {
            return None;
        }
        condition = condition.named_child(0)?;
    }
    let call = if condition.kind() == "binary_expression" {
        if node_text(condition.child_by_field_name("operator")?, source) != "!=" {
            return None;
        }
        let left = condition.child_by_field_name("left")?;
        let right = condition.child_by_field_name("right")?;
        if node_text(right, source) == "0" {
            left
        } else if node_text(left, source) == "0" {
            right
        } else {
            return None;
        }
    } else {
        condition
    };
    let callee = call.child_by_field_name("function")?;
    if !matches!(node_text(callee, source), "pthread_mutex_lock" | "mtx_lock") {
        return None;
    }
    explicit_lock_operation(call, source)
        .filter(|(acquire, _)| *acquire)
        .map(|(_, guard)| guard)
}

fn scoped_lock_declaration_owner(
    mut declarator: tree_sitter::Node<'_>,
    source: &str,
) -> Option<String> {
    loop {
        if matches!(declarator.kind(), "identifier" | "field_identifier") {
            return Some(node_text(declarator, source).to_string());
        }
        // CTAD `unique_lock guard(mutex)` can be parsed as a function
        // declarator; the lock declaration context supplies its meaning.
        declarator = declarator.child_by_field_name("declarator")?;
    }
}

/// Only an unconditional, standalone acquisition establishes a new interval.
/// Calls found below a conditional are used only to invalidate an existing
/// interval, never to prove acquisition along every path.
fn explicit_lock_operation(node: tree_sitter::Node<'_>, source: &str) -> Option<(bool, String)> {
    let call = if node.kind() == "expression_statement" {
        node.named_child(0)?
    } else {
        node
    };
    if call.kind() != "call_expression" {
        return None;
    }
    let callee = call.child_by_field_name("function")?;
    if callee.kind() == "field_expression" {
        let method = node_text(callee.child_by_field_name("field")?, source);
        if !matches!(method, "unlock" | "release" | "swap") {
            return None;
        }
        let receiver =
            normalize_scalar_guard_id(node_text(callee.child_by_field_name("argument")?, source))?;
        return Some((false, receiver));
    }
    let acquire = match node_text(callee, source) {
        "pthread_mutex_lock" | "mtx_lock" | "gpr_mu_lock" | "PyMutex_Lock" | "g_mutex_lock"
        | "uv_mutex_lock" => true,
        "pthread_mutex_unlock"
        | "mtx_unlock"
        | "gpr_mu_unlock"
        | "PyMutex_Unlock"
        | "g_mutex_unlock"
        | "uv_mutex_unlock" => false,
        _ => return None,
    };
    let argument = call.child_by_field_name("arguments")?.named_child(0)?;
    Some((
        acquire,
        normalize_scalar_guard_id(node_text(argument, source))?,
    ))
}

fn scalar_guard_may_be_shared(guard: &str, node: tree_sitter::Node<'_>, source: &str) -> bool {
    if !guard.bytes().all(is_ident_continue) {
        return true;
    }
    let mut ancestor = node.parent();
    while let Some(function) = ancestor {
        if function.kind() == "function_definition" {
            let mut local = false;
            walk_nodes(function, &mut |declaration| {
                if !matches!(declaration.kind(), "declaration" | "parameter_declaration")
                    || node_text(declaration, source)
                        .trim_start()
                        .starts_with("static ")
                {
                    return;
                }
                let mut cursor = declaration.walk();
                local |= declaration
                    .children_by_field_name("declarator", &mut cursor)
                    .any(|declarator| {
                        declarator_variable_name(declarator, source).as_deref() == Some(guard)
                    });
            });
            // A stack mutex belongs to each invocation, and a mutex parameter
            // may denote a different lock at each call. Neither is a common
            // lock identity across the candidate's possible callers.
            return !local;
        }
        ancestor = function.parent();
    }
    true
}

fn scoped_lock_guard_ids(line: &str) -> Vec<String> {
    let Some(keyword_offset) = ["lock_guard", "unique_lock", "scoped_lock"]
        .iter()
        .filter_map(|keyword| line.find(keyword))
        .min()
    else {
        return Vec::new();
    };
    let suffix = &line[keyword_offset..];
    let lower = suffix.to_ascii_lowercase();
    if lower.contains("defer_lock") || lower.contains("try_to_lock") {
        return Vec::new();
    }
    let Some(open) = suffix.find('(').or_else(|| suffix.find('{')) else {
        return Vec::new();
    };
    let delimiter = suffix.as_bytes()[open];
    let close_delimiter = if delimiter == b'(' { ')' } else { '}' };
    let Some(close) = suffix[open + 1..].find(close_delimiter) else {
        return Vec::new();
    };
    split_call_arguments(&suffix[open + 1..open + 1 + close])
        .into_iter()
        .filter(|argument| {
            !matches!(
                argument.trim(),
                "std::adopt_lock" | "adopt_lock" | "std::defer_lock" | "defer_lock"
            )
        })
        .filter_map(|argument| normalize_scalar_guard_id(&argument))
        .collect()
}

fn normalize_scalar_guard_id(expression: &str) -> Option<String> {
    let compact = expression
        .trim()
        .trim_start_matches('&')
        .replace(char::is_whitespace, "")
        .replace("this->", "");
    if compact.is_empty()
        || compact.contains('[')
        || compact.contains('(')
        || compact.contains('?')
        || compact.contains(',')
        || !compact.bytes().all(|byte| {
            byte == b'_'
                || byte == b'.'
                || byte == b'-'
                || byte == b'>'
                || byte.is_ascii_alphanumeric()
        })
    {
        return None;
    }
    Some(compact)
}

fn is_non_contiguous_index_type(type_text: &str) -> bool {
    let compact = type_text.replace(' ', "").to_ascii_lowercase();
    [
        "std::map<",
        "std::multimap<",
        "std::unordered_map<",
        "std::set<",
        "std::multiset<",
        "std::unordered_set<",
        "absl::flat_hash_map<",
        "absl::node_hash_map<",
        "folly::f14",
        "nlohmann::json",
        "poco::json",
    ]
    .iter()
    .any(|kind| compact.contains(kind))
}

fn collect_legacy_function_regions(
    file: &ParsedCppFile,
    parsed: &[FunctionRegion],
) -> Vec<FunctionRegion> {
    let lines: Vec<&str> = file.source.lines().collect();
    let mut functions = Vec::new();
    let mut scopes = Vec::new();
    let mut idx = 0usize;
    while idx < lines.len() {
        let line = lines[idx].trim();
        let at_namespace_scope = scopes.iter().all(|is_namespace| *is_namespace);
        let looks_like_function = at_namespace_scope
            && !is_comment_only_line(line)
            && line.contains('(')
            && line.contains(')')
            && !line.ends_with(';')
            && !line.starts_with('#')
            && !line.starts_with("if")
            && !line.starts_with("for")
            && !line.starts_with("while")
            && !line.starts_with("switch")
            && !line.starts_with("return");
        if looks_like_function
            && let Some(name) = callable_name(line)
            && let Some(open_idx) =
                (idx..(idx + 24).min(lines.len())).find(|candidate| lines[*candidate].contains('{'))
        {
            let end_idx = braced_scope_end(&lines, open_idx);
            let body_start_line = open_idx + 1;
            if end_idx > open_idx
                && !parsed.iter().any(|function| {
                    function.body_start_line == body_start_line
                        && function.body_end_line == end_idx + 1
                })
            {
                functions.push(FunctionRegion {
                    name,
                    declarator: line.to_string(),
                    signature: lines[idx..open_idx].join("\n"),
                    body_start_line,
                    body_end_line: end_idx + 1,
                });
            }
            idx = end_idx + 1;
            continue;
        }
        update_scope_stack(lines[idx], &mut scopes);
        idx += 1;
    }
    functions
}

fn callable_name(declarator: &str) -> Option<String> {
    let before_args = declarator.split('(').next()?.trim();
    identifier_tokens(before_args)
        .last()
        .filter(|name| {
            !matches!(
                *name,
                "for" | "if" | "while" | "switch" | "catch" | "sizeof" | "alignof"
            )
        })
        .map(ToOwned::to_owned)
}

fn function_definition_name(node: tree_sitter::Node<'_>, file: &ParsedCppFile) -> Option<String> {
    let declarator = node.child_by_field_name("declarator")?;
    let text = node_text(declarator, &file.source);
    if text.contains('(') {
        return callable_name(text);
    }
    // A trailing annotation macro can be misparsed as the declarator. Recover
    // from the actual signature, never from an annotation's spelling.
    let body = node.child_by_field_name("body")?;
    let signature = &file.source[node.start_byte()..body.start_byte()];
    signature
        .contains('(')
        .then(|| callable_name(signature))
        .flatten()
}

/// A narrow pre-escape proof for native and std::array automatic storage. Never infer privacy
/// merely from a local pointer: it may address shared storage. A nested team or
/// callback also invalidates this proof, since it may share the enclosing stack.
fn ownership_parse_without_alignment_macros(
    file: &ParsedCppFile,
    macros: &HashMap<String, usize>,
) -> Option<ParsedCppFile> {
    let tree = file.tree.as_ref()?;
    let mut source = file.source.as_bytes().to_vec();
    let mut changed = false;
    walk_nodes(tree.root_node(), &mut |node| {
        if matches!(node.kind(), "identifier" | "type_identifier")
            && macros
                .get(node_text(node, &file.source))
                .is_some_and(|begin| node.start_byte() >= *begin)
        {
            source[node.byte_range()].fill(b' ');
            changed = true;
        }
    });
    if !changed {
        return None;
    }
    let source = String::from_utf8(source).ok()?;
    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(&tree_sitter_cpp::LANGUAGE.into())
        .ok()?;
    let tree = parser.parse(&source, None)?;
    Some(ParsedCppFile {
        path: file.path.clone(),
        source,
        tree: Some(tree),
        is_c: file.is_c,
        allow_internal_linkage_proof: file.allow_internal_linkage_proof,
    })
}

/// A native automatic array may be shared by an OpenMP team yet have no
/// overlapping accesses: one critical block, optionally followed by one
/// single block after an unconditional barrier. This execution proof is
/// separate from the caller's complete scalar-use/nonescape check.
fn serialized_worksharing_array(
    file: &ParsedCppFile,
    declaration: tree_sitter::Node<'_>,
    scope: tree_sitter::Node<'_>,
    name: &str,
    macro_tokens: &HashSet<String>,
) -> bool {
    let source = &file.source;
    if macro_tokens.contains(name) {
        return false;
    }
    let blocks = scope
        .named_children(&mut scope.walk())
        .filter(|node| {
            node.kind() == "compound_statement"
                && node.start_byte() > declaration.end_byte()
                && preceding_omp_directive(*node, source).as_deref() == Some("parallel")
        })
        .collect::<Vec<_>>();
    for parallel in blocks {
        let mut critical = Vec::new();
        let mut singles = Vec::new();
        walk_nodes(parallel, &mut |block| {
            if !matches!(block.kind(), "compound_statement" | "for_statement") {
                return;
            }
            let Some(directive) = preceding_omp_directive(block, source) else {
                return;
            };
            if directive == "critical"
                || directive
                    .strip_prefix("critical")
                    .map(str::trim)
                    .and_then(|s| s.strip_prefix('('))
                    .and_then(|s| s.strip_suffix(')'))
                    .is_some_and(|s| {
                        let s = s.trim();
                        !s.is_empty()
                            && !s.starts_with(|c: char| c.is_ascii_digit())
                            && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                    })
            {
                critical.push(block);
            } else if directive == "single" && block.kind() == "compound_statement" {
                singles.push(block);
            }
        });
        // Multiple critical sites can use different locks. Multiple single
        // sites can select different threads. Do not collapse those domains.
        if critical.len() != 1 || singles.len() > 1 {
            continue;
        }
        let critical = critical[0];
        let single = singles.first().copied();
        // A common ordinary conditional may enclose the complete phase.
        // Loops/tasks/nested parallel regions could overlap another phase.
        let mut ancestor = critical.parent();
        let mut same_phase = false;
        while let Some(node) = ancestor {
            if node == parallel {
                same_phase = true;
                break;
            }
            if !matches!(
                node.kind(),
                "compound_statement" | "if_statement" | "else_clause"
            ) || preceding_omp_directive(node, source).is_some()
            {
                break;
            }
            ancestor = node.parent();
        }
        if !same_phase || single.is_some_and(|s| s.parent() != critical.parent()) {
            continue;
        }
        if let Some(single) = single {
            if single.start_byte() <= critical.end_byte() {
                continue;
            }
            let gap = source[critical.end_byte()..single.start_byte()]
                .lines()
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .collect::<Vec<_>>();
            let direct = ["#pragma omp barrier", "#pragma omp single"];
            let guarded = [
                "#ifdef _OPENMP",
                "#pragma omp barrier",
                "#endif",
                "#ifdef _OPENMP",
                "#pragma omp single",
                "#endif",
            ];
            if gap != direct && gap != guarded {
                continue;
            }
        }
        let regions = std::iter::once(critical).chain(single).collect::<Vec<_>>();
        if regions.iter().any(|region| {
            region.has_error() || automatic_storage_scope_may_fork(node_text(*region, source))
        }) {
            continue;
        }
        let mut valid = true;
        let mut seen = false;
        walk_nodes(scope, &mut |usage| {
            if usage.start_byte() <= declaration.end_byte() {
                return;
            }
            if matches!(usage.kind(), "goto_statement" | "labeled_statement") {
                valid = false;
            }
            if usage.kind() == "identifier" && node_text(usage, source) == name {
                seen = true;
                valid &= regions.iter().any(|region| {
                    region.start_byte() < usage.start_byte() && usage.end_byte() < region.end_byte()
                });
            }
        });
        if valid && seen {
            return true;
        }
    }
    false
}

/// Accept direct directives and the exact conventional _OPENMP wrapper.
/// Other conditionals cannot establish that synchronization is enabled.
fn preceding_omp_directive(node: tree_sitter::Node<'_>, source: &str) -> Option<String> {
    let prefix = &source[..node.start_byte()];
    if !prefix.rsplit_once('\n')?.1.trim().is_empty() {
        return None;
    }
    let mut lines = prefix
        .lines()
        .rev()
        .map(str::trim)
        .filter(|s| !s.is_empty());
    let last = lines.next()?;
    let directive = if last == "#endif" {
        let directive = lines.next()?;
        if lines.next()? != "#ifdef _OPENMP" {
            return None;
        }
        directive
    } else {
        last
    };
    directive.strip_prefix("#pragma omp ").map(str::to_owned)
}

fn private_array_ranges(
    file: &ParsedCppFile,
    memory_arguments: Option<&HashSet<usize>>,
) -> Vec<(String, usize, usize)> {
    let mut ranges = Vec::new();
    let scalar_macros = scalar_macros::collect(file);
    let scalar_calls = scalar_calls::collect(file);
    let functions = collect_function_regions(file);
    let Some(tree) = &file.tree else {
        return ranges;
    };
    let mut macro_names = HashSet::new();
    let mut macro_tokens = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if matches!(node.kind(), "preproc_def" | "preproc_function_def")
            && let Some(name) = node.child_by_field_name("name")
        {
            macro_names.insert(node_text(name, &file.source).to_owned());
            macro_tokens
                .extend(identifier_tokens(node_text(node, &file.source)).map(str::to_owned));
        }
    });
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "declaration" {
            return;
        }
        // Loop initializers and recovered declaration syntax have different
        // binding extents; only prove ordinary block declarations here.
        if node
            .parent()
            .is_none_or(|parent| parent.kind() != "compound_statement")
        {
            return;
        }
        let text = node_text(node, &file.source);
        let Some(ty) = node.child_by_field_name("type") else {
            return;
        };
        let inline_std_array = node_text(ty, &file.source)
            .split_whitespace()
            .collect::<String>()
            .starts_with("std::array<");
        if !inline_std_array && !matches!(ty.kind(), "primitive_type" | "sized_type_specifier") {
            return;
        }
        if identifier_tokens(text).any(|token| matches!(token, "static" | "extern")) {
            return;
        }
        let mut ancestor = node.parent();
        let mut scope = None;
        let mut callable = false;
        while let Some(parent) = ancestor {
            if scope.is_none() && parent.kind() == "compound_statement" {
                scope = Some(parent);
            }
            if matches!(parent.kind(), "function_definition" | "lambda_expression") {
                callable = true;
                break;
            }
            ancestor = parent.parent();
        }
        // Macro-decorated function signatures can recover as namespace-level
        // compound statements. Reuse the bounded function-region recovery,
        // rather than treating their automatic arrays as project storage.
        callable |= functions.iter().any(|function| {
            function.body_start_line < node.start_position().row + 1
                && node.end_position().row < function.body_end_line
        });
        let Some(scope) = scope.filter(|_| callable) else {
            return;
        };
        let remainder = &file.source[node.end_byte()..scope.end_byte()];
        let scope_may_fork = automatic_storage_scope_may_fork(remainder);
        let mut cursor = node.walk();
        for declarator in node.children_by_field_name("declarator", &mut cursor) {
            let mut inner = declarator;
            if inner.kind() == "init_declarator" {
                let Some(value) = inner.child_by_field_name("declarator") else {
                    continue;
                };
                inner = value;
            }
            if inner.kind() != "array_declarator" && !inline_std_array {
                continue;
            }
            let mut array_rank = 0;
            while inner.kind() == "array_declarator" {
                array_rank += 1;
                let Some(value) = inner.child_by_field_name("declarator") else {
                    break;
                };
                inner = value;
            }
            if inner.kind() != "identifier" {
                continue;
            }
            let name = node_text(inner, &file.source);
            if scope_may_fork
                && (inline_std_array
                    || !serialized_worksharing_array(file, node, scope, name, &macro_tokens))
            {
                continue;
            }
            if identifier_tokens(text)
                .filter(|token| *token == name)
                .count()
                != 1
            {
                continue;
            }
            let mut first_escape_line = scope.end_position().row + 2;
            let escape_cutoff = |usage: tree_sitter::Node<'_>| {
                let mut cutoff = usage.start_position().row + 1;
                let mut ancestor = usage.parent();
                while let Some(parent) = ancestor {
                    // Publication on a previous iteration can reach stores
                    // lexically before the publication on the next iteration.
                    // Only loops entered after this array was declared carry
                    // the same object's escaped state across that backedge.
                    if matches!(
                        parent.kind(),
                        "for_statement" | "for_range_loop" | "while_statement" | "do_statement"
                    ) && parent.start_byte() >= node.end_byte()
                    {
                        cutoff = cutoff.min(parent.start_position().row + 1);
                    }
                    if parent == scope {
                        break;
                    }
                    ancestor = parent.parent();
                }
                cutoff
            };
            walk_nodes(scope, &mut |usage| {
                if usage.start_byte() <= node.end_byte()
                    || usage.kind() != "identifier"
                    || node_text(usage, &file.source) != name
                {
                    return;
                }
                if !inline_std_array
                    && scalar_macros::queries_array_size(&scalar_macros, usage, &file.source)
                {
                    return;
                }
                if !inline_std_array
                    && memory_arguments.is_some_and(|uses| uses.contains(&usage.start_byte()))
                {
                    return;
                }
                let Some(parent) = usage.parent() else {
                    first_escape_line = first_escape_line.min(escape_cutoff(usage));
                    return;
                };
                // Querying the size of this array does not pass its address.
                // Restrict this to a bare (possibly parenthesized) operand:
                // other sizeof operands can contain evaluated VLA expressions
                // in C. A visible keyword macro invalidates the source proof.
                let mut size_operand = usage;
                while let Some(outer) = size_operand.parent() {
                    if outer.kind() != "parenthesized_expression" {
                        break;
                    }
                    size_operand = outer;
                }
                if !macro_names.contains("sizeof")
                    && size_operand
                        .parent()
                        .is_some_and(|outer| outer.kind() == "sizeof_expression")
                {
                    return;
                }
                if parent.kind() != "subscript_expression"
                    || parent.child_by_field_name("argument") != Some(usage)
                {
                    first_escape_line = first_escape_line.min(escape_cutoff(usage));
                    return;
                }
                let mut element = parent;
                let mut indexed_rank = 1;
                while let Some(outer) = element.parent() {
                    if outer.kind() != "subscript_expression"
                        || outer.child_by_field_name("argument") != Some(element)
                    {
                        break;
                    }
                    indexed_rank += 1;
                    element = outer;
                }
                let mut ancestor = element.parent();
                while let Some(outer) = ancestor {
                    if !inline_std_array
                        && indexed_rank == array_rank
                        && outer.kind() == "argument_list"
                        && scalar_calls::consumes_value(&scalar_calls, outer, element, &file.source)
                    {
                        break;
                    }
                    if !file.is_c
                        && !inline_std_array
                        && indexed_rank == array_rank
                        && outer.kind() == "binary_expression"
                        && !["left", "right"].iter().all(|side| {
                            outer.child_by_field_name(side).is_some_and(|operand| {
                                primitive_local_operand(operand, &file.source)
                            })
                        })
                    {
                        // An unresolved overloaded operator can retain the
                        // original lvalue before a later cast/copy takes place.
                        first_escape_line = first_escape_line.min(escape_cutoff(outer));
                        break;
                    }
                    if !inline_std_array
                        && outer.kind() == "argument_list"
                        && scalar_macros::preserves_array(
                            &scalar_macros,
                            outer,
                            &file.source,
                            name,
                            array_rank,
                        )
                    {
                        // The body and every operand are scalar-only. Keep
                        // walking so a deferred enclosing lambda still escapes.
                        ancestor = outer.parent().and_then(|call| call.parent());
                        continue;
                    }
                    // Built-in arithmetic, scalar casts and initialization of
                    // a primitive value consume the element's value. Neither
                    // that prvalue nor the independent scalar copy publishes
                    // the array's address. Require complete indexing: a row
                    // of a multidimensional array still decays to a pointer.
                    // User-defined conversions and reference bindings do not
                    // establish this ownership proof.
                    if !inline_std_array
                        && indexed_rank == array_rank
                        && ((outer.kind() == "binary_expression"
                            && (file.is_c
                                || ["left", "right"].iter().all(|side| {
                                    outer.child_by_field_name(side).is_some_and(|operand| {
                                        primitive_local_operand(operand, &file.source)
                                    })
                                })))
                            || (outer.kind() == "init_declarator"
                                && outer
                                    .child_by_field_name("declarator")
                                    .is_some_and(|decl| decl.kind() == "identifier")
                                && outer.parent().is_some_and(|decl| {
                                    decl.kind() == "declaration"
                                        && decl.child_by_field_name("type").is_some_and(|ty| {
                                            matches!(
                                                ty.kind(),
                                                "primitive_type" | "sized_type_specifier"
                                            )
                                        })
                                }))
                            || (outer.kind() == "cast_expression"
                                && outer.child_by_field_name("type").is_some_and(|cast| {
                                    let text = node_text(cast, &file.source);
                                    !text.contains(['*', '&'])
                                        && cast.child_by_field_name("type").is_some_and(|ty| {
                                            matches!(
                                                ty.kind(),
                                                "primitive_type" | "sized_type_specifier"
                                            )
                                        })
                                })))
                    {
                        // A prvalue formed inside a deferred lambda still
                        // reads the original array when the lambda executes.
                        // Do not let value conversion erase capture/ERROR
                        // boundaries outside the expression itself.
                        let mut context = outer.parent();
                        while let Some(enclosing) = context {
                            if enclosing.kind() == "call_expression"
                                && enclosing
                                    .child_by_field_name("function")
                                    .is_some_and(|callee| {
                                        macro_names.contains(node_text(callee, &file.source))
                                    })
                                && !enclosing.child_by_field_name("arguments").is_some_and(
                                    |arguments| {
                                        scalar_macros::preserves_array(
                                            &scalar_macros,
                                            arguments,
                                            &file.source,
                                            name,
                                            array_rank,
                                        )
                                    },
                                )
                            {
                                // Unparenthesized substitution can turn x+1
                                // into &x+1. The raw argument AST alone does
                                // not establish a value conversion in a macro.
                                first_escape_line = first_escape_line.min(escape_cutoff(enclosing));
                                break;
                            }
                            if matches!(enclosing.kind(), "lambda_expression" | "ERROR") {
                                first_escape_line = first_escape_line.min(escape_cutoff(enclosing));
                                break;
                            }
                            if enclosing == scope {
                                break;
                            }
                            context = enclosing.parent();
                        }
                        break;
                    }
                    if matches!(
                        outer.kind(),
                        "pointer_expression"
                            | "return_statement"
                            | "call_expression"
                            | "argument_list"
                            | "init_declarator"
                            | "lambda_expression"
                            | "ERROR"
                    ) {
                        first_escape_line = first_escape_line.min(escape_cutoff(outer));
                        break;
                    }
                    if outer == scope {
                        break;
                    }
                    ancestor = outer.parent();
                }
            });
            // Shared team storage needs a whole-lifetime nonescape proof:
            // a later publication can overlap another thread's earlier block.
            if scope_may_fork && first_escape_line <= scope.end_position().row + 1 {
                continue;
            }
            // A later handoff does not retroactively make earlier stores
            // shared. End the privacy proof before the first possible escape;
            // same-line publication stays unresolved conservatively.
            if first_escape_line > node.start_position().row + 1 {
                ranges.push((
                    name.to_string(),
                    node.start_position().row + 1,
                    first_escape_line - 1,
                ));
            }
        }
    });
    ranges
}

/// Resolve just enough lexical type information to distinguish built-in
/// scalar arithmetic from operators that can retain a reference to an operand.
pub(super) fn primitive_local_operand(operand: tree_sitter::Node<'_>, source: &str) -> bool {
    primitive_local_operand_at_depth(operand, source, 0)
}

fn primitive_local_operand_at_depth(
    mut operand: tree_sitter::Node<'_>,
    source: &str,
    depth: usize,
) -> bool {
    if depth >= 16 {
        return false;
    }
    while operand.kind() == "parenthesized_expression" {
        let Some(inner) = operand.named_child(0) else {
            return false;
        };
        operand = inner;
    }
    if matches!(
        operand.kind(),
        "number_literal" | "char_literal" | "true" | "false" | "sizeof_expression"
    ) {
        return true;
    }
    if operand.kind() == "binary_expression" {
        return ["left", "right"].iter().all(|side| {
            operand
                .child_by_field_name(side)
                .is_some_and(|part| primitive_local_operand_at_depth(part, source, depth + 1))
        });
    }
    let use_site = operand;
    while operand.kind() == "parenthesized_expression" {
        let Some(inner) = operand.named_child(0) else {
            return false;
        };
        operand = inner;
    }
    let mut indexed = 0;
    while operand.kind() == "subscript_expression" {
        indexed += 1;
        let Some(inner) = operand.child_by_field_name("argument") else {
            return false;
        };
        operand = inner;
    }
    if operand.kind() != "identifier" {
        return false;
    }
    let name = node_text(operand, source);
    let matches_type = |declaration: tree_sitter::Node<'_>,
                        mut declarator: tree_sitter::Node<'_>| {
        if !declaration
            .child_by_field_name("type")
            .is_some_and(|ty| matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
        {
            return false;
        }
        if declarator.kind() == "init_declarator" {
            let Some(inner) = declarator.child_by_field_name("declarator") else {
                return false;
            };
            declarator = inner;
        }
        let mut rank = 0;
        while matches!(
            declarator.kind(),
            "array_declarator" | "pointer_declarator" | "parenthesized_declarator"
        ) {
            if declarator.kind() != "parenthesized_declarator" {
                rank += 1;
            }
            let Some(inner) = declarator.child_by_field_name("declarator") else {
                return false;
            };
            declarator = inner;
        }
        declarator.kind() == "identifier" && rank == indexed
    };
    let mut ancestor = use_site.parent();
    while let Some(scope) = ancestor {
        if scope.kind() == "compound_statement" {
            let declarations = scope
                .named_children(&mut scope.walk())
                .filter(|n| n.kind() == "declaration" && n.end_byte() < use_site.start_byte())
                .collect::<Vec<_>>();
            for declaration in declarations.into_iter().rev() {
                for declarator in
                    declaration.children_by_field_name("declarator", &mut declaration.walk())
                {
                    if declarator_variable_name(declarator, source).as_deref() == Some(name) {
                        return matches_type(declaration, declarator);
                    }
                    if declarator_variable_name(declarator, source).is_none()
                        && token_occurs(node_text(declarator, source), name)
                    {
                        return false;
                    }
                }
            }
        }
        if matches!(
            scope.kind(),
            "for_statement"
                | "for_range_loop"
                | "if_statement"
                | "switch_statement"
                | "catch_clause"
        ) {
            if let Some(initializer) = scope.child_by_field_name("initializer")
                && initializer.kind() == "declaration"
            {
                for declarator in
                    initializer.children_by_field_name("declarator", &mut initializer.walk())
                {
                    if declarator_variable_name(declarator, source).as_deref() == Some(name) {
                        return matches_type(initializer, declarator);
                    }
                }
            }
            // Initializer/range/catch bindings shadow outer block variables.
            // Keep these less common binding forms unresolved here.
            if scope
                .child_by_field_name("declarator")
                .is_some_and(|declarator| token_occurs(node_text(declarator, source), name))
            {
                return false;
            }
            for part in scope.named_children(&mut scope.walk()) {
                if part.end_byte() < use_site.start_byte() {
                    let mut shadowed = false;
                    walk_nodes(part, &mut |node| {
                        shadowed |= (node.kind() == "structured_binding_declarator"
                            && token_occurs(node_text(node, source), name))
                            || (matches!(
                                node.kind(),
                                "declaration" | "parameter_declaration" | "init_declarator"
                            ) && node
                                .child_by_field_name("declarator")
                                .and_then(|declarator| declarator_variable_name(declarator, source))
                                .as_deref()
                                == Some(name));
                    });
                    if shadowed {
                        return false;
                    }
                }
            }
        }
        if matches!(scope.kind(), "lambda_expression" | "function_definition") {
            if let Some(parameters) = scope
                .child_by_field_name("declarator")
                .and_then(|declarator| declarator.child_by_field_name("parameters"))
            {
                for parameter in parameters.named_children(&mut parameters.walk()) {
                    if let Some(declarator) = parameter.child_by_field_name("declarator")
                        && declarator_variable_name(declarator, source).as_deref() == Some(name)
                    {
                        return matches_type(parameter, declarator);
                    }
                }
            }
            // Do not borrow same-named variables from unrelated callables or
            // implicit captures; unresolved bindings stay unknown.
            return false;
        }
        ancestor = scope.parent();
    }
    false
}

/// Worksharing distributes the current team's implicit tasks; it does not
/// publish a thread's automatic objects to another task. Keep that distinct
/// from nested parallel/task/target constructs. This is only an execution
/// boundary check: ordinary address escapes are still checked separately.
pub(super) fn automatic_storage_scope_may_fork(source: &str) -> bool {
    source.lines().any(|line| {
        let line = line.trim_start();
        if line.starts_with("//") {
            return false;
        }
        if let Some(directive) = line.strip_prefix("#pragma") {
            let directive = directive.trim();
            return !omp_preserves_automatic_storage(directive)
                && !loop_hint_preserves_automatic_storage(directive);
        }
        line.contains("#pragma")
            || identifier_tokens(line).any(|token| token == "goto")
            || contains_concurrency_token(line)
            || contains_parallel_library_token(line)
    })
}

// Loop-unrolling hints replicate instructions, not independently executing
// threads/tasks. Admit only literal hint syntax; arbitrary pragma operands
// could contain macros or refer to storage and remain unresolved.
fn loop_hint_preserves_automatic_storage(directive: &str) -> bool {
    if matches!(directive, "unroll" | "nounroll") {
        return true;
    }
    let positive_literal = |text: &str| {
        let text = text.trim();
        !text.is_empty()
            && text.chars().all(|c| c.is_ascii_digit())
            && text.parse::<u32>().is_ok_and(|value| value > 0)
    };
    if let Some(rest) = directive.strip_prefix("unroll") {
        return (rest.starts_with(char::is_whitespace) && positive_literal(rest))
            || rest
                .trim()
                .strip_prefix('(')
                .and_then(|s| s.strip_suffix(')'))
                .is_some_and(positive_literal);
    }
    let Some(rest) = directive.strip_prefix("clang loop ") else {
        return false;
    };
    let compact = rest.split_whitespace().collect::<String>();
    matches!(
        compact.as_str(),
        "unroll(enable)" | "unroll(disable)" | "unroll(full)"
    ) || compact
        .strip_prefix("unroll_count(")
        .and_then(|s| s.strip_suffix(')'))
        .is_some_and(positive_literal)
}

fn omp_preserves_automatic_storage(directive: &str) -> bool {
    let Some(construct) = directive.strip_prefix("omp ").map(str::trim) else {
        return false;
    };
    if matches!(
        construct,
        "barrier" | "single" | "single nowait" | "critical"
    ) {
        return true;
    }
    if let Some(name) = construct
        .strip_prefix("critical(")
        .and_then(|s| s.strip_suffix(')'))
    {
        return !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    }
    // Admit only scheduling clauses whose syntax cannot reference/publish
    // an array. In particular copyprivate, reductions, user expressions,
    // macro clauses and continued directives remain unresolved.
    let Some(rest) = construct.strip_prefix("for") else {
        return false;
    };
    if !rest.is_empty() && !rest.starts_with(char::is_whitespace) {
        return false;
    }
    rest.chars().all(|c| {
        c.is_ascii_alphanumeric() || c.is_ascii_whitespace() || matches!(c, '(' | ')' | ',')
    }) && identifier_tokens(rest).all(|token| {
        matches!(
            token,
            "simd"
                | "collapse"
                | "schedule"
                | "static"
                | "dynamic"
                | "guided"
                | "auto"
                | "runtime"
                | "nowait"
                | "ordered"
        )
    })
}

fn collect_pthread_worker_field_candidates(
    file: &ParsedCppFile,
    structs: &[CppStructInfo],
    functions: &[FunctionRegion],
    locksets_by_line: &HashMap<usize, Vec<String>>,
    cache_line_size: usize,
    owned_inline_writes: &mut HashSet<(usize, String)>,
) -> Vec<IndexedWriteCandidate> {
    if functions.is_empty() {
        return Vec::new();
    }
    let lines: Vec<&str> = file.source.lines().collect();
    let calls = call_argument_lists(&file.source, "pthread_create");
    let mut candidates = Vec::new();
    for arguments in calls.into_iter().filter(|arguments| arguments.len() >= 4) {
        let Some(worker_name) = callable_identifier(&arguments[2]) else {
            continue;
        };
        let Some(array_name) = first_indexed_symbol(&arguments[3]) else {
            continue;
        };
        if !arguments[3].contains('&')
            || symbol_has_cache_line_protection(&file.source, &array_name, cache_line_size)
        {
            continue;
        }
        let Some(worker) = functions.iter().find(|region| region.name == worker_name) else {
            continue;
        };
        let worker_start = worker.body_start_line.saturating_sub(1).min(lines.len());
        let worker_end = worker.body_end_line.min(lines.len()).max(worker_start);
        let matching_records: Vec<&CppStructInfo> = structs
            .iter()
            .filter(|record| record.file == file.path)
            .filter(|record| !record.is_cache_aligned && !record.has_cache_padding)
            .filter(|record| {
                worker.signature.contains(&record.name)
                    || lines[worker_start..worker_end]
                        .iter()
                        .any(|line| line.contains(&record.name))
            })
            .filter(|record| record_array_binding(&file.source, &record.name, &array_name))
            .collect();
        if matching_records.len() != 1 {
            continue;
        }
        let record = matching_records[0];
        let body_lines = &lines[worker_start..worker_end];
        let parameters = function_parameters(worker);
        let [parameter] = parameters.as_slice() else {
            continue;
        };
        let receivers = record_pointer_receivers(body_lines, &record.name, parameter);
        if receivers.is_empty() {
            continue;
        }
        let mut emitted_fields = HashSet::new();
        let mut inline_writes = Vec::new();
        for (offset, line) in body_lines.iter().enumerate() {
            let aliases = record_field_aliases(&body_lines[..=offset], record, &receivers);
            for field in &record.fields {
                let directly_mutated = receivers
                    .iter()
                    .any(|receiver| receiver_field_is_mutated(line, receiver, &field.name));
                let alias_mutated = aliases.iter().any(|(alias, aliased_field)| {
                    aliased_field == &field.name && indexed_alias_is_mutated(line, alias)
                });
                if !(directly_mutated || alias_mutated)
                    || !emitted_fields.insert(field.name.clone())
                {
                    continue;
                }
                if field.is_array && !field.is_indirect {
                    let line_number = worker.body_start_line + offset;
                    owned_inline_writes.insert((line_number, field.name.clone()));
                    let kind = indexed_mutations(line)
                        .into_iter()
                        .find(|(name, _, _)| {
                            *name == field.name
                                || aliases
                                    .iter()
                                    .any(|(alias, member)| alias == name && member == &field.name)
                        })
                        .map(|(_, _, kind)| kind)
                        .unwrap_or(CppAccessKind::Write);
                    inline_writes.push((field, line_number, *line, kind));
                    continue;
                }
                candidates.push(IndexedWriteCandidate {
                    file: file.path.clone(),
                    line: worker.body_start_line + offset,
                    snippet: line.trim().to_string(),
                    function_name: Some(worker.name.clone()),
                    record_name: Some(record.name.clone()),
                    record_line: Some(record.line),
                    record_peer: None,
                    record_storage: Some(array_name.clone()),
                    field_name: Some(field.name.clone()),
                    alias_name: None,
                    access_kind: CppAccessKind::Write,
                    has_direct_partition_evidence: true,
                    access_in_concurrent_context: true,
                    guard_ids: locksets_by_line
                        .get(&(worker.body_start_line + offset))
                        .cloned()
                        .unwrap_or_default(),
                    evidence: vec![
                        format!(
                            "并发证据: pthread worker '{}' 接收连续数组 '{}[index]' 的单个元素",
                            worker.name, array_name
                        ),
                        format!(
                            "过程间写证据: worker 经 '{}' 指针写入 '{}.{}'",
                            record.name, record.name, field.name
                        ),
                        "布局证据: worker 参数记录未见 cache-line 对齐或尾部 padding".to_string(),
                    ],
                    storage_identity: None,
                });
            }
        }
        // Only boundary-reaching payload can share with another record.
        // Internal histogram buckets separated by > B from the next object's
        // payload are not a cross-thread pair, even though their names match.
        if let Some(size) = record.total_estimated_size
            && pthread_launches_distinct_records(file, &worker.name, &array_name)
        {
            for (tail, line, snippet, kind) in &inline_writes {
                for (head, head_line, _, head_kind) in &inline_writes {
                    let (Some(offset), Some(bytes), Some(next_offset)) =
                        (tail.offset, tail.estimated_size, head.offset)
                    else {
                        continue;
                    };
                    let Some(gap) = size
                        .checked_add(next_offset)
                        .and_then(|next| next.checked_sub(offset.saturating_add(bytes)))
                    else {
                        continue;
                    };
                    if gap >= cache_line_size.saturating_sub(1) {
                        continue;
                    }
                    candidates.push(IndexedWriteCandidate {
                        file: file.path.clone(), line: *line, snippet: snippet.trim().to_owned(),
                        function_name: Some(worker.name.clone()),
                        record_name: Some(record.name.clone()), record_line: Some(record.line),
                        record_storage: Some(array_name.clone()),
                        record_peer: Some(super::types::CppIndexedPeerAccess {
                            field: head.name.clone(), line: *head_line, kind: head_kind.clone(),
                            guard_ids: locksets_by_line.get(head_line).cloned().unwrap_or_default(),
                        }), field_name: Some(tail.name.clone()),
                        alias_name: None, access_kind: kind.clone(),
                        has_direct_partition_evidence: true, access_in_concurrent_context: true,
                        guard_ids: locksets_by_line.get(line).cloned().unwrap_or_default(),
                        evidence: vec![
                            format!("存储证据: pthread worker '{}' 接收连续数组 '{}[index]' 的独立记录", worker.name, array_name),
                            format!("边界证据: '{}.{}' 尾部与下一记录 '{}.{}' 起部之间间隔 {gap} bytes，小于 B={cache_line_size}", record.name, tail.name, record.name, head.name),
                        ],
                        storage_identity: None,
                    });
                }
            }
        }
    }
    candidates
}

fn pthread_launches_distinct_records(file: &ParsedCppFile, worker: &str, array: &str) -> bool {
    let Some(tree) = &file.tree else { return false };
    let mut found = false;
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "call_expression"
            || node
                .child_by_field_name("function")
                .is_none_or(|f| node_text(f, &file.source) != "pthread_create")
        {
            return;
        }
        let args = call_argument_lists(node_text(node, &file.source), "pthread_create");
        let Some(args) = args.first().filter(|a| a.len() >= 4) else {
            return;
        };
        if callable_identifier(&args[2]).as_deref() != Some(worker) {
            return;
        }
        let accesses = indexed_accesses(&args[3]);
        let Some((storage, index)) = accesses.first() else {
            return;
        };
        if storage != array || identifier_tokens(index).collect::<Vec<_>>() != vec![index.trim()] {
            return;
        }
        let mut parent = node.parent();
        while let Some(n) = parent {
            if n.kind() == "function_definition" {
                break;
            }
            if n.kind() == "for_statement" {
                let update = n
                    .child_by_field_name("update")
                    .map(|v| node_text(v, &file.source).replace(' ', ""));
                let body = n
                    .child_by_field_name("body")
                    .map(|v| node_text(v, &file.source))
                    .unwrap_or("");
                found |= update
                    .is_some_and(|u| u == format!("{index}++") || u == format!("++{index}"))
                    && !body.contains("pthread_join")
                    && !body.lines().any(|line| {
                        simple_assignment_parts(line).is_some_and(|(lhs, _)| lhs.trim() == index)
                    });
                break;
            }
            parent = n.parent();
        }
    });
    found
}

fn call_argument_lists(source: &str, call_name: &str) -> Vec<Vec<String>> {
    let mut calls = Vec::new();
    let bytes = source.as_bytes();
    let mut search_from = 0usize;
    while let Some(relative) = source[search_from..].find(call_name) {
        let name_start = search_from + relative;
        let mut open = name_start + call_name.len();
        // A suffix is not a callee: set != sigfillset/reset, add != fetch_add.
        // This helper also serves thread/atomic APIs, so enforce the boundary
        // before any summary can attach memory effects to a call.
        if name_start > 0
            && (bytes[name_start - 1].is_ascii_alphanumeric() || bytes[name_start - 1] == b'_')
        {
            search_from = open;
            continue;
        }
        while open < bytes.len() && bytes[open].is_ascii_whitespace() {
            open += 1;
        }
        if bytes.get(open) != Some(&b'(') {
            search_from = open.min(bytes.len());
            continue;
        }
        let mut depth = 0i32;
        let mut close = None;
        for (idx, byte) in bytes.iter().enumerate().skip(open) {
            match byte {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        close = Some(idx);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(close) = close else {
            break;
        };
        calls.push(split_call_arguments(&source[open + 1..close]));
        search_from = close + 1;
    }
    calls
}

fn split_call_arguments(arguments: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut start = 0usize;
    let mut paren_depth = 0i32;
    let mut bracket_depth = 0i32;
    let mut brace_depth = 0i32;
    for (idx, byte) in arguments.bytes().enumerate() {
        match byte {
            b'(' => paren_depth += 1,
            b')' => paren_depth -= 1,
            b'[' => bracket_depth += 1,
            b']' => bracket_depth -= 1,
            b'{' => brace_depth += 1,
            b'}' => brace_depth -= 1,
            b',' if paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 => {
                result.push(arguments[start..idx].trim().to_string());
                start = idx + 1;
            }
            _ => {}
        }
    }
    result.push(arguments[start..].trim().to_string());
    result
}

fn callable_identifier(argument: &str) -> Option<String> {
    identifier_tokens(argument)
        .filter(|token| !matches!(*token, "void" | "static_cast" | "reinterpret_cast"))
        .last()
        .map(ToOwned::to_owned)
}

fn first_indexed_symbol(text: &str) -> Option<String> {
    let open = text.find('[')?;
    identifier_before(text, open).map(ToOwned::to_owned)
}

fn record_array_binding(source: &str, record: &str, array: &str) -> bool {
    source.lines().any(|line| {
        token_occurs(line, record)
            && token_occurs(line, array)
            && (line.contains('*') || line.contains('[') || line.contains("sizeof"))
    })
}

fn record_pointer_receivers(lines: &[&str], record: &str, parameter: &str) -> HashSet<String> {
    lines
        .iter()
        .filter_map(|line| {
            let (lhs, rhs) = simple_assignment_parts(line)?;
            let compact = rhs
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>();
            let value = compact.trim_end_matches(';');
            if ![
                format!("({record}*){parameter}"),
                format!("static_cast<{record}*>({parameter})"),
                format!("reinterpret_cast<{record}*>({parameter})"),
            ]
            .contains(&value.to_owned())
            {
                return None;
            }
            identifier_tokens(lhs).last().map(ToOwned::to_owned)
        })
        .collect()
}

fn record_field_aliases(
    lines: &[&str],
    record: &CppStructInfo,
    receivers: &HashSet<String>,
) -> Vec<(String, String)> {
    let mut aliases = Vec::new();
    for line in lines {
        let Some((lhs, rhs)) = simple_assignment_parts(line) else {
            continue;
        };
        let Some(alias) = identifier_tokens(lhs).last() else {
            continue;
        };
        if lhs.contains(['[', ']', '.', '(', ')']) || lhs.contains("->") {
            continue;
        }
        aliases.retain(|(name, _): &(String, String)| name != alias);
        let value = rhs.trim().trim_end_matches(';').trim();
        for receiver in receivers {
            for field in &record.fields {
                if value == format!("{receiver}->{}", field.name)
                    || value == format!("{receiver}.{}", field.name)
                {
                    aliases.push((alias.to_string(), field.name.clone()));
                }
            }
        }
    }
    aliases
}

fn receiver_field_is_mutated(line: &str, receiver: &str, field: &str) -> bool {
    [
        format!("{receiver}->{field}"),
        format!("{receiver}.{field}"),
    ]
    .iter()
    .any(|marker| {
        let Some(offset) = line.find(marker) else {
            return false;
        };
        mutation_follows_access(&line[offset + marker.len()..])
    })
}

fn indexed_alias_is_mutated(line: &str, alias: &str) -> bool {
    let Some(offset) = line.find(alias) else {
        return false;
    };
    let suffix = &line[offset + alias.len()..];
    suffix.trim_start().starts_with('[') && mutation_follows_access(suffix)
}

fn mutation_follows_access(suffix: &str) -> bool {
    let suffix = suffix.trim_start();
    let after_access = if suffix.starts_with('[') {
        suffix
            .find(']')
            .map(|close| &suffix[close + 1..])
            .unwrap_or(suffix)
    } else {
        suffix
    };
    let compact = after_access.trim_start();
    compact.starts_with("++")
        || compact.starts_with("--")
        || compact.starts_with("+=")
        || compact.starts_with("-=")
        || compact.starts_with("*=")
        || compact.starts_with("/=")
        || (compact.starts_with('=') && !compact.starts_with("=="))
        || compact.starts_with(".store(")
        || compact.starts_with(".fetch_")
        || compact.starts_with(".exchange(")
        || compact.starts_with(".compare_exchange")
}

/// Recognize an unpadded per-thread region selected through pointer
/// arithmetic.  This is a topology witness only; callers must additionally
/// prove that the derived pointer is mutated.
fn per_thread_pointer_region(line: &str) -> Option<(String, String)> {
    let lower = line.to_ascii_lowercase();
    if is_comment_only_line(line)
        || !(lower.contains("get_thread_num")
            || lower.contains("thread_id")
            || lower.contains("threadid"))
        || !line.contains('=')
        || !line.contains('+')
        || !line.contains('*')
    {
        return None;
    }
    let (lhs, rhs) = line.split_once('=')?;
    let alias = identifier_tokens(lhs).last()?.to_string();
    let base = rhs.split('+').next()?.trim();
    let storage = identifier_tokens(base).last()?.to_string();
    Some((storage, alias))
}

fn pointer_alias_mutation(
    lines: &[&str],
    declaration_index: usize,
    alias: &str,
    functions: &[FunctionRegion],
) -> Option<CppAccessKind> {
    // Never borrow a mutation from a later function reusing this local name.
    let binding = logical_statement(lines, declaration_index, 6);
    let reference_binding = simple_assignment_parts(&binding)
        .is_some_and(|(lhs, _)| lhs.contains('&'))
        || binding.contains("atomic_ref<");
    let end = functions
        .iter()
        .filter(|function| {
            function.body_start_line <= declaration_index + 1
                && function.body_end_line > declaration_index + 1
        })
        .map(|function| function.body_end_line)
        .min()
        .unwrap_or(declaration_index + 1);
    lines
        .iter()
        .skip(declaration_index + 1)
        .take(end.saturating_sub(declaration_index + 1).min(128))
        .take_while(|line| {
            let Some((lhs, _)) = simple_assignment_parts(line) else {
                return true;
            };
            let lhs = lhs.trim();
            // Rebinding a pointer/view ends the old alias; assignment through
            // a reference does not. A new local declaration shadows either.
            if lhs == alias {
                return reference_binding;
            }
            identifier_tokens(lhs).last() != Some(alias)
                || identifier_tokens(lhs).count() <= 1
                || lhs.contains(['.', '(', '['])
                || lhs.contains("->")
        })
        .filter_map(|line| {
            indexed_mutations(line)
                .into_iter()
                .find_map(|(symbol, _, kind)| (symbol == alias).then_some(kind))
                .or_else(|| {
                    line.match_indices(alias).find_map(|(offset, _)| {
                        let before = &line[..offset];
                        let after = &line[offset + alias.len()..];
                        let identifier = |c: char| c == '_' || c.is_ascii_alphanumeric();
                        if before.chars().next_back().is_some_and(identifier)
                            || after.chars().next().is_some_and(identifier)
                        {
                            return None;
                        }
                        if !reference_binding
                            && !after.trim_start().starts_with(['[', '.'])
                            && !after.trim_start().starts_with("->")
                            && !before.trim_end().ends_with('*')
                        {
                            // p++ changes a local pointer, not p's payload.
                            return None;
                        }
                        // A pointer bound to &array[i] may dereference once
                        // into that element. A reference to a pointer slot may
                        // not: following -> would leave the contiguous slot.
                        if !reference_binding
                            && let Some(member) = after.trim_start().strip_prefix("->")
                        {
                            mutation_kind_around(before, &format!(".{member}"))
                        } else {
                            mutation_kind_around(before, after)
                        }
                    })
                })
                .or_else(|| {
                    call_argument_lists(line, "memset")
                        .into_iter()
                        .any(|arguments| {
                            arguments
                                .first()
                                .is_some_and(|target| target.trim() == alias)
                        })
                        .then_some(CppAccessKind::Write)
                })
                .or_else(|| call_mutates_argument(line, alias, lines, functions))
        })
        .max_by_key(access_kind_strength)
}

fn logical_statement(lines: &[&str], start: usize, limit: usize) -> String {
    let mut statement = String::new();
    for line in lines.iter().skip(start).take(limit) {
        if !statement.is_empty() {
            statement.push(' ');
        }
        statement.push_str(line.trim());
        if line.contains(';') {
            break;
        }
    }
    statement
}

struct ScopedIndexedAliases {
    // Unknown assignments and declarations are kill facts, not missing facts.
    bindings: Vec<(String, usize, usize, Option<String>)>,
}

impl ScopedIndexedAliases {
    fn collect(file: &ParsedCppFile, data_accessor: bool) -> Self {
        let mut bindings = Vec::new();
        if let Some(tree) = &file.tree {
            walk_nodes(tree.root_node(), &mut |node| {
                let (lhs, rhs) = match node.kind() {
                    "init_declarator" => (
                        node.child_by_field_name("declarator"),
                        node.child_by_field_name("value"),
                    ),
                    "assignment_expression" => (
                        node.child_by_field_name("left"),
                        node.child_by_field_name("right"),
                    ),
                    "parameter_declaration" => (node.child_by_field_name("declarator"), None),
                    "declaration" if !node_text(node, &file.source).contains('=') => {
                        (node.child_by_field_name("declarator"), None)
                    }
                    _ => return,
                };
                let Some(lhs) = lhs else { return };
                if !matches!(
                    lhs.kind(),
                    "identifier"
                        | "pointer_declarator"
                        | "reference_declarator"
                        | "array_declarator"
                ) {
                    return;
                }
                let Some(name) = declarator_variable_name(lhs, &file.source) else {
                    return;
                };
                let mut scope = node.parent();
                while scope.is_some_and(|n| {
                    !matches!(
                        n.kind(),
                        "compound_statement"
                            | "function_definition"
                            | "lambda_expression"
                            | "translation_unit"
                    )
                }) {
                    scope = scope.and_then(|n| n.parent());
                }
                let Some(scope) = scope else { return };
                // File-scope aliasing requires linkage/initialization analysis;
                // this resolver only claims ordinary local lexical bindings.
                if scope.kind() == "translation_unit" {
                    return;
                }
                let mut end = scope.end_position().row + 1;
                if node.kind() == "assignment_expression" {
                    // A branch-local reassignment may reach later statements.
                    // Kill the old binding through the callable's end instead
                    // of incorrectly restoring it on leaving the inner block.
                    let mut ancestor = node.parent();
                    while let Some(parent) = ancestor {
                        if matches!(parent.kind(), "function_definition" | "lambda_expression") {
                            end = parent.end_position().row + 1;
                            break;
                        }
                        ancestor = parent.parent();
                    }
                    bindings.push((name.clone(), node.start_position().row + 1, end, None));
                    // Only a standalone assignment establishes a new source.
                    // Its must-binding stops at this lexical block; the kill
                    // fact above still reaches statements after the branch.
                    if !node.parent().is_some_and(|parent| {
                        parent.kind() == "expression_statement" && parent.parent() == Some(scope)
                    }) {
                        return;
                    }
                    end = scope.end_position().row + 1;
                }
                let declared_type = node
                    .parent()
                    .and_then(|parent| parent.child_by_field_name("type"))
                    .or_else(|| node.child_by_field_name("type"))
                    .map(|type_node| node_text(type_node, &file.source))
                    .unwrap_or("");
                let target = rhs.and_then(|rhs| {
                    if data_accessor {
                        // In C a native pointer offset stays in the base
                        // allocation. Preserve that identity for subsequent
                        // indexed stores, rather than reporting the slice and
                        // its backing storage as unrelated objects. C++ may
                        // invoke an overloaded operator, so needs type proof.
                        if file.is_c
                            && lhs.kind() == "pointer_declarator"
                            && rhs.kind() == "binary_expression"
                            && rhs.child_by_field_name("right").is_some_and(|offset| {
                                primitive_local_operand(offset, &file.source)
                                    || (offset.kind() == "binary_expression"
                                        && offset.child_by_field_name("operator").is_some_and(
                                            |operator| {
                                                // C multiplication/division cannot
                                                // produce a pointer, even when an
                                                // operand's declaration is imported.
                                                matches!(
                                                    node_text(operator, &file.source),
                                                    "*" | "/" | "%"
                                                )
                                            },
                                        ))
                            })
                            && rhs.child_by_field_name("operator").is_some_and(|operator| {
                                matches!(node_text(operator, &file.source), "+" | "-")
                            })
                        {
                            let base = rhs.child_by_field_name("left")?;
                            if base.kind() == "identifier" {
                                return Some(node_text(base, &file.source).to_owned());
                            }
                        }
                        // A non-owning span/view is often initialized from an
                        // owning vector's data pointer and then sliced by the
                        // worker rank. Preserve the backing allocation as the
                        // storage identity when the declared view type is a
                        // known contiguous view. This is bounded to a direct
                        // `.data()` receiver; arbitrary factory calls remain
                        // unresolved.
                        if is_contiguous_index_type(declared_type)
                            && let Some(backing) =
                                view_data_backing_symbol(node_text(rhs, &file.source))
                        {
                            return Some(backing);
                        }
                        if rhs.kind() != "call_expression" {
                            return None;
                        }
                        let function = rhs.child_by_field_name("function")?;
                        let args = rhs.child_by_field_name("arguments")?;
                        if args.named_child_count() != 0 || function.kind() != "field_expression" {
                            return None;
                        }
                        if node_text(function.child_by_field_name("field")?, &file.source) != "data"
                        {
                            return None;
                        }
                        let receiver = function.child_by_field_name("argument")?;
                        (receiver.kind() == "identifier")
                            .then(|| node_text(receiver, &file.source).to_string())
                    } else {
                        if rhs.kind() != "field_expression" {
                            return None;
                        }
                        let receiver = rhs.child_by_field_name("argument")?;
                        if receiver.kind() != "identifier" {
                            return None;
                        }
                        Some(node_text(rhs.child_by_field_name("field")?, &file.source).to_string())
                    }
                });
                bindings.push((name, node.start_position().row + 1, end, target));
            });
        }
        Self { bindings }
    }

    fn resolve(&self, name: &str, line: usize) -> Option<&String> {
        self.bindings
            .iter()
            .filter(|(alias, start, end, _)| alias == name && *start <= line && line <= *end)
            .max_by_key(|(_, start, _, _)| *start)
            .and_then(|(_, _, _, target)| target.as_ref())
    }
}

fn inline_array_row_bindings(file: &ParsedCppFile) -> Vec<(String, usize, usize)> {
    // T (*rows)[width] points into one contiguous sequence of inline rows;
    // T **rows and T *rows[N] do not establish that topology.
    let pattern = Regex::new(r"\(\s*\*\s*(?:const\s+)?([A-Za-z_]\w*)\s*\)\s*\[").unwrap();
    let mut bindings = Vec::new();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "declaration" {
                return;
            }
            let text = node_text(node, &file.source);
            let declarator = text.split('=').next().unwrap_or(text);
            for capture in pattern.captures_iter(declarator) {
                let mut scope = node;
                while let Some(parent) = scope.parent() {
                    scope = parent;
                    if scope.kind() == "compound_statement" {
                        break;
                    }
                }
                bindings.push((
                    capture[1].to_string(),
                    node.start_position().row + 1,
                    scope.end_position().row + 1,
                ));
            }
        });
    }
    bindings
}

/// Return the direct object supplying the data pointer to a view constructor.
/// The caller has already established that the declared type is a contiguous
/// view; this helper only accepts a simple `object.data()` first initializer
/// and therefore does not infer storage through arbitrary factories.
fn view_data_backing_symbol(initializer: &str) -> Option<String> {
    let data = initializer.find(".data(")?;
    let receiver = initializer[..data].trim().trim_start_matches('{').trim();
    if receiver.is_empty()
        || receiver.contains(['(', ')', '[', ']', '+', '-', '*', '&', ':'])
        || !receiver.bytes().all(is_ident_continue)
    {
        return None;
    }
    Some(receiver.to_owned())
}

/// A bound atomic RMW exposes a conditional indexed synchronization API.
/// This is not a runtime worker identity: the caller still supplies the index.
/// Require the exact atomic reference, parameter-derived element, and immediate
/// operation together, rather than borrowing an atomic type elsewhere.
fn bound_indexed_atomic_aliases(file: &ParsedCppFile) -> HashMap<usize, (String, String)> {
    let mut aliases = HashMap::new();
    let Some(tree) = &file.tree else {
        return aliases;
    };
    walk_nodes(tree.root_node(), &mut |declaration| {
        if declaration.kind() != "declaration" || declaration.has_error() {
            return;
        }
        let Some(ty) = declaration.child_by_field_name("type") else {
            return;
        };
        let ty = node_text(ty, &file.source)
            .split_whitespace()
            .collect::<String>();
        let Some(arguments) = [
            "std::atomic_ref<",
            "sycl::atomic_ref<",
            "cl::sycl::atomic_ref<",
        ]
        .iter()
        .find_map(|prefix| ty.trim_start_matches("::").strip_prefix(prefix)) else {
            return;
        };
        // Scalar elements only; a reference to a pointer is a different location.
        if !matches!(
            arguments.split([',', '>']).next(),
            Some(
                "int"
                    | "unsigned"
                    | "unsignedint"
                    | "long"
                    | "unsignedlong"
                    | "longlong"
                    | "unsignedlonglong"
            )
        ) {
            return;
        }
        let declarators = declaration
            .children_by_field_name("declarator", &mut declaration.walk())
            .collect::<Vec<_>>();
        let [binding] = declarators.as_slice() else {
            return;
        };
        let (Some(name), Some(value)) = (
            binding.child_by_field_name("declarator"),
            binding.child_by_field_name("value"),
        ) else {
            return;
        };
        if name.kind() != "identifier"
            || !matches!(value.kind(), "argument_list" | "initializer_list")
            || value.named_child_count() != 1
        {
            return;
        }
        let Some(element) = value.named_child(0) else {
            return;
        };
        if element.kind() != "subscript_expression" {
            return;
        }
        let accesses = indexed_accesses(node_text(element, &file.source));
        let [(storage, index)] = accesses.as_slice() else {
            return;
        };
        let mut scope = declaration.parent();
        while scope
            .is_some_and(|n| !matches!(n.kind(), "function_definition" | "lambda_expression"))
        {
            scope = scope.and_then(|n| n.parent());
        }
        let Some(scope) = scope else { return };
        let Some(body) = scope.child_by_field_name("body") else {
            return;
        };
        let mut parameters = HashSet::new();
        walk_nodes(scope, &mut |node| {
            if node.kind() == "parameter_declaration"
                && node.end_byte() <= body.start_byte()
                && let Some(parameter) = node.child_by_field_name("declarator")
                && parameter.kind() == "identifier"
            {
                parameters.insert(node_text(parameter, &file.source));
            }
        });
        let index = index.split_whitespace().collect::<String>();
        let mut coordinate = index.split('.');
        let root = coordinate.next().unwrap_or("");
        if !parameters.contains(root)
            || coordinate.any(|field| field.is_empty() || !field.bytes().all(is_ident_continue))
        {
            return;
        }
        let mut changed = false;
        walk_nodes(body, &mut |node| {
            if node.start_byte() >= declaration.start_byte() {
                return;
            }
            let target = match node.kind() {
                "assignment_expression" => node.child_by_field_name("left"),
                "update_expression" | "pointer_expression" => node.child_by_field_name("argument"),
                "init_declarator" => node.child_by_field_name("declarator"),
                _ => None,
            };
            if target.is_some_and(|target| {
                identifier_tokens(node_text(target, &file.source)).next() == Some(root)
            }) {
                changed = true;
            }
        });
        if changed {
            return;
        }
        let mut next = declaration.next_named_sibling();
        while next.is_some_and(|n| n.kind() == "comment") {
            next = next.and_then(|n| n.next_named_sibling());
        }
        let Some(next) = next else { return };
        if next.has_error() || !matches!(next.kind(), "expression_statement" | "declaration") {
            return;
        }
        let alias = node_text(name, &file.source);
        // No intervening escape, shadowing or rebinding. Exactly one use in
        // the next statement must be the receiver of the recognized operation.
        if identifier_tokens(node_text(next, &file.source))
            .filter(|n| *n == alias)
            .count()
            != 1
        {
            return;
        }
        let mut rmw = false;
        walk_nodes(next, &mut |call| {
            if call.kind() != "call_expression" {
                return;
            }
            let mut parent = call.parent();
            while let Some(node) = parent {
                if node == next {
                    break;
                }
                if matches!(
                    node.kind(),
                    "lambda_expression"
                        | "sizeof_expression"
                        | "decltype"
                        | "noexcept_expression"
                        | "requires_expression"
                ) {
                    return;
                }
                parent = node.parent();
            }
            let Some(callee) = call.child_by_field_name("function") else {
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
            if receiver.kind() == "identifier"
                && node_text(receiver, &file.source) == alias
                && matches!(
                    node_text(method, &file.source),
                    "fetch_add"
                        | "fetch_sub"
                        | "fetch_and"
                        | "fetch_or"
                        | "fetch_xor"
                        | "exchange"
                        | "compare_exchange_weak"
                        | "compare_exchange_strong"
                )
            {
                rmw = true;
            }
        });
        if rmw {
            aliases.insert(
                declaration.start_position().row + 1,
                (storage.clone(), alias.to_owned()),
            );
        }
    });
    aliases
}

fn partitioned_region_alias(
    statement: &str,
    origins: &IndexPartitionOrigins,
    line: usize,
    in_parallel_region: bool,
    inline_array_rows: &[(String, usize, usize)],
) -> Option<(String, String)> {
    let (alias, initializer) = if let Some((lhs, rhs)) = simple_assignment_parts(statement) {
        // A binding must have a simple name, not an indexed assignment target,
        // a for/if condition, or a member expression. Only the initializer
        // supplies the aliased storage; other reads on the line do not.
        if lhs.contains(['[', ']', '(', ')', '.', ';']) || lhs.contains("->") {
            return None;
        }
        let is_reference = lhs.contains('&');
        let takes_address = rhs.trim_start().starts_with('&');
        let is_view = rhs.contains(".slice(") || rhs.contains(".subspan(");
        let is_inline_row = indexed_accesses(rhs).first().is_some_and(|(symbol, _)| {
            inline_array_rows
                .iter()
                .any(|(name, begin, end)| name == symbol && *begin <= line && line <= *end)
        });
        if !is_reference && !takes_address && !is_view && !is_inline_row {
            return None;
        }
        // An opaque call's return value does not alias its indexed argument.
        let before_index = rhs.split('[').next().unwrap_or(rhs);
        if before_index.contains('(') && !before_index.contains(".at(") && !is_view {
            return None;
        }
        (identifier_tokens(lhs).last()?.to_string(), rhs)
    } else {
        if !statement.contains("atomic_ref<") {
            return None;
        }
        let (storage, _) = indexed_accesses(statement).into_iter().next()?;
        let storage_offset = statement.find(&storage)?;
        let prefix = &statement[..storage_offset];
        let open = prefix.rfind('(')?;
        (
            identifier_before(prefix, open)?.to_string(),
            &statement[open + 1..],
        )
    };

    // An alias of *pointers[i] (or pointers[i]->member) names a pointee,
    // not bytes in the contiguous pointer table itself.
    if initializer.trim_start().starts_with('*') {
        return None;
    }
    if let Some(open) = initializer.find('[') {
        let mut depth = 0usize;
        for (offset, ch) in initializer[open..].char_indices() {
            match ch {
                '[' => depth += 1,
                ']' => depth -= 1,
                _ => {}
            }
            if depth == 0 {
                if initializer[open + offset + 1..]
                    .trim_start()
                    .starts_with("->")
                {
                    return None;
                }
                break;
            }
        }
    }
    for (storage, expression) in indexed_accesses(initializer) {
        let explicit_parallel_partition =
            in_parallel_region && identifier_tokens(&expression).any(explicit_partition_parameter);
        if origins.supports(&expression, line) || explicit_parallel_partition {
            return Some((storage, alias));
        }
    }

    let slice = initializer.find(".slice(")?;
    let storage = identifier_before(initializer, slice)?.to_string();
    let arguments = &initializer[slice + ".slice(".len()..];
    if split_call_arguments(arguments)
        .iter()
        .any(|argument| origins.supports(argument, line))
    {
        Some((storage, alias))
    } else {
        None
    }
}

fn partitioned_pointer_stride(
    statement: &str,
    origins: &IndexPartitionOrigins,
    line: usize,
) -> Option<(String, String, String)> {
    let (lhs, rhs) = simple_assignment_parts(statement)?;
    if !rhs.contains('+') || !rhs.contains('*') || !origins.supports(rhs, line) {
        return None;
    }
    let alias = identifier_tokens(lhs).last()?.to_string();
    let (base, offset) = rhs.split_once('+')?;
    let storage = identifier_tokens(base).last()?.to_string();
    let stride = identifier_tokens(offset)
        .filter(|token| {
            let lower = token.to_ascii_lowercase();
            lower.contains("stride") || lower.contains("size") || lower.contains("step")
        })
        .last()?
        .to_string();
    Some((storage, stride, alias))
}

fn partitioned_alias_has_runtime_identity(
    statement: &str,
    origins: &IndexPartitionOrigins,
    line: usize,
) -> bool {
    indexed_accesses(statement)
        .into_iter()
        .any(|(_, expression)| origins.supports_runtime_identity(&expression, line))
        || statement
            .find(".slice(")
            .map(|slice| &statement[slice + ".slice(".len()..])
            .is_some_and(|arguments| {
                split_call_arguments(arguments)
                    .iter()
                    .any(|argument| origins.supports_runtime_identity(argument, line))
            })
}

fn call_mutates_argument(
    call_line: &str,
    argument: &str,
    lines: &[&str],
    functions: &[FunctionRegion],
) -> Option<CppAccessKind> {
    for function in functions {
        for arguments in call_argument_lists(call_line, &function.name) {
            for (position, actual) in arguments.iter().enumerate() {
                if actual.trim() != argument {
                    continue;
                }
                let parameters = function_parameters(function);
                let Some(parameter) = parameters.get(position) else {
                    continue;
                };
                let start = function.body_start_line.saturating_sub(1).min(lines.len());
                let end = function.body_end_line.min(lines.len()).max(start);
                let body = &lines[start..end];
                if let Some(kind) = body.iter().find_map(|line| {
                    indexed_mutations(line)
                        .into_iter()
                        .find_map(|(symbol, _, kind)| (symbol == *parameter).then_some(kind))
                }) {
                    return Some(kind);
                }
            }
        }
    }
    None
}

fn function_parameters(function: &FunctionRegion) -> Vec<String> {
    let signature = if function.declarator.contains('(') {
        function.declarator.as_str()
    } else {
        function.signature.as_str()
    };
    let Some(open) = signature.find('(') else {
        return Vec::new();
    };
    let Some(close) = signature.rfind(')') else {
        return Vec::new();
    };
    if close <= open {
        return Vec::new();
    }
    split_call_arguments(&signature[open + 1..close])
        .into_iter()
        .filter_map(|parameter| identifier_tokens(&parameter).last().map(ToOwned::to_owned))
        .collect()
}

fn collect_partitioned_loop_candidates(
    file: &ParsedCppFile,
    functions: &[FunctionRegion],
    shared_symbols: &HashSet<String>,
    locksets_by_line: &HashMap<usize, Vec<String>>,
    cache_line_size: usize,
) -> Vec<IndexedWriteCandidate> {
    let lines: Vec<&str> = file.source.lines().collect();
    if shared_symbols.is_empty() {
        return Vec::new();
    }
    let mut candidates = Vec::new();
    for function in functions {
        let start = function.body_start_line.saturating_sub(1).min(lines.len());
        let end = function.body_end_line.min(lines.len()).max(start);
        let body_lines = &lines[start..end];
        let worker_ids =
            worker_identifiers(&format!("{} {}", function.declarator, function.signature));
        if worker_ids.is_empty() || !has_parallel_worker_context(body_lines, &function.signature) {
            continue;
        }
        let derived = derived_partition_variables(body_lines, &worker_ids);
        for (offset, line) in body_lines.iter().enumerate() {
            let Some(loop_index) = partitioned_loop_index(line, &derived) else {
                continue;
            };
            let end_offset = braced_scope_end(body_lines, offset);
            for (inner_offset, body_line) in body_lines[offset..=end_offset].iter().enumerate() {
                let mutations = indexed_mutations(body_line);
                for symbol in indexed_symbols_for_expression(body_line, &loop_index) {
                    let Some((_, _, access_kind)) =
                        mutations.iter().find(|(candidate, expression, _)| {
                            candidate == &symbol && expression.trim() == loop_index
                        })
                    else {
                        continue;
                    };
                    if !shared_symbols.contains(&symbol)
                        || symbol_has_cache_line_protection(&file.source, &symbol, cache_line_size)
                    {
                        continue;
                    }
                    candidates.push(IndexedWriteCandidate {
                        file: file.path.clone(),
                        line: function.body_start_line + offset + inner_offset,
                        snippet: body_line.trim().to_string(),
                        function_name: Some(function.name.clone()),
                        record_name: None,
                        record_line: None,
                        record_peer: None,
                        record_storage: None,
                        field_name: Some(symbol),
                        alias_name: None,
                        access_kind: access_kind.clone(),
                        has_direct_partition_evidence: true,
                        access_in_concurrent_context: true,
                        guard_ids: locksets_by_line
                            .get(&(function.body_start_line + offset + inner_offset))
                            .cloned()
                            .unwrap_or_default(),
                        evidence: vec![
                            format!("并发证据: worker 参数 {:?} 推导循环分区边界", worker_ids),
                            format!(
                                "分区写证据: 循环索引 '{}' 只覆盖该 worker 的连续区间",
                                loop_index
                            ),
                            "布局证据: 共享连续数组的线程分区边界未见 cache-line 取整".to_string(),
                        ],
                        storage_identity: None,
                    });
                }
            }
        }
    }
    candidates
}

fn collect_owner_guarded_block_candidates(
    file: &ParsedCppFile,
    functions: &[FunctionRegion],
    shared_symbols: &HashSet<String>,
    locksets_by_line: &HashMap<usize, Vec<String>>,
    cache_line_size: usize,
) -> Vec<IndexedWriteCandidate> {
    let lines: Vec<&str> = file.source.lines().collect();
    let heap_symbols: HashSet<String> = shared_symbols
        .iter()
        .filter(|symbol| symbol_has_dense_heap_allocation(&file.source, symbol))
        .filter(|symbol| !symbol_has_cache_line_protection(&file.source, symbol, cache_line_size))
        .cloned()
        .collect();
    if heap_symbols.is_empty() {
        return Vec::new();
    }
    let file_parallel_worker_runtime = has_parallel_source_marker(&file.source);
    let mut candidates = Vec::new();
    for function in functions {
        let start = function.body_start_line.saturating_sub(1).min(lines.len());
        let end = function.body_end_line.min(lines.len()).max(start);
        let body_lines = &lines[start..end];
        let worker_ids =
            worker_identifiers(&format!("{} {}", function.declarator, function.signature));
        let has_worker_context = has_parallel_worker_context(body_lines, &function.signature)
            || file_parallel_worker_runtime;
        if worker_ids.is_empty() || !has_worker_context {
            continue;
        }
        let mut emitted = HashSet::new();
        for (offset, line) in body_lines.iter().enumerate() {
            if !owner_guard_mentions_worker(line, &worker_ids) {
                continue;
            }
            let end_offset = braced_scope_end(body_lines, offset);
            for (inner_offset, guarded_line) in body_lines[offset..=end_offset].iter().enumerate() {
                let mut mutations = indexed_mutations(guarded_line)
                    .into_iter()
                    .map(|(symbol, index, kind)| (symbol, index, kind, false))
                    .collect::<Vec<_>>();
                // Blocked numerical kernels commonly take the address of an
                // selected array element and hand that pointer to a helper
                // (for example `A = &(a[row]); lu0(A, ...)`).  The indexed
                // lvalue is then mutated in the callee, so it is not visible
                // to the line-local mutation classifier.  An address-taking
                // assignment inside an ownership guard is a bounded write
                // witness; ordinary indexed reads do not satisfy this shape.
                if mutations.is_empty() && guarded_line.contains('&') && guarded_line.contains('=')
                {
                    mutations.extend(indexed_accesses(guarded_line).into_iter().filter_map(
                        |(symbol, index)| {
                            let symbol_offset = guarded_line.find(&symbol)?;
                            let prefix = &guarded_line[..symbol_offset];
                            (prefix.contains('&') && guarded_line.contains('(')).then_some((
                                symbol,
                                index,
                                CppAccessKind::Write,
                                true,
                            ))
                        },
                    ));
                }
                for (symbol, _, access_kind, through_pointer) in mutations {
                    if !heap_symbols.contains(&symbol) || !emitted.insert(symbol.clone()) {
                        continue;
                    }
                    candidates.push(IndexedWriteCandidate {
                        file: file.path.clone(),
                        line: function.body_start_line + offset + inner_offset,
                        snippet: guarded_line.trim().to_string(),
                        function_name: Some(function.name.clone()),
                        record_name: None,
                        record_line: None,
                    record_peer: None,
                    record_storage: None,
                        field_name: Some(symbol),
                        alias_name: None,
                        access_kind,
                        has_direct_partition_evidence: true,
                        access_in_concurrent_context: true,
                        guard_ids: locksets_by_line
                            .get(&(function.body_start_line + offset + inner_offset))
                            .cloned()
                            .unwrap_or_default(),
                        evidence: vec![
                            format!(
                                "并发证据: owner predicate 将共享 block 分配给 worker {:?}",
                                worker_ids
                            ),
                            if through_pointer {
                                "写入证据: owner-selected array element 的地址传入 helper，helper 可能修改该 block"
                                    .to_string()
                            } else {
                                "布局证据: worker 在未对齐 heap 数组中取得独占 block 起始地址"
                                    .to_string()
                            },
                            "边界证据: block 起点/步长未证明按 cache line 对齐".to_string(),
                        ],
                        storage_identity: None,
                    });
                }
            }
        }
    }
    candidates
}

fn global_shared_array_symbols(file: &ParsedCppFile) -> HashSet<String> {
    let mut symbols = HashSet::new();
    let mut scopes = Vec::new();
    for line in file.source.lines() {
        let trimmed = line.trim();
        let declaration = trimmed
            .split("//")
            .next()
            .unwrap_or(trimmed)
            .split("/*")
            .next()
            .unwrap_or(trimmed)
            .trim();
        let at_namespace_scope = scopes.iter().all(|is_namespace| *is_namespace);
        if at_namespace_scope
            && declaration.ends_with(';')
            && !declaration.starts_with('#')
            && !declaration.contains("thread_local")
            && !declaration.contains(" const ")
            && !declaration.contains('(')
            && (declaration.contains('*') || declaration.contains('['))
            && let Some(symbol) = extract_static_candidate_name(declaration)
        {
            symbols.insert(symbol);
        }
        update_scope_stack(line, &mut scopes);
    }
    symbols
}

fn worker_identifiers(text: &str) -> HashSet<String> {
    identifier_tokens(text)
        .filter(|identifier| is_worker_identifier(identifier))
        .map(ToOwned::to_owned)
        .collect()
}

fn is_worker_identifier(identifier: &str) -> bool {
    let lower = identifier.to_ascii_lowercase();
    matches!(
        lower.as_str(),
        "pid" | "tid" | "mynum" | "worker" | "threadid" | "thread_id"
    ) || ((lower.ends_with("_id") || lower.ends_with("_index"))
        && ["worker", "thread", "cpu", "shard", "proc", "process"]
            .iter()
            .any(|token| lower.contains(token)))
}

fn has_parallel_worker_context(lines: &[&str], signature: &str) -> bool {
    let text = lines.join("\n");
    let combined = format!("{signature}\n{text}");
    [
        "pthread_barrier",
        "std::barrier",
        "#pragma omp",
        "omp_get_thread_num",
        "BARRIER(",
        "BARRIER (",
        "barrier.wait",
        "barrier->wait",
    ]
    .iter()
    .any(|token| combined.contains(token))
}

fn has_parallel_source_marker(source: &str) -> bool {
    [
        "pthread_barrier",
        "std::barrier",
        "#pragma omp",
        "omp_get_thread_num",
        "BARRIER(",
        "BARRIER (",
        "barrier.wait",
        "barrier->wait",
    ]
    .iter()
    .any(|token| source.contains(token))
}

fn derived_partition_variables(lines: &[&str], worker_ids: &HashSet<String>) -> HashSet<String> {
    let mut derived = worker_ids.clone();
    for _ in 0..4 {
        let mut changed = false;
        for line in lines {
            let Some((lhs, rhs)) = simple_assignment_parts(line) else {
                continue;
            };
            if !derived.iter().any(|name| token_occurs(rhs, name)) {
                continue;
            }
            if let Some(name) = identifier_tokens(lhs).last()
                && derived.insert(name.to_string())
            {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    derived
}

fn partitioned_loop_index(line: &str, derived: &HashSet<String>) -> Option<String> {
    let trimmed = line.trim_start();
    if !(trimmed.starts_with("for(") || trimmed.starts_with("for (")) {
        return None;
    }
    let open = line.find('(')?;
    let close = line[open + 1..].find(')')? + open + 1;
    let clauses: Vec<&str> = line[open + 1..close].split(';').collect();
    if clauses.len() < 2
        || !derived
            .iter()
            .any(|name| token_occurs(clauses[0], name) || token_occurs(clauses[1], name))
    {
        return None;
    }
    let lhs = clauses[0].split('=').next()?.trim();
    identifier_tokens(lhs).last().map(ToOwned::to_owned)
}

fn braced_scope_end(lines: &[&str], start: usize) -> usize {
    let mut depth = 0i32;
    let mut saw_open = false;
    for (offset, line) in lines.iter().enumerate().skip(start) {
        for byte in line.bytes() {
            match byte {
                b'{' => {
                    depth += 1;
                    saw_open = true;
                }
                b'}' if saw_open => {
                    depth -= 1;
                    if depth == 0 {
                        return offset;
                    }
                }
                _ => {}
            }
        }
        if offset == start && !saw_open {
            return start;
        }
    }
    lines.len().saturating_sub(1)
}

fn indexed_symbols_for_expression(line: &str, expected: &str) -> Vec<String> {
    let mut symbols = Vec::new();
    let mut search_from = 0usize;
    while let Some(relative) = line[search_from..].find('[') {
        let open = search_from + relative;
        let Some(relative_close) = line[open + 1..].find(']') else {
            break;
        };
        let close = open + 1 + relative_close;
        if line[open + 1..close].trim() == expected
            && let Some(symbol) = identifier_before(line, open)
        {
            symbols.push(symbol.to_string());
        }
        search_from = close + 1;
    }
    symbols
}

fn owner_guard_mentions_worker(line: &str, worker_ids: &HashSet<String>) -> bool {
    let trimmed = line.trim_start();
    if !(trimmed.starts_with("if(") || trimmed.starts_with("if ("))
        || !line.contains("==")
        || !worker_ids.iter().any(|name| token_occurs(line, name))
    {
        return false;
    }
    let condition = line
        .split_once('(')
        .map(|(_, suffix)| suffix)
        .unwrap_or(line);
    condition.split("==").any(side_contains_non_control_call)
}

fn side_contains_non_control_call(side: &str) -> bool {
    let bytes = side.as_bytes();
    let mut offset = 0usize;
    while offset < bytes.len() {
        while offset < bytes.len() && !is_ident_start(bytes[offset]) {
            offset += 1;
        }
        let start = offset;
        while offset < bytes.len() && is_ident_continue(bytes[offset]) {
            offset += 1;
        }
        if start == offset {
            continue;
        }
        let identifier = &side[start..offset];
        while offset < bytes.len() && bytes[offset].is_ascii_whitespace() {
            offset += 1;
        }
        if bytes.get(offset) == Some(&b'(')
            && !matches!(identifier, "if" | "for" | "while" | "switch" | "sizeof")
        {
            return true;
        }
    }
    false
}

fn symbol_has_dense_heap_allocation(source: &str, symbol: &str) -> bool {
    source.lines().any(|line| {
        token_occurs(line, symbol)
            && line.contains('=')
            && ["malloc", "calloc", "G_MALLOC", "new "]
                .iter()
                .any(|allocator| line.contains(allocator))
    })
}

fn symbol_has_cache_line_protection(source: &str, symbol: &str, cache_line_size: usize) -> bool {
    source.lines().any(|line| {
        token_occurs(line, symbol) && static_candidate_is_protected(line, cache_line_size)
    })
}

fn simple_assignment_parts(line: &str) -> Option<(&str, &str)> {
    let (lhs, rhs) = line.split_once('=')?;
    let previous = lhs.chars().next_back();
    let next = rhs.chars().next();
    if matches!(
        previous,
        Some('=' | '!' | '<' | '>' | '+' | '-' | '*' | '/' | '%' | '|' | '&' | '^')
    ) || next == Some('=')
    {
        return None;
    }
    Some((lhs, rhs))
}

fn token_occurs(text: &str, expected: &str) -> bool {
    identifier_tokens(text).any(|token| token == expected)
}

fn cache_aligned_receiver_fields(
    file: &ParsedCppFile,
    records: &[&CppStructInfo],
) -> HashSet<(String, String)> {
    let mut protected = HashSet::new();
    if records.is_empty() {
        return protected;
    }
    for declaration in file.source.lines() {
        if !(declaration.contains('*') || declaration.contains('&')) {
            continue;
        }
        for record in records {
            if !token_occurs(declaration, &record.name) {
                continue;
            }
            let lhs = declaration.split('=').next().unwrap_or(declaration);
            let Some(receiver) = identifier_tokens(lhs).last() else {
                continue;
            };
            for field in &record.fields {
                // Aligning the owning record protects its own boundary, not
                // the stride between elements inside an array/vector field.
                // Treating those payloads as protected hid per-lcore arrays
                // embedded in an otherwise cache-aligned control record.
                if !field.is_array
                    && !field.is_indirect
                    && !super::types::has_contiguous_elements(field)
                {
                    protected.insert((receiver.to_string(), field.name.clone()));
                }
            }
        }
    }
    protected
}

fn line_accesses_cache_aligned_record(line: &str, protected: &HashSet<(String, String)>) -> bool {
    if protected.is_empty() {
        return false;
    }
    field_access_tokens(line)
        .into_iter()
        .filter_map(|(receiver, field)| receiver.map(|receiver| (receiver, field)))
        .any(|(receiver, field)| protected.contains(&(receiver.to_string(), field.to_string())))
}

fn source_aligned_type_names(files: &[ParsedCppFile], cache_line_size: usize) -> HashSet<String> {
    let mut names = HashSet::new();
    for line in files.iter().flat_map(|file| file.source.lines()) {
        let lower = line.to_ascii_lowercase();
        let aligned = extract_align_bytes(line).is_some_and(|bytes| bytes >= cache_line_size);
        if !aligned || !(line.contains('}') || lower.contains("struct") || lower.contains("class"))
        {
            continue;
        }
        // Parse the declaration header, not the final identifier on the row.
        // For a one-line record the latter is commonly an embedded field, and
        // treating that field name as an aligned *type* suppresses all later
        // indexed writes to it.
        if let Some(name) = aligned_type_name_from_line(line) {
            names.insert(name);
        }
    }
    names
}

fn source_declared_aligned_type_names(
    files: &[ParsedCppFile],
    cache_line_size: usize,
) -> HashSet<String> {
    files
        .iter()
        .flat_map(|file| file.source.lines())
        .filter(|line| {
            let lower = line.to_ascii_lowercase();
            extract_align_bytes(line).is_some_and(|bytes| bytes >= cache_line_size)
                && (lower.contains("struct") || lower.contains("class"))
        })
        .filter_map(aligned_type_name_from_line)
        .collect()
}

fn aligned_type_name_from_line(line: &str) -> Option<String> {
    let is_type_name = |token: &&str| {
        let upper = token.to_ascii_uppercase();
        !matches!(
            *token,
            "class" | "struct" | "typedef" | "alignas" | "const" | "volatile"
        ) && !upper.contains("ALIGN")
            && !upper.contains("CACHELINE")
            && !upper.contains("CACHE_LINE")
            && !matches!(*token, "LOCAL" | "static")
    };
    let header = line.split('{').next().unwrap_or(line);
    let header_names: Vec<&str> = identifier_tokens(header).filter(is_type_name).collect();
    if let Some(name) = header_names.last()
        && !matches!(*name, "class" | "struct" | "typedef")
    {
        return Some((*name).to_string());
    }
    identifier_tokens(line)
        .filter(is_type_name)
        .last()
        .map(ToOwned::to_owned)
}

pub fn collect_atomic_alias_array_candidates(
    files: &[ParsedCppFile],
) -> Vec<AtomicAliasArrayCandidate> {
    collect_atomic_alias_array_candidates_with_commands(files, &[])
}

pub(super) fn collect_atomic_alias_array_candidates_with_commands(
    files: &[ParsedCppFile],
    commands: &[super::types::CppCompileCommand],
) -> Vec<AtomicAliasArrayCandidate> {
    let runtime_views = super::unevaluated::views(files, commands);
    let files = runtime_views.as_ref();
    let linkage_views = internal_index_api::views(files, commands);
    let files = linkage_views.as_ref();
    let mut candidates = Vec::new();
    for file in files {
        let lines: Vec<&str> = file.source.lines().collect();
        for (alias_idx, line) in lines.iter().enumerate() {
            if is_comment_only_line(line) {
                continue;
            }
            let Some(alias) = atomic_alias_name(line) else {
                continue;
            };
            let storage = lines.iter().enumerate().find_map(|(idx, storage_line)| {
                (idx != alias_idx)
                    .then(|| {
                        alias_contiguous_storage_symbol(storage_line, alias)
                            .map(|symbol| (idx, storage_line, symbol))
                    })
                    .flatten()
            });
            let Some((storage_idx, storage_line, storage_name)) = storage else {
                continue;
            };
            candidates.push(AtomicAliasArrayCandidate {
                file: file.path.clone(),
                line: alias_idx + 1,
                alias: alias.to_string(),
                storage_name,
                snippet: line.trim().to_string(),
                access_file: None,
                access_line: None,
                access_kind: None,
                access_in_concurrent_context: false,
                access_is_mutable_api: false,
                guard_ids: Vec::new(),
                evidence: vec![
                    format!(
                        "布局证据: atomic alias `{alias}` 被连续数组/容器存储: {}:{}",
                        file.path,
                        storage_idx + 1
                    ),
                    format!("存储声明: {}", storage_line.trim()),
                ],
            });
        }
    }
    attach_atomic_alias_access_sites(files, &mut candidates);
    candidates
}

fn atomic_alias_name(line: &str) -> Option<&str> {
    let trimmed = line.trim();
    if !(trimmed.contains("atomic<") || trimmed.contains("atomic <")) {
        return None;
    }
    if let Some(rest) = trimmed.strip_prefix("using ") {
        let (name, rhs) = rest.split_once('=')?;
        return rhs
            .contains("atomic")
            .then(|| name.trim())
            .filter(|name| !name.is_empty() && name.bytes().all(is_ident_continue));
    }
    if let Some(rest) = trimmed.strip_prefix("typedef ") {
        let declaration = rest.split(';').next()?;
        return identifier_tokens(declaration).last().filter(|name| {
            !matches!(*name, "atomic" | "std") && name.bytes().all(is_ident_continue)
        });
    }
    None
}

fn alias_contiguous_storage_symbol(line: &str, alias: &str) -> Option<String> {
    if !contains_identifier(line, alias) {
        return None;
    }
    let compact: String = line
        .chars()
        .filter(|ch| !ch.is_ascii_whitespace())
        .collect();
    let contiguous = compact.contains(&format!("{alias}[]"))
        // A raw pointer is accepted only as a provisional storage shape. The
        // candidate is retained later only when an exact indexed mutation or
        // mutable indexed accessor proves that it denotes element storage.
        || compact.contains(&format!("{alias}*"))
        || compact.contains(&format!("new{alias}["))
        || compact.contains(&format!("vector<{alias}"))
        || compact.contains(&format!("array<{alias}"))
        || compact.contains(&format!("unique_ptr<{alias}[]"))
        || compact.contains(&format!("shared_ptr<{alias}[]"))
        || line
            .find(alias)
            .is_some_and(|offset| line[offset + alias.len()..].contains('['));
    contiguous
        .then(|| extract_static_candidate_name(line))
        .flatten()
}

fn attach_atomic_alias_access_sites(
    files: &[ParsedCppFile],
    candidates: &mut [AtomicAliasArrayCandidate],
) {
    let mut by_storage = HashMap::<String, Vec<usize>>::new();
    for (index, candidate) in candidates.iter().enumerate() {
        by_storage
            .entry(candidate.storage_name.clone())
            .or_default()
            .push(index);
    }
    for file in files {
        let functions = collect_function_regions(file);
        let concurrent_lines = concurrent_context_lines(file);
        let locksets = collect_scoped_locksets(file);
        for (offset, line) in file.source.lines().enumerate() {
            let line_no = offset + 1;
            for (symbol, expression, access_kind) in indexed_mutations(line) {
                let Some(indices) = by_storage.get(&symbol) else {
                    continue;
                };
                let semantic_partition = is_thread_index_expression(&expression);
                let in_concurrent_context =
                    concurrent_lines.contains(&line_no) || semantic_partition;
                if !in_concurrent_context
                    || !(semantic_partition || is_parallel_loop_index_expression(&expression))
                {
                    continue;
                }
                for candidate_index in indices {
                    let candidate = &mut candidates[*candidate_index];
                    let replace = candidate.access_kind.as_ref().is_none_or(|existing| {
                        access_kind_strength(&access_kind) > access_kind_strength(existing)
                    });
                    if replace {
                        candidate.access_file = Some(file.path.clone());
                        candidate.access_line = Some(line_no);
                        candidate.access_kind = Some(access_kind.clone());
                        candidate.access_in_concurrent_context = true;
                        candidate.access_is_mutable_api = false;
                        candidate.guard_ids = locksets.get(&line_no).cloned().unwrap_or_default();
                        candidate.evidence.push(format!(
                            "访问证据: atomic alias storage '{}' 在并发索引 '{}' 上发生写入",
                            symbol, expression
                        ));
                    }
                }
            }
            if !line.trim_start().starts_with("return ") {
                continue;
            }
            for (symbol, _) in indexed_accesses(line) {
                let Some(indices) = by_storage.get(&symbol) else {
                    continue;
                };
                let mutable_accessor = functions.iter().any(|function| {
                    line_no >= function.body_start_line
                        && line_no <= function.body_end_line
                        && signature_returns_mutable_reference(function)
                });
                if !mutable_accessor {
                    continue;
                }
                for candidate_index in indices {
                    let candidate = &mut candidates[*candidate_index];
                    if candidate.access_kind.is_some() {
                        continue;
                    }
                    candidate.access_file = Some(file.path.clone());
                    candidate.access_line = Some(line_no);
                    candidate.access_kind = Some(CppAccessKind::Write);
                    candidate.access_in_concurrent_context = false;
                    candidate.access_is_mutable_api = true;
                    candidate.evidence.push(format!(
                        "API 写能力: 非 const 引用 accessor 返回 atomic storage '{}[index]'",
                        symbol
                    ));
                }
            }
        }
    }
}

fn signature_returns_mutable_reference(function: &FunctionRegion) -> bool {
    let signature = format!("{} {}", function.signature, function.declarator);
    let before_arguments = signature.split('(').next().unwrap_or(&signature);
    before_arguments.contains('&') && !before_arguments.contains("const ")
}

fn contains_identifier(text: &str, identifier: &str) -> bool {
    text.match_indices(identifier).any(|(offset, _)| {
        let before = text[..offset].bytes().next_back();
        let after = text[offset + identifier.len()..].bytes().next();
        !before.is_some_and(is_ident_continue) && !after.is_some_and(is_ident_continue)
    })
}

/// Return only mutations whose target is the indexed expression itself.
///
/// This deliberately rejects lines such as
/// `const auto & value = container[index]`: the line contains `=`, but the
/// indexed expression is on the right-hand side and is therefore a read.
fn indexed_mutations(line: &str) -> Vec<(String, String, CppAccessKind)> {
    let bytes = line.as_bytes();
    let mut mutations = Vec::new();
    let mut open = 0usize;
    while open < bytes.len() {
        let Some(relative) = line[open..].find('[') else {
            break;
        };
        open += relative;
        let mut depth = 1usize;
        let mut close = open + 1;
        while close < bytes.len() && depth > 0 {
            match bytes[close] {
                b'[' => depth += 1,
                b']' => depth -= 1,
                _ => {}
            }
            close += 1;
        }
        if depth != 0 {
            break;
        }
        let close_bracket = close - 1;
        let Some(symbol) = identifier_before(line, open) else {
            open = close;
            continue;
        };
        let expression = line[open + 1..close_bracket].trim();
        let symbol_start = line[..open].rfind(symbol).unwrap_or(open);
        // An array declarator's extent is not an indexed access, and writing a
        // pointee does not mutate the pointer array's contiguous storage.
        if expression.is_empty()
            || indexed_target_is_declaration(&line[..symbol_start])
            || line[close_bracket + 1..].trim_start().starts_with("->")
        {
            open = close;
            continue;
        }
        if let Some(kind) = mutation_kind_around(&line[..symbol_start], &line[close_bracket + 1..])
        {
            mutations.push((symbol.to_string(), expression.to_string(), kind));
        }
        open = close;
    }
    for mutation in macro_indexed_mutations(line) {
        if !mutations
            .iter()
            .any(|existing| existing.0 == mutation.0 && existing.1 == mutation.1)
        {
            mutations.push(mutation);
        }
    }
    mutations
}

/// Compiler intrinsics and project atomic wrappers often encode the mutated
/// lvalue as the first macro/function argument.  Only that argument is
/// classified as a mutation; indexed reads in later arguments remain reads.
fn macro_indexed_mutations(line: &str) -> Vec<(String, String, CppAccessKind)> {
    let mut mutations = Vec::new();
    for (call, kind) in [
        ("atomicIncr", CppAccessKind::ReadModifyWrite),
        ("atomicDecr", CppAccessKind::ReadModifyWrite),
        ("atomicAdd", CppAccessKind::ReadModifyWrite),
        ("atomicSub", CppAccessKind::ReadModifyWrite),
        ("atomicSet", CppAccessKind::Write),
        ("atomicSetWithSync", CppAccessKind::Write),
        ("__atomic_store_n", CppAccessKind::Write),
        ("__atomic_fetch_add", CppAccessKind::ReadModifyWrite),
        ("__atomic_fetch_sub", CppAccessKind::ReadModifyWrite),
        ("atomic_store", CppAccessKind::Write),
        ("atomic_fetch_add", CppAccessKind::ReadModifyWrite),
        ("atomic_fetch_sub", CppAccessKind::ReadModifyWrite),
        ("atomic_inc", CppAccessKind::ReadModifyWrite),
        ("atomic_dec", CppAccessKind::ReadModifyWrite),
        ("atomic_dec_if_positive", CppAccessKind::ReadModifyWrite),
        ("atomic_set", CppAccessKind::Write),
        ("pthread_mutex_init", CppAccessKind::Write),
        ("pthread_mutex_destroy", CppAccessKind::Write),
        ("pthread_mutex_lock", CppAccessKind::ReadModifyWrite),
        ("pthread_mutex_unlock", CppAccessKind::ReadModifyWrite),
    ] {
        for arguments in call_argument_lists(line, call) {
            let Some(target) = arguments.first() else {
                continue;
            };
            for (symbol, expression) in indexed_accesses(target) {
                mutations.push((symbol, expression, kind.clone()));
            }
        }
    }
    mutations
}

fn indexed_accesses(text: &str) -> Vec<(String, String)> {
    let bytes = text.as_bytes();
    let mut accesses = Vec::new();
    let mut open = 0usize;
    while open < bytes.len() {
        let Some(relative) = text[open..].find('[') else {
            break;
        };
        open += relative;
        let mut depth = 1usize;
        let mut close = open + 1;
        while close < bytes.len() && depth > 0 {
            match bytes[close] {
                b'[' => depth += 1,
                b']' => depth -= 1,
                _ => {}
            }
            close += 1;
        }
        if depth != 0 {
            break;
        }
        let close_bracket = close - 1;
        if let Some(symbol) = indexed_receiver_before(text, open) {
            accesses.push((
                symbol.to_string(),
                text[open + 1..close_bracket].trim().to_string(),
            ));
        }
        open = close;
    }
    accesses
}

fn indexed_receiver_before(text: &str, open: usize) -> Option<&str> {
    // `table.at(constant)[worker]` indexes the returned object/pointer, not
    // worker-selected slots in table. Crossing a call requires a typed return
    // projection; the spelling "at" supplies neither identity nor contiguity.
    identifier_before(text, open)
}

fn function_indexed_mutation(line: &str) -> Option<(Option<String>, Option<&str>, CppAccessKind)> {
    for (open, _) in line.match_indices('(') {
        let Some(symbol) = identifier_before(line, open) else {
            continue;
        };
        let lower_symbol = symbol.to_ascii_lowercase();
        if !(symbol.ends_with('_')
            && ["lock", "state", "info", "counter", "slot"]
                .iter()
                .any(|token| lower_symbol.contains(token)))
        {
            continue;
        }
        let close = line[open + 1..].find(')')? + open + 1;
        let expression = line[open + 1..close].trim();
        let symbol_start = line[..open].rfind(symbol).unwrap_or(open);
        if let Some(kind) = mutation_kind_around(&line[..symbol_start], &line[close + 1..]) {
            return Some((Some(symbol.to_string()), Some(expression), kind));
        }
    }
    None
}

fn mutation_kind_around(prefix: &str, suffix: &str) -> Option<CppAccessKind> {
    let mut prefix = prefix.trim_end();
    let mut suffix = suffix.trim_start();
    // Parentheses around the complete lvalue preserve its storage identity.
    // Do not cross a call, cast, dereference or comma expression boundary.
    while let (Some(before), Some(after)) = (prefix.strip_suffix('('), suffix.strip_prefix(')')) {
        let before = before.trim_end();
        if before
            .chars()
            .next_back()
            .is_some_and(|c| c.is_alphanumeric() || matches!(c, '_' | ')' | ']'))
        {
            break;
        }
        prefix = before;
        suffix = after.trim_start();
    }
    // Follow only the actual lvalue's member/subscript chain. Scanning the
    // entire suffix invents writes from unrelated RHS arguments/statements.
    loop {
        if suffix.starts_with('[') {
            let mut depth = 0usize;
            let close = suffix.char_indices().find_map(|(offset, ch)| {
                match ch {
                    '[' => depth += 1,
                    ']' => depth -= 1,
                    _ => {}
                }
                (depth == 0).then_some(offset)
            })?;
            suffix = suffix[close + 1..].trim_start();
        } else if suffix.starts_with("->") {
            return None;
        } else if suffix.starts_with('.') {
            let member = suffix.trim_start_matches('.').trim_start();
            let length = member
                .bytes()
                .take_while(|byte| is_ident_continue(*byte))
                .count();
            if length == 0 {
                return None;
            }
            let tail = member[length..].trim_start();
            if tail.starts_with('(') {
                if &member[..length] == "at" {
                    let mut depth = 0usize;
                    let close = tail.char_indices().find_map(|(offset, ch)| {
                        match ch {
                            '(' => depth += 1,
                            ')' => depth -= 1,
                            _ => {}
                        }
                        (depth == 0).then_some(offset)
                    })?;
                    suffix = tail[close + 1..].trim_start();
                    continue;
                }
                // A method call must itself be a known mutator; never scan
                // through an unknown/read-only call into its arguments.
                break;
            }
            suffix = tail;
        } else {
            break;
        }
    }
    if prefix.ends_with("++")
        || prefix.ends_with("--")
        || suffix.starts_with("++")
        || suffix.starts_with("--")
        || ["+=", "-=", "*=", "/=", "%=", "|=", "&=", "^="]
            .iter()
            .any(|operator| suffix.starts_with(operator))
        || [
            ".fetch_",
            ".exchange(",
            ".compare_exchange",
            ".test_and_set(",
            ".lock(",
            ".unlock(",
            ".try_lock(",
            ".tryLock(",
            ".lockShared(",
            ".unlockShared(",
            ".tryLockShared(",
            // Existing container/accumulator effect models consume old state,
            // unlike blind store/clear. Preserve that distinction downstream.
            ".merge(",
            ".push_",
            ".emplace",
            ".insert(",
            ".erase(",
            ".increment(",
            ".add(",
        ]
        .iter()
        .any(|method| suffix.starts_with(method))
    {
        return Some(CppAccessKind::ReadModifyWrite);
    }
    if suffix.starts_with(".store(")
        || [".clear(", ".update("]
            .iter()
            .any(|method| suffix.starts_with(method))
    {
        return Some(CppAccessKind::Write);
    }
    if suffix.starts_with('=') && !suffix.starts_with("==") {
        Some(CppAccessKind::Write)
    } else {
        None
    }
}

fn indexed_symbol(line: &str) -> Option<String> {
    let open = line.find('[')?;
    identifier_before(line, open).map(ToOwned::to_owned)
}

fn identifier_before(text: &str, offset: usize) -> Option<&str> {
    let bytes = text.as_bytes();
    let mut end = offset;
    while end > 0 && bytes[end - 1].is_ascii_whitespace() {
        end -= 1;
    }
    let mut start = end;
    while start > 0 && is_ident_continue(bytes[start - 1]) {
        start -= 1;
    }
    (start < end).then(|| &text[start..end])
}

fn is_thread_index_expression(expression: &str) -> bool {
    if expression.contains(['\"', '\'']) {
        return false;
    }
    identifier_tokens(expression).any(|token| match token {
        "rte_lcore_id" | "pthread_self" | "sched_getcpu" => {
            identity_occurrence_is_transparent(expression, token, true)
        }
        token if token.ends_with("get_thread_num") || token.ends_with("get_smp_processor_id") => {
            identity_occurrence_is_transparent(expression, token, true)
        }
        _ => false,
    })
}

/// Recognize a bounded worker-slot expression in a POSIX callback.  Member
/// projections of the callback argument and the repository-independent worker
/// identifier vocabulary are accepted; an ordinary loop induction variable
/// such as `i` or `index` is not.
fn looks_like_worker_slot_expression(expression: &str) -> bool {
    expression.contains("->")
        || expression.contains('.')
        || identifier_tokens(expression).any(is_worker_identifier)
}

fn identity_occurrence_is_transparent(expression: &str, token: &str, require_call: bool) -> bool {
    expression.match_indices(token).any(|(offset, _)| {
        let token_end = offset + token.len();
        let bytes = expression.as_bytes();
        if offset
            .checked_sub(1)
            .and_then(|index| bytes.get(index))
            .is_some_and(|byte| is_ident_continue(*byte))
            || bytes
                .get(token_end)
                .is_some_and(|byte| is_ident_continue(*byte))
        {
            return false;
        }
        if require_call && !expression[token_end..].trim_start().starts_with('(') {
            return false;
        }

        let mut open_parentheses = Vec::new();
        for (index, byte) in bytes[..offset].iter().enumerate() {
            match byte {
                b'(' => open_parentheses.push(index),
                b')' => {
                    open_parentheses.pop();
                }
                _ => {}
            }
        }
        !open_parentheses
            .into_iter()
            .any(|open| identifier_before(expression, open).is_some())
    })
}

/// Reject declaration syntax without making assumptions about an unknown
/// typedef. Expressions (member access, assignments, calls, control flow) have
/// punctuation that a type/qualifier prefix cannot contain.
fn indexed_target_is_declaration(prefix: &str) -> bool {
    let prefix = prefix
        .rsplit([';', '{', '}'])
        .next()
        .unwrap_or(prefix)
        .trim();
    if prefix.is_empty() || prefix.contains(['=', '.', '+', '-', '/', '!', '?', '(', ')', '[', ']'])
    {
        return false;
    }
    let tokens: Vec<_> = identifier_tokens(prefix).collect();
    !tokens.is_empty()
        && !tokens
            .iter()
            .any(|token| matches!(*token, "return" | "co_return" | "throw" | "delete"))
}

fn array_declaration_sites(file: &ParsedCppFile) -> HashSet<(usize, String)> {
    let mut declarations = HashSet::new();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() == "array_declarator"
                && let Some(name) = declarator_variable_name(node, &file.source)
            {
                declarations.insert((node.start_position().row + 1, name));
            }
        });
    }
    declarations
}

fn index_method_name(mut node: tree_sitter::Node<'_>, source: &str) -> Option<String> {
    while node.kind() != "function_declarator" {
        node = node.child_by_field_name("declarator")?;
    }
    let name = node.child_by_field_name("declarator")?;
    if !matches!(
        name.kind(),
        "identifier" | "field_identifier" | "qualified_identifier"
    ) {
        return None;
    }
    Some(node_text(name, source).rsplit("::").next()?.to_owned())
}

fn declared_private_index_methods(
    files: &[ParsedCppFile],
    records: &[CppStructInfo],
) -> HashSet<(usize, String)> {
    let inherited_interfaces = index_method_interfaces(files);
    let callback_owners = escaping_this_callback_owners(files, records);
    let mut accessibility: HashMap<(usize, String), bool> = HashMap::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(node.kind(), "class_specifier" | "struct_specifier") {
                return;
            }
            let Some(name) = node.child_by_field_name("name") else {
                return;
            };
            let Some(owner) = records.iter().position(|record| {
                record.file == file.path
                    && record.line == node.start_position().row + 1
                    && record.name == node_text(name, &file.source)
            }) else {
                return;
            };
            let Some(body) = node.child_by_field_name("body") else {
                return;
            };
            let mut private = node.kind() == "class_specifier";
            for member in body.named_children(&mut body.walk()) {
                if member.kind() == "access_specifier" {
                    private = node_text(member, &file.source).trim() == "private";
                } else if member.has_error() || member.kind() == "ERROR" {
                    // Recovery can obscure a declaration or access boundary.
                    // Do not infer privacy again until an explicit marker.
                    let bounded_method_declaration = member.kind() == "field_declaration"
                        && index_method_name(member, &file.source).is_some()
                        && node_text(member, &file.source).trim_end().ends_with(';')
                        && !identifier_tokens(node_text(member, &file.source))
                            .any(|word| matches!(word, "public" | "private" | "protected"));
                    if let Some(name) = index_method_name(member, &file.source) {
                        let member_private = bounded_method_declaration
                            && private
                            && !callback_owners.contains(&owner)
                            && index_bases_exclude_method(
                                node,
                                &file.source,
                                &name,
                                &inherited_interfaces,
                            )
                            && !identifier_tokens(node_text(member, &file.source))
                                .any(|word| matches!(word, "virtual" | "override" | "final"));
                        accessibility
                            .entry((owner, name))
                            .and_modify(|all| *all &= member_private)
                            .or_insert(member_private);
                    }
                    // An unexpanded declaration annotation may damage its
                    // type/declarator without changing the following access
                    // section. Use the visible declaration boundary, while
                    // keeping unknown base dispatch and callbacks conservative.
                    if !bounded_method_declaration {
                        private = false;
                    }
                } else if let Some(name) = index_method_name(member, &file.source) {
                    let private = private
                        && !callback_owners.contains(&owner)
                        && index_bases_exclude_method(
                            node,
                            &file.source,
                            &name,
                            &inherited_interfaces,
                        )
                        && !identifier_tokens(node_text(member, &file.source))
                            .any(|word| matches!(word, "virtual" | "override" | "final"));
                    // A public/protected overload keeps the spelling unresolved.
                    accessibility
                        .entry((owner, name))
                        .and_modify(|all| *all &= private)
                        .or_insert(private);
                }
            }
        });
    }
    accessibility
        .into_iter()
        .filter_map(|(key, private)| private.then_some(key))
        .collect()
}

fn escaping_this_callback_owners(
    files: &[ParsedCppFile],
    records: &[CppStructInfo],
) -> HashSet<usize> {
    let index = EvidenceIndex::new(records);
    let callback_contracts = synchronous_callbacks::collect(files);
    let mut owners = HashSet::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        let concurrent = concurrent_context_lines(file);
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "lambda_expression" {
                return;
            }
            let Some(captures) = node
                .named_children(&mut node.walk())
                .find(|child| child.kind() == "lambda_capture_specifier")
            else {
                return;
            };
            let text = node_text(captures, &file.source);
            let first = text
                .trim_start_matches('[')
                .split(',')
                .next()
                .unwrap_or("")
                .trim()
                .trim_end_matches(']');
            if !identifier_tokens(text).any(|word| word == "this") && !matches!(first, "&" | "=") {
                return;
            }
            let mut target = node;
            while let Some(parent) = target.parent() {
                if parent.kind() != "parenthesized_expression" {
                    break;
                }
                target = parent;
            }
            let may_suspend = identifier_tokens(node_text(node, &file.source))
                .any(|word| matches!(word, "co_await" | "co_yield" | "co_return"));
            // Only captures that cannot invoke a user copy constructor or an
            // initializer can inherit the inline call's non-escape proof.
            let inert_captures = text
                .trim_start_matches('[')
                .trim_end_matches(']')
                .split(',')
                .all(|capture| {
                    let capture = capture.trim();
                    matches!(capture, "this" | "&")
                        || capture.strip_prefix('&').is_some_and(|name| {
                            let name = name.trim();
                            !name.is_empty()
                                && identifier_tokens(name).collect::<Vec<_>>() == [name]
                        })
                });
            if !may_suspend
                && (target.parent().is_some_and(|call| {
                    call.kind() == "call_expression"
                        && call.child_by_field_name("function") == Some(target)
                }) || callback_contracts
                    // An inline lambda is its own closure type, just like an
                    // auto-bound local lambda. Reuse the selected callee's
                    // contract; an arbitrary callback conversion is not proof.
                    .call_consuming(target, file, true)
                    .is_some_and(|call| {
                        inert_captures && !concurrent.contains(&(call.start_position().row + 1))
                    })
                    || local_receiver_callback_is_direct_only(
                        node,
                        file,
                        &concurrent,
                        &callback_contracts,
                    ))
            {
                return;
            }
            // A stored/passed callback may expose private member call paths.
            // This withdraws a negative proof; it does not assert parallelism.
            let mut ancestor = node.parent();
            while let Some(parent) = ancestor {
                if parent.kind() == "function_definition" {
                    if let Some(owner) = field_access::function_owner(parent, file, &index) {
                        owners.insert(owner);
                    }
                    break;
                }
                ancestor = parent.parent();
            }
        });
    }
    owners
}

/// Prove the closure value does not outlive this invocation. This is separate
/// from index-parameter inference: an ordinary callback argument neither
/// proves nor disproves that the closure itself was published.
fn local_receiver_callback_is_direct_only(
    lambda: tree_sitter::Node<'_>,
    file: &ParsedCppFile,
    concurrent: &HashSet<usize>,
    contracts: &synchronous_callbacks::Contracts,
) -> bool {
    let Some(binding) = lambda.parent().filter(|n| {
        n.kind() == "init_declarator" && n.child_by_field_name("value") == Some(lambda)
    }) else {
        return false;
    };
    let Some(name) = binding
        .child_by_field_name("declarator")
        .filter(|n| n.kind() == "identifier")
    else {
        return false;
    };
    let Some(statement) = binding.parent().filter(|n| n.kind() == "declaration") else {
        return false;
    };
    let Some(scope) = statement
        .parent()
        .filter(|n| n.kind() == "compound_statement" && !n.has_error())
    else {
        return false;
    };
    if identifier_tokens(node_text(statement, &file.source))
        .any(|token| matches!(token, "static" | "thread_local" | "extern"))
    {
        return false;
    }
    let mut safe = true;
    let mut calls = 0;
    walk_nodes(scope, &mut |use_node| {
        if !safe
            || use_node.kind() != "identifier"
            || node_text(use_node, &file.source) != node_text(name, &file.source)
            || use_node == name
        {
            return;
        }
        // All references must use this exact local declaration. Reject a
        // redeclaration, rebinding, copy, capture, address or unknown argument.
        if use_node.start_byte() < binding.end_byte() {
            safe = false;
            return;
        }
        let call = use_node
            .parent()
            .filter(|n| {
                n.kind() == "call_expression" && n.child_by_field_name("function") == Some(use_node)
            })
            .or_else(|| direct_static_callback_wrapper_call(use_node, file, concurrent))
            .or_else(|| {
                contracts.call_consuming(
                    use_node,
                    file,
                    statement
                        .child_by_field_name("type")
                        .is_some_and(|ty| node_text(ty, &file.source).trim() == "auto"),
                )
            });
        let Some(call) = call else {
            safe = false;
            return;
        };
        let mut ancestor = call.parent();
        while let Some(node) = ancestor {
            if node == scope {
                break;
            }
            if matches!(
                node.kind(),
                "lambda_expression"
                    | "function_definition"
                    | "class_specifier"
                    | "struct_specifier"
            ) {
                safe = false;
                return;
            }
            ancestor = node.parent();
        }
        if concurrent.contains(&(call.start_position().row + 1)) {
            safe = false;
            return;
        }
        calls += 1;
    });
    safe && calls > 0
}

/// Bounded positional summaries for same-file, file-scope static functions.
/// Forwarding and wrapper lambdas must terminate in proven direct invocation;
/// unknown overloads, member dispatch and cycles do not supply a proof.
fn direct_static_callback_wrapper_call<'a>(
    argument: tree_sitter::Node<'a>,
    file: &'a ParsedCppFile,
    concurrent: &HashSet<usize>,
) -> Option<tree_sitter::Node<'a>> {
    static_callback_wrapper_call_at_depth(argument, file, concurrent, 0)
}

fn static_callback_wrapper_call_at_depth<'a>(
    argument: tree_sitter::Node<'a>,
    file: &'a ParsedCppFile,
    concurrent: &HashSet<usize>,
    depth: usize,
) -> Option<tree_sitter::Node<'a>> {
    if depth >= 4 {
        return None;
    }
    let arguments = argument.parent().filter(|n| n.kind() == "argument_list")?;
    let call = arguments
        .parent()
        .filter(|n| n.kind() == "call_expression")?;
    let function = call.child_by_field_name("function")?;
    let (callee, explicit_types) = if function.kind() == "template_function" {
        (
            function.child_by_field_name("name")?,
            function
                .child_by_field_name("arguments")?
                .named_child_count(),
        )
    } else {
        (function, 0)
    };
    if callee.kind() != "identifier" {
        return None;
    }
    let name = node_text(callee, &file.source);
    let caller_namespace = callback_lexical_namespace(call, &file.source)?;
    let mut caller_scope = call.parent();
    while let Some(scope) = caller_scope {
        if (matches!(scope.kind(), "class_specifier" | "struct_specifier")
            && scope
                .named_children(&mut scope.walk())
                .any(|n| n.kind() == "base_class_clause"))
            || (scope.kind() == "function_definition"
                && scope
                    .child_by_field_name("declarator")
                    .and_then(|n| n.child_by_field_name("declarator"))
                    .is_some_and(|n| n.kind() == "qualified_identifier"))
        {
            return None;
        }
        caller_scope = scope.parent();
    }
    let position = arguments
        .named_children(&mut arguments.walk())
        .position(|n| n == argument)?;
    let tree = file.tree.as_ref()?;
    let mut declarations = Vec::new();
    let mut shadowed = false;
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "function_declarator" {
            if node.child_by_field_name("declarator").is_some_and(|n| {
                node_text(n, &file.source) == name
                    || n.child_by_field_name("name")
                        .is_some_and(|n| node_text(n, &file.source) == name)
            }) && callback_lexical_namespace(node, &file.source).as_ref()
                == Some(&caller_namespace)
            {
                declarations.push(node);
            }
        } else if matches!(
            node.kind(),
            "init_declarator" | "parameter_declaration" | "declaration" | "field_declaration"
        ) && node
            .child_by_field_name("declarator")
            .and_then(|n| declarator_variable_name(n, &file.source))
            .as_deref()
            == Some(name)
        {
            shadowed = true;
        }
    });
    let [declarator] = declarations.as_slice() else {
        return None;
    };
    if shadowed {
        return None;
    }
    let definition = declarator
        .parent()
        .filter(|n| n.kind() == "function_definition")?;
    // Require matching lexical namespace, without namespace aliases or
    // implicit member lookup. Anonymous namespaces remain unresolved here.
    let mut outer = definition.parent()?;
    if outer.kind() == "template_declaration" {
        outer = outer.parent()?;
    }
    if outer.kind() != "translation_unit"
        && !(outer.kind() == "declaration_list"
            && outer
                .parent()
                .is_some_and(|n| n.kind() == "namespace_definition"))
    {
        return None;
    }
    let body = definition
        .child_by_field_name("body")
        .filter(|n| !n.has_error())?;
    let signature = &file.source[definition.start_byte()..body.start_byte()];
    if !identifier_tokens(signature).any(|n| n == "static") {
        return None;
    }
    let params = declarator.child_by_field_name("parameters")?;
    if params.named_child_count() != arguments.named_child_count() {
        return None;
    }
    if !synchronous_callbacks::preserves_callback_target(
        params.named_child(u32::try_from(position).ok()?)?,
        definition,
        file,
    ) {
        return None;
    }
    if explicit_types > 0 {
        let parameter = params.named_child(u32::try_from(position).ok()?)?;
        let ty = node_text(parameter.child_by_field_name("type")?, &file.source);
        if field_access::without_template_arguments(ty).trim() != "std::function" {
            let template_parameters = definition.parent()?.child_by_field_name("parameters")?;
            let deduced_position = template_parameters
                .named_children(&mut template_parameters.walk())
                .position(|n| {
                    n.kind() == "type_parameter_declaration"
                        && identifier_tokens(node_text(n, &file.source)).last() == Some(ty)
                })?;
            // An explicitly selected callback type may convert/publish the
            // lambda. Only deduction preserves the actual closure type.
            if deduced_position < explicit_types {
                return None;
            }
        }
    }
    let parameter = params
        .named_child(u32::try_from(position).ok()?)?
        .child_by_field_name("declarator")?;
    let parameter = declarator_variable_name(parameter, &file.source)?;
    let mut safe = true;
    let mut calls = 0;
    walk_nodes(body, &mut |node| {
        if !safe || node.kind() != "identifier" || node_text(node, &file.source) != parameter {
            return;
        }
        let invocation = node
            .parent()
            .filter(|n| {
                n.kind() == "call_expression" && n.child_by_field_name("function") == Some(node)
            })
            .or_else(|| static_callback_wrapper_call_at_depth(node, file, concurrent, depth + 1));
        let Some(invocation) = invocation else {
            safe = false;
            return;
        };
        let mut ancestor = invocation.parent();
        while let Some(scope) = ancestor {
            if scope == body {
                break;
            }
            if scope.kind() == "lambda_expression" {
                // A nested closure is synchronous only if its own value is
                // consumed by a separately proven callback parameter.
                if static_callback_wrapper_call_at_depth(scope, file, concurrent, depth + 1)
                    .is_none()
                {
                    safe = false;
                    return;
                }
            } else if scope.kind() == "function_definition" {
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
    if identifier_tokens(node_text(body, &file.source))
        .any(|n| matches!(n, "co_await" | "co_yield" | "co_return"))
    {
        safe = false;
    }
    (safe && calls > 0).then_some(call)
}

fn callback_lexical_namespace(node: tree_sitter::Node<'_>, source: &str) -> Option<String> {
    let mut scopes = Vec::new();
    let mut ancestor = node.parent();
    while let Some(scope) = ancestor {
        if scope.kind() == "namespace_definition" {
            scopes.push(node_text(scope.child_by_field_name("name")?, source));
        }
        ancestor = scope.parent();
    }
    scopes.reverse();
    Some(scopes.join("::"))
}

struct IndexMethodInterface {
    methods: HashSet<String>,
    bases: Option<Vec<String>>,
}

fn index_base_names(node: tree_sitter::Node<'_>, source: &str) -> Option<Vec<String>> {
    let Some(clause) = node.child_by_field_name("base_class_clause").or_else(|| {
        node.named_children(&mut node.walk())
            .find(|child| child.kind() == "base_class_clause")
    }) else {
        return Some(Vec::new());
    };
    let mut bases = Vec::new();
    for child in clause.named_children(&mut clause.walk()) {
        match child.kind() {
            "access_specifier" => {}
            "type_identifier" => bases.push(node_text(child, source).to_owned()),
            // Qualified/template/dependent bases need actual type resolution.
            _ => return None,
        }
    }
    (!bases.is_empty()).then_some(bases)
}

fn index_method_interfaces(files: &[ParsedCppFile]) -> HashMap<String, Vec<IndexMethodInterface>> {
    let mut result: HashMap<String, Vec<IndexMethodInterface>> = HashMap::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(node.kind(), "class_specifier" | "struct_specifier") {
                return;
            }
            let (Some(name), Some(body)) = (
                node.child_by_field_name("name"),
                node.child_by_field_name("body"),
            ) else {
                return;
            };
            let methods = body
                .named_children(&mut body.walk())
                .filter(|member| {
                    // A nonvirtual base member with the same spelling does
                    // not dispatch to a derived private helper. Implicit
                    // overrides remain covered by walking all ancestor bases.
                    let end = member
                        .child_by_field_name("body")
                        .map_or(member.end_byte(), |body| body.start_byte());
                    identifier_tokens(&file.source[member.start_byte()..end])
                        .any(|word| matches!(word, "virtual" | "override" | "final"))
                })
                .filter_map(|member| index_method_name(member, &file.source))
                .collect();
            // A recovered expression inside a method body cannot introduce
            // another virtual member or alter inheritance. Keep declaration
            // errors conservative without invalidating the whole interface
            // for an unrelated implementation-body parse error.
            let incomplete_interface = body.named_children(&mut body.walk()).any(|member| {
                if member.kind() == "function_definition" {
                    member
                        .named_children(&mut member.walk())
                        .any(|part| part.kind() != "compound_statement" && part.has_error())
                } else {
                    member.has_error() || member.kind() == "ERROR"
                }
            });
            let bases = if incomplete_interface {
                None
            } else {
                index_base_names(node, &file.source)
            };
            result
                .entry(node_text(name, &file.source).to_owned())
                .or_default()
                .push(IndexMethodInterface { methods, bases });
        });
    }
    result
}

fn index_bases_exclude_method(
    node: tree_sitter::Node<'_>,
    source: &str,
    method: &str,
    interfaces: &HashMap<String, Vec<IndexMethodInterface>>,
) -> bool {
    let Some(mut pending) = index_base_names(node, source) else {
        return false;
    };
    let mut visited = HashSet::new();
    while let Some(base) = pending.pop() {
        if !visited.insert(base.clone()) {
            continue;
        }
        let Some(definitions) = interfaces.get(&base) else {
            return false;
        };
        let [definition] = definitions.as_slice() else {
            return false;
        };
        if definition.methods.contains(method) {
            return false;
        }
        let Some(bases) = &definition.bases else {
            return false;
        };
        pending.extend(bases.iter().cloned());
    }
    true
}

fn remove_private_api_partition_seeds(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    private: &HashSet<(usize, String)>,
    origins: &mut IndexPartitionOrigins,
) {
    let Some(tree) = &file.tree else { return };
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "function_definition" {
            return;
        }
        let (Some(owner), Some(name), Some(body)) = (
            field_access::function_owner(node, file, index),
            index_method_name(node, &file.source),
            node.child_by_field_name("body"),
        ) else {
            return;
        };
        if private.contains(&(owner, name)) {
            for (start, end, parameters) in &mut origins.regions {
                if *start == body.start_position().row + 1 && *end == body.end_position().row + 1 {
                    parameters.clear();
                }
            }
        }
    });
}

#[derive(Clone)]
struct IndexPartitionOrigins {
    /// Each map is bounded to a callable's body. Parameter names in unrelated
    /// functions must never establish an index's provenance.
    regions: Vec<(usize, usize, HashSet<String>)>,
    assignments: Vec<(usize, String, String)>,
    thread_local_ids: HashSet<String>,
    api_thread_local_ids: HashSet<String>,
    parallel_inductions: Vec<(usize, usize, String)>,
    value_expressions: HashMap<(usize, String), String>,
    runtime_values: HashMap<(usize, String), bool>,
    runtime_parameters: HashSet<(usize, usize, String)>,
}

impl IndexPartitionOrigins {
    fn supports(&self, expression: &str, line: usize) -> bool {
        self.supports_origin(expression, line, true, false)
    }

    fn supports_runtime_identity(&self, expression: &str, line: usize) -> bool {
        self.supports_origin(expression, line, false, false)
    }

    fn supports_parallel_argument(&self, expression: &str, line: usize) -> bool {
        self.supports_origin(expression, line, true, true)
    }

    fn supports_origin(
        &self,
        expression: &str,
        line: usize,
        include_api: bool,
        include_parallel: bool,
    ) -> bool {
        // A direct runtime identity call is conclusive.  Do this before alias
        // substitution: recovery-mode assignment collection can otherwise
        // create a same-text entry for a call expression and accidentally
        // replace the intrinsic with an unrelated RHS fragment.
        if is_thread_index_expression(expression)
            || self
                .runtime_values
                .get(&(line, expression.trim().to_owned()))
                == Some(&true)
        {
            return true;
        }
        let expression = self
            .value_expressions
            .get(&(line, expression.trim().to_string()))
            .map(String::as_str)
            .unwrap_or(expression);
        if expression.contains(['\"', '\'']) {
            return false;
        }
        if is_thread_index_expression(expression) {
            return true;
        }
        let mut origins = self.thread_local_ids.clone();
        if include_api {
            origins.extend(self.api_thread_local_ids.iter().cloned());
        }
        let inductions = self
            .parallel_inductions
            .iter()
            .filter(|(start, end, _)| include_parallel && *start <= line && line <= *end)
            .collect::<Vec<_>>();
        let region = self
            .regions
            .iter()
            .filter(|(start, end, _)| *start <= line && line <= *end)
            .min_by_key(|(start, end, _)| end - start);
        let start_line = region.map_or(line, |(start, _, parameters)| {
            if include_api {
                origins.extend(parameters.iter().cloned());
            }
            *start
        });
        if let Some((start, end, _)) = region {
            origins.extend(
                self.runtime_parameters
                    .iter()
                    .filter(|(b, e, _)| b == start && e == end)
                    .map(|(_, _, name)| name.clone()),
            );
        }
        let first = self
            .assignments
            .partition_point(|(assignment_line, _, _)| *assignment_line < start_line);
        for (assignment_line, lhs, rhs) in self.assignments[first..]
            .iter()
            .take_while(|(assignment_line, _, _)| *assignment_line < line)
        {
            for (start, _, name) in &inductions {
                if *start <= *assignment_line {
                    origins.insert(name.clone());
                }
            }
            if inductions
                .iter()
                .any(|(start, _, name)| *start == *assignment_line && name == lhs)
            {
                continue; // The canonical loop initializer is not a serial rebind.
            }
            let typed_runtime = self
                .runtime_values
                .get(&(*assignment_line, rhs.trim().to_owned()))
                == Some(&true);
            let rhs = self
                .value_expressions
                .get(&(*assignment_line, rhs.trim().to_string()))
                .map(String::as_str)
                .unwrap_or(rhs);
            let runtime_identity = typed_runtime || is_thread_index_expression(rhs);
            let derived = origins
                .iter()
                .any(|origin| contains_identifier(rhs, origin));
            // A tuple/column/bucket index is not a worker identity. In
            // particular, the fallback token scanner also returns bare names;
            // those must not turn every *_index assignment into runtime MHP.
            let descriptor_partition = include_api
                && field_access_tokens(rhs)
                    .into_iter()
                    .any(|(receiver, field)| {
                        receiver.is_some()
                            && matches!(
                                field,
                                "thread"
                                    | "thread_id"
                                    | "worker"
                                    | "worker_id"
                                    | "cpu_id"
                                    | "lcore_id"
                            )
                    });
            let nonlinear_remap = rhs
                .find('(')
                .and_then(|open| identifier_before(rhs, open))
                .is_some_and(|callee| {
                    let callee = callee.to_ascii_lowercase();
                    callee.starts_with("map")
                        || callee.contains("hash")
                        || callee.contains("reverse")
                        || callee.contains("permute")
                        || callee.contains("shuffle")
                });
            // Dispatching a hash into a declared thread/worker count is a
            // partition route, unlike a hash bucket count or ordinary slot.
            let dispatch_partition = include_api
                && rhs.contains('%')
                && identifier_tokens(rhs).any(|token| {
                    let lower = token.to_ascii_lowercase();
                    lower.ends_with("threads") || lower.ends_with("workers")
                });
            if nonlinear_remap {
                origins.remove(lhs);
            } else if runtime_identity || derived || descriptor_partition || dispatch_partition {
                origins.insert(lhs.clone());
            } else {
                // Assignment to a constant or sequential loop induction kills
                // the incoming parameter's role for this subsequent use.
                origins.remove(lhs);
            }
        }
        for (_, _, name) in inductions {
            origins.insert(name.clone());
        }
        origins
            .iter()
            .any(|origin| contains_identifier(expression, origin))
    }
}

fn bpf_array_map_symbols(file: &ParsedCppFile) -> HashSet<String> {
    let mut maps = HashSet::new();
    let mut block = String::new();
    let mut in_record = false;
    for raw_line in file.source.lines() {
        let line = raw_line.trim();
        if line.starts_with("struct {") {
            block.clear();
            in_record = true;
        }
        if !in_record {
            continue;
        }
        block.push_str(line);
        block.push(' ');
        if line.starts_with('}') && line.contains("SEC(") {
            if block.contains("BPF_MAP_TYPE_ARRAY")
                && let Some(name) = identifier_tokens(line).next()
            {
                maps.insert(name.to_string());
            }
            block.clear();
            in_record = false;
        }
    }
    maps
}

// This is a conditional API role, not a runtime concurrency witness. Generic
// index spelling carries no worker identity; actual argument provenance and
// parallel contexts are collected independently of the formal name.
fn explicit_partition_parameter(name: &str) -> bool {
    let normalized = name.trim_matches('_').to_ascii_lowercase();
    // Quantity words do not identify an independently executing participant.
    // This only removes the naming heuristic; real argument/runtime evidence
    // can still establish an identity for a variable with any spelling.
    if ["size", "count", "length", "stride", "capacity", "bytes"]
        .iter()
        .any(|quantity| normalized.split('_').any(|part| part == *quantity))
    {
        return false;
    }
    // Data coordinates (slots, cells, blocks, scenarios, state indices) do
    // not identify executing participants. Their caller/runtime provenance
    // must establish a partition; spelling alone must not do so.
    matches!(
        normalized.as_str(),
        "thread" | "worker" | "tid" | "cpu" | "lcore" | "num_thread"
    ) || ["thread_", "worker_", "cpu_", "lcore_"]
        .iter()
        .any(|prefix| normalized.starts_with(prefix))
}

// A named object/array pointer is storage, not an integer partition input.
// Its explicitly identified thread member is handled separately below.
fn partition_value_declarator(
    declaration: tree_sitter::Node<'_>,
    mut shape: tree_sitter::Node<'_>,
) -> bool {
    loop {
        match shape.kind() {
            "identifier" | "field_identifier" => return true,
            "parenthesized_declarator" => {}
            "reference_declarator"
                if declaration.child_by_field_name("type").is_some_and(|ty| {
                    matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                }) => {}
            _ => return false,
        }
        let Some(inner) = shape
            .child_by_field_name("declarator")
            .or_else(|| shape.named_child(0))
        else {
            return false;
        };
        shape = inner;
    }
}

/// Only the scalar ID overloads on a lexically bound runtime descriptor.
/// Range queries and same-named methods on application objects are not IDs.
fn sycl_item_identity_call(file: &ParsedCppFile, mut call: tree_sitter::Node<'_>) -> Option<bool> {
    while call.kind() == "parenthesized_expression" {
        call = call.named_child(0)?;
    }
    if call.kind() != "call_expression" {
        return None;
    }
    let method = call
        .child_by_field_name("function")
        .filter(|n| n.kind() == "field_expression")?;
    let member = node_text(method.child_by_field_name("field")?, &file.source);
    if !matches!(
        member,
        "get_local_id" | "get_global_id" | "get_local_linear_id" | "get_global_linear_id"
    ) {
        return None;
    }
    Some(
        (|| -> Option<()> {
            if file.is_c || node_text(method, &file.source).contains("->") {
                return None;
            }
            let receiver = method
                .child_by_field_name("argument")
                .filter(|n| n.kind() == "identifier")?;
            let name = node_text(receiver, &file.source);
            let mut ancestor = call.parent();
            let callable = loop {
                let node = ancestor?;
                if matches!(node.kind(), "function_definition" | "lambda_expression") {
                    break node;
                }
                ancestor = node.parent();
            };
            let body = callable.child_by_field_name("body")?;
            let mut parameters = Vec::new();
            walk_nodes(callable, &mut |node| {
                if node.kind() == "parameter_declaration"
                    && node.end_byte() < body.start_byte()
                    && node
                        .child_by_field_name("declarator")
                        .and_then(|n| declarator_variable_name(n, &file.source))
                        .as_deref()
                        == Some(name)
                {
                    parameters.push(node);
                }
            });
            let [parameter] = parameters.as_slice() else {
                return None;
            };
            let ty = node_text(parameter.child_by_field_name("type")?, &file.source)
                .split_whitespace()
                .collect::<String>();
            let absolute = ty.starts_with("::");
            let ty = ty.trim_start_matches("::");
            let dimension = ty
                .strip_prefix("sycl::nd_item<")
                .or_else(|| ty.strip_prefix("cl::sycl::nd_item<"))?
                .strip_suffix('>')?;
            let dimension = if dimension.is_empty() {
                1
            } else {
                dimension.parse::<usize>().ok()?
            };
            if !(1..=3).contains(&dimension) {
                return None;
            }
            let mut shape = parameter.child_by_field_name("declarator")?;
            if shape.kind() == "reference_declarator" {
                shape = shape
                    .child_by_field_name("declarator")
                    .or_else(|| shape.named_child(0))?;
            }
            if shape.kind() != "identifier" {
                return None;
            }
            let mut scope = callable.parent();
            while let Some(node) = scope {
                if !absolute && node.kind() == "namespace_definition" {
                    return None;
                }
                scope = node.parent();
            }
            let arguments = call.child_by_field_name("arguments")?;
            if member.ends_with("linear_id") {
                if arguments.named_child_count() != 0 {
                    return None;
                }
            } else {
                if arguments.named_child_count() != 1 {
                    return None;
                }
                let argument = arguments.named_child(0)?;
                if argument.kind() != "number_literal"
                    || node_text(argument, &file.source).parse::<usize>().ok()? >= dimension
                {
                    return None;
                }
            }
            let mut blocked = false;
            walk_nodes(file.tree.as_ref()?.root_node(), &mut |node| {
                if matches!(
                    node.kind(),
                    "preproc_def"
                        | "preproc_function_def"
                        | "namespace_alias_definition"
                        | "class_specifier"
                        | "struct_specifier"
                ) && node.child_by_field_name("name").is_some_and(|n| {
                    [name, member, "sycl", "nd_item"].contains(&node_text(n, &file.source))
                }) {
                    blocked = true;
                }
            });
            walk_nodes(body, &mut |node| {
                if matches!(node.kind(), "declaration" | "parameter_declaration")
                    && node
                        .child_by_field_name("declarator")
                        .and_then(|n| declarator_variable_name(n, &file.source))
                        .as_deref()
                        == Some(name)
                {
                    blocked = true;
                }
                let target = match node.kind() {
                    "assignment_expression" => node.child_by_field_name("left"),
                    "pointer_expression"
                        if node_text(node, &file.source).trim_start().starts_with('&') =>
                    {
                        node.child_by_field_name("argument")
                    }
                    _ => None,
                };
                if target.is_some_and(|n| node_text(n, &file.source) == name) {
                    blocked = true;
                }
            });
            (!blocked).then_some(())
        })()
        .is_some(),
    )
}

fn collect_index_partition_origins(
    file: &ParsedCppFile,
    functions: &[FunctionRegion],
) -> IndexPartitionOrigins {
    let fields = partition_descriptors::api_fields(file);
    collect_index_partition_origins_with_descriptors(file, functions, &fields)
}

fn collect_index_partition_origins_with_descriptors(
    file: &ParsedCppFile,
    functions: &[FunctionRegion],
    descriptor_api_fields: &HashMap<String, HashSet<String>>,
) -> IndexPartitionOrigins {
    let mut origins = IndexPartitionOrigins {
        regions: Vec::new(),
        assignments: Vec::new(),
        thread_local_ids: HashSet::new(),
        api_thread_local_ids: HashSet::new(),
        parallel_inductions: Vec::new(),
        value_expressions: HashMap::new(),
        runtime_values: HashMap::new(),
        runtime_parameters: HashSet::new(),
    };
    let Some(tree) = &file.tree else {
        return origins;
    };
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "for_statement" {
            return;
        }
        let prefix = &file.source[..node.start_byte()];
        let mut lines = prefix
            .lines()
            .rev()
            .map(str::trim)
            .filter(|s| !s.is_empty());
        let mut directive = lines.next().unwrap_or("");
        if directive == "#endif" {
            directive = lines.next().unwrap_or("");
        }
        // Join only actual continued directive lines. Clauses on a following
        // line must not hide the induction variable of a real worksharing
        // loop, and an unrelated earlier pragma must not lend provenance.
        let mut joined = directive.to_owned();
        for _ in 0..8 {
            if directive.starts_with("#pragma") {
                break;
            }
            let previous = lines.next().unwrap_or("");
            let Some(head) = previous.strip_suffix('\\') else {
                break;
            };
            joined = format!("{head} {joined}");
            directive = previous;
        }
        let tokens = identifier_tokens(&joined).collect::<Vec<_>>();
        let pragma = matches!(
            tokens.as_slice(),
            ["pragma", "omp", "parallel", "for", ..] | ["pragma", "omp", "for", ..]
        );
        if !pragma {
            return;
        }
        let (Some(initializer), Some(body)) = (
            node.child_by_field_name("initializer"),
            node.child_by_field_name("body"),
        ) else {
            return;
        };
        if initializer.kind() != "declaration" {
            return;
        }
        let Some(declarator) = initializer.child_by_field_name("declarator") else {
            return;
        };
        let Some(name_node) = declarator
            .child_by_field_name("declarator")
            .filter(|n| n.kind() == "identifier")
        else {
            return;
        };
        let name = node_text(name_node, &file.source);
        let canonical_update = node.child_by_field_name("update").is_some_and(|update| {
            update.kind() == "update_expression"
                && update
                    .child_by_field_name("argument")
                    .is_some_and(|n| node_text(n, &file.source) == name)
                && update
                    .child_by_field_name("operator")
                    .is_some_and(|n| matches!(node_text(n, &file.source), "++" | "--"))
        });
        if !canonical_update {
            return;
        }
        let mut modified = false;
        walk_nodes(body, &mut |n| {
            let target = match n.kind() {
                "assignment_expression" => n.child_by_field_name("left"),
                "init_declarator" => n.child_by_field_name("declarator"),
                "update_expression" => n.child_by_field_name("argument"),
                "pointer_expression" if node_text(n, &file.source).starts_with('&') => {
                    n.child_by_field_name("argument")
                }
                _ => None,
            };
            modified |= target.is_some_and(|n| {
                let mut n = n;
                while n.kind() == "parenthesized_expression" {
                    let Some(inner) = n.named_child(0) else {
                        break;
                    };
                    n = inner;
                }
                node_text(n, &file.source) == name
            });
            if matches!(n.kind(), "declaration" | "parameter_declaration") {
                modified |= n
                    .child_by_field_name("declarator")
                    .and_then(|d| declarator_variable_name(d, &file.source))
                    .as_deref()
                    == Some(name);
            }
        });
        if !modified {
            origins.parallel_inductions.push((
                node.start_position().row + 1,
                node.end_position().row + 1,
                name.to_string(),
            ));
        }
    });
    // Passing a worker identity into an opaque function does not establish
    // that the function returns that identity. Bind complete call arguments
    // through the same value-expression rules used for indexed expressions.
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "argument_list" {
            return;
        }
        let Some(call) = node.parent().filter(|p| p.kind() == "call_expression") else {
            return;
        };
        let mut cursor = node.walk();
        for argument in node.named_children(&mut cursor) {
            origins.value_expressions.insert(
                (
                    call.start_position().row + 1,
                    node_text(argument, &file.source).trim().to_owned(),
                ),
                transparent_partition_value(argument, &file.source),
            );
        }
    });
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "call_expression" {
            let key = (
                node.start_position().row + 1,
                node_text(node, &file.source).trim().to_owned(),
            );
            if let Some(valid) = sycl_item_identity_call(file, node) {
                origins
                    .runtime_values
                    .entry(key)
                    .and_modify(|known| *known &= valid)
                    .or_insert(valid);
            }
        }
        if node.kind() == "subscript_expression"
            && let Some(expression) = node
                .child_by_field_name("indices")
                .and_then(|indices| indices.named_child(0))
        {
            origins.value_expressions.insert(
                (
                    expression.start_position().row + 1,
                    node_text(expression, &file.source).trim().to_string(),
                ),
                transparent_partition_value(expression, &file.source),
            );
        }
        if matches!(node.kind(), "function_definition" | "lambda_expression") {
            let Some(body) = node.child_by_field_name("body") else {
                return;
            };
            let mut parameters = HashSet::new();
            let parallel_callback = node.kind() == "lambda_expression"
                && node.parent().is_some_and(|arguments| {
                    arguments.kind() == "argument_list"
                        && arguments.parent().is_some_and(|call| {
                            call.kind() == "call_expression"
                                && call.child_by_field_name("function").is_some_and(|callee| {
                                    node_text(callee, &file.source)
                                        .split('<')
                                        .next()
                                        .unwrap_or("")
                                        .rsplit(['.', ':'])
                                        .next()
                                        == Some("parallel_for")
                                })
                        })
                });
            // Only parameter declarations, not identifiers merely occurring in
            // the signature or a lambda's capture list, are role inputs.
            walk_nodes(node, &mut |child| {
                if child.start_byte() >= body.start_byte()
                    || child.kind() != "parameter_declaration"
                {
                    return;
                }
                if let Some(declarator) = child.child_by_field_name("declarator")
                    && let Some(name) = declarator_variable_name(declarator, &file.source)
                {
                    let scalar_sycl_id = parallel_callback
                        && child.child_by_field_name("type").is_some_and(|ty| {
                            matches!(
                                node_text(ty, &file.source)
                                    .split_whitespace()
                                    .collect::<String>()
                                    .trim_start_matches("::"),
                                "sycl::id<1>" | "cl::sycl::id<1>"
                            )
                        });
                    if (explicit_partition_parameter(&name) || scalar_sycl_id)
                        && partition_value_declarator(child, declarator)
                    {
                        parameters.insert(name.clone());
                    }
                    // A caller-owned descriptor may carry the partition id.
                    // Require the receiver to be an actual parameter and the
                    // member to be declared in this file or named as a thread
                    // identity, not just an arbitrary substring in an index.
                    for (_, field) in field_access_tokens(node_text(body, &file.source)) {
                        if matches!(field, "thread" | "thread_id" | "worker_id")
                            || child
                                .child_by_field_name("type")
                                .filter(|ty| {
                                    matches!(ty.kind(), "type_identifier" | "template_type")
                                })
                                .and_then(|ty| {
                                    descriptor_api_fields.get(
                                        node_text(ty, &file.source).split('<').next().unwrap_or(""),
                                    )
                                })
                                .is_some_and(|fields| fields.contains(field))
                        {
                            for separator in [".", "->"] {
                                let member = format!("{name}{separator}{field}");
                                if node_text(body, &file.source).contains(&member) {
                                    parameters.insert(member);
                                }
                            }
                        }
                    }
                }
            });
            origins.regions.push((
                body.start_position().row + 1,
                body.end_position().row + 1,
                parameters,
            ));
        }
        if matches!(node.kind(), "init_declarator" | "assignment_expression") {
            let lhs = node.child_by_field_name(if node.kind() == "init_declarator" {
                "declarator"
            } else {
                "left"
            });
            let rhs = node.child_by_field_name(if node.kind() == "init_declarator" {
                "value"
            } else {
                "right"
            });
            if let (Some(lhs), Some(rhs)) = (lhs, rhs)
                && matches!(
                    lhs.kind(),
                    "identifier" | "pointer_declarator" | "reference_declarator"
                )
                && let Some(mut name) = declarator_variable_name(lhs, &file.source)
            {
                // A macro-delimited block can recover a scalar declaration
                // as `const` followed by an ERROR node and an assignment.
                // Recover only the complete built-in declaration prefix;
                // never install a keyword as an index variable or guess an
                // unknown type, pointer, reference, or decorated declaration.
                if name == "const" && node.has_error() {
                    let prefix = file.source[node.start_byte()..rhs.start_byte()]
                        .trim_end()
                        .strip_suffix('=')
                        .unwrap_or("")
                        .trim();
                    let tokens = prefix.split_whitespace().collect::<Vec<_>>();
                    let valid = tokens.len() >= 3
                        && tokens[0] == "const"
                        && tokens[1..tokens.len() - 1].iter().all(|ty| {
                            matches!(
                                *ty,
                                "int"
                                    | "unsigned"
                                    | "signed"
                                    | "long"
                                    | "short"
                                    | "size_t"
                                    | "std::size_t"
                            )
                        });
                    let recovered = tokens.last().copied().unwrap_or("");
                    if !valid || identifier_tokens(recovered).collect::<Vec<_>>() != [recovered] {
                        return;
                    }
                    name = recovered.to_owned();
                }
                let key = (
                    node.start_position().row + 1,
                    node_text(rhs, &file.source).trim().to_owned(),
                );
                if let Some(valid) = sycl_item_identity_call(file, rhs) {
                    origins
                        .runtime_values
                        .entry(key)
                        .and_modify(|known| *known &= valid)
                        .or_insert(valid);
                }
                origins.value_expressions.insert(
                    (
                        node.start_position().row + 1,
                        node_text(rhs, &file.source).trim().to_string(),
                    ),
                    transparent_partition_value(rhs, &file.source),
                );
                let operator = node
                    .child_by_field_name("operator")
                    .map(|operator| node_text(operator, &file.source));
                let value = if matches!(operator, Some("+=" | "-="))
                    && (file.is_c
                        || (primitive_local_operand(lhs, &file.source)
                            && primitive_local_operand(rhs, &file.source)))
                {
                    if operator == Some("-=") && node_text(rhs, &file.source).trim() == name {
                        "0".to_owned()
                    } else {
                        format!(
                            "{name} {} ({})",
                            if operator == Some("+=") { "+" } else { "-" },
                            transparent_partition_value(rhs, &file.source)
                        )
                    }
                } else {
                    node_text(rhs, &file.source).to_owned()
                };
                origins
                    .assignments
                    .push((node.start_position().row + 1, name, value));
            }
        }
    });
    // A TLS counter allocated with an atomic ticket has source-backed identity
    // even when registration and use live in different functions.
    for name in thread_local_symbols(file) {
        if origins.assignments.iter().any(|(_, lhs, rhs)| {
            lhs == &name && (rhs.contains("fetch_add") || rhs.contains("fetch_sub"))
        }) {
            origins.thread_local_ids.insert(name);
        }
    }
    // Legacy C definitions can be absent from an error-recovering syntax tree.
    for function in functions {
        if !origins.regions.iter().any(|(start, end, _)| {
            *start == function.body_start_line && *end == function.body_end_line
        }) {
            let parameters = function
                .declarator
                .split('(')
                .nth(1)
                .unwrap_or("")
                .split(',')
                .filter(|parameter| !parameter.contains(['*', '&', '[', ']']))
                .filter_map(|parameter| identifier_tokens(parameter).last())
                .filter(|name| explicit_partition_parameter(name))
                .map(ToOwned::to_owned)
                .collect();
            origins
                .regions
                .push((function.body_start_line, function.body_end_line, parameters));
        }
    }
    origins.assignments.sort_by_key(|(line, _, _)| *line);
    let concurrent = concurrent_context_lines(file);
    let mut local_regions = Vec::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "lambda_expression"
            && local_callback_has_only_sequential_data_calls(node, file, &origins, &concurrent)
            && let Some(body) = node.child_by_field_name("body")
        {
            local_regions.push((body.start_position().row + 1, body.end_position().row + 1));
        }
    });
    for (start, end, parameters) in &mut origins.regions {
        if local_regions.contains(&(*start, *end)) {
            parameters.clear();
        }
    }
    let internal_calls = internal_index_api::prepare(file, &mut origins);
    propagate_local_callback_partition_arguments(file, &mut origins, &concurrent);
    pthread_partitions::seed(file, &mut origins);
    if let Some(calls) = &internal_calls {
        calls.propagate(&mut origins);
    }
    propagate_direct_partition_arguments(file, &mut origins);
    partition_descriptors::propagate(file, &mut origins);
    if let Some(calls) = &internal_calls {
        calls.propagate(&mut origins);
    }
    origins
}

/// A registration API can save a caller-supplied partition in TLS for later
/// calls. This supports conditional API partitioning, never runtime MHP merely
/// because a variable is thread-local. Require a scalar source declaration and
/// a bound partition assignment; reject shadowing and escaped addresses.
fn propagate_tls_api_partitions(
    file: &ParsedCppFile,
    functions: &[FunctionRegion],
    origins: &mut IndexPartitionOrigins,
) {
    let Some(tree) = &file.tree else { return };
    let at_file_scope = |node: tree_sitter::Node<'_>| {
        let mut parent = node.parent();
        while let Some(ancestor) = parent {
            if !ancestor.kind().starts_with("preproc_") {
                return ancestor.kind() == "translation_unit";
            }
            parent = ancestor.parent();
        }
        false
    };
    let mut free_bodies = Vec::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "function_definition"
            && at_file_scope(node)
            && node
                .child_by_field_name("declarator")
                .is_some_and(|d| !node_text(d, &file.source).contains("::"))
            && let Some(body) = node.child_by_field_name("body")
        {
            free_bodies.push((body.start_position().row + 1, body.end_position().row + 1));
        }
    });
    let mut declarations = HashMap::<String, Vec<usize>>::new();
    for (idx, line) in file.source.lines().enumerate() {
        let tokens = identifier_tokens(line).collect::<Vec<_>>();
        if !tokens
            .iter()
            .any(|t| matches!(*t, "thread_local" | "__thread" | "_Thread_local"))
            || !tokens
                .iter()
                .any(|t| matches!(*t, "int" | "unsigned" | "long" | "short" | "size_t"))
            || line.contains(['*', '&', '[', ']', ','])
            || line.trim_start().starts_with('#')
            || functions
                .iter()
                .any(|f| f.body_start_line <= idx + 1 && idx < f.body_end_line)
        {
            continue;
        }
        if let Some(name) = extract_static_candidate_name(line) {
            declarations.entry(name).or_default().push(idx + 1);
        }
    }
    let mut supported = Vec::new();
    for (name, lines) in declarations {
        if lines.len() != 1
            || functions
                .iter()
                .any(|f| function_parameters(f).contains(&name))
        {
            continue;
        }
        let mut ambiguous = false;
        let mut declared = false;
        walk_nodes(tree.root_node(), &mut |node| {
            // A spelling shared with a member/local declaration is not a
            // project-wide TLS identity. Keep this file conservatively unbound.
            if matches!(
                node.kind(),
                "declaration" | "field_declaration" | "parameter_declaration"
            ) {
                for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
                    if declarator_variable_name(declarator, &file.source).as_deref()
                        == Some(name.as_str())
                    {
                        if node.kind() == "declaration"
                            && node.start_position().row + 1 == lines[0]
                            && at_file_scope(node)
                        {
                            declared = true;
                        } else {
                            ambiguous = true;
                        }
                    }
                }
            }
            if node.kind() == "pointer_expression"
                && node
                    .child_by_field_name("operator")
                    .is_some_and(|op| node_text(op, &file.source) == "&")
                && node
                    .child_by_field_name("argument")
                    .is_some_and(|arg| contains_identifier(node_text(arg, &file.source), &name))
            {
                ambiguous = true;
            }
        });
        if declared
            && !ambiguous
            && origins.assignments.iter().any(|(line, lhs, rhs)| {
                lhs == &name
                    && origins.supports(rhs, *line)
                    && free_bodies
                        .iter()
                        .any(|(start, end)| start <= line && line <= end)
            })
        {
            supported.push(name);
        }
    }
    origins.api_thread_local_ids.extend(supported);
}

/// Bind scalar partition arguments to uniquely defined file-scope functions.
/// An ordinary coordinate formal acquires a role from its caller, not its name.
fn propagate_direct_partition_arguments(file: &ParsedCppFile, origins: &mut IndexPartitionOrigins) {
    let Some(tree) = &file.tree else { return };
    let mut definitions = HashMap::new();
    let mut definition_counts = HashMap::<String, usize>::new();
    let mut declarations = HashMap::<String, HashSet<Vec<String>>>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "function_declarator"
            && let Some(name) = node.child_by_field_name("declarator")
        {
            let signature = node
                .child_by_field_name("parameters")
                .map(|params| {
                    params
                        .named_children(&mut params.walk())
                        .map(|p| {
                            let ty = p
                                .child_by_field_name("type")
                                .map(|t| node_text(t, &file.source))
                                .unwrap_or("");
                            let shape = p
                                .child_by_field_name("declarator")
                                .map(|d| d.kind())
                                .unwrap_or("");
                            format!("{ty}:{shape}")
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            declarations
                .entry(node_text(name, &file.source).to_owned())
                .or_default()
                .insert(signature);
        }
        if node.kind() != "function_definition"
            || node.has_error()
            || node.parent().is_none_or(|p| p.kind() != "translation_unit")
        {
            return;
        }
        let Some(declarator) = node.child_by_field_name("declarator") else {
            return;
        };
        if declarator.kind() != "function_declarator" {
            return;
        }
        let (Some(name), Some(parameters), Some(body)) = (
            declarator.child_by_field_name("declarator"),
            declarator.child_by_field_name("parameters"),
            node.child_by_field_name("body"),
        ) else {
            return;
        };
        if name.kind() != "identifier" {
            return;
        }
        let mut cursor = parameters.walk();
        let params = parameters
            .named_children(&mut cursor)
            .map(|parameter| {
                let ty = parameter.child_by_field_name("type")?;
                let formal = parameter.child_by_field_name("declarator")?;
                (parameter.kind() == "parameter_declaration"
                    && formal.kind() == "identifier"
                    && matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
                .then(|| node_text(formal, &file.source).to_owned())
            })
            .collect::<Vec<_>>();
        *definition_counts
            .entry(node_text(name, &file.source).to_owned())
            .or_default() += 1;
        definitions.insert(
            node_text(name, &file.source).to_owned(),
            (
                body.start_position().row + 1,
                body.end_position().row + 1,
                params,
            ),
        );
    });
    definitions.retain(|name, _| {
        declarations.get(name).is_some_and(|s| s.len() == 1)
            && definition_counts.get(name) == Some(&1)
    });
    let mut calls = Vec::new();
    let mut invalid = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        let name = node_text(node, &file.source);
        if node.kind() != "identifier" || !definitions.contains_key(name) {
            return;
        }
        let Some(parent) = node.parent() else {
            invalid.insert(name.to_owned());
            return;
        };
        if parent.kind() == "function_declarator"
            && parent.child_by_field_name("declarator") == Some(node)
        {
            return;
        }
        if parent.kind() != "call_expression"
            || parent.child_by_field_name("function") != Some(node)
        {
            invalid.insert(name.to_owned());
            return;
        }
        // Unqualified member lookup must not bind a same-named free function.
        let mut ancestor = parent.parent();
        while let Some(scope) = ancestor {
            if matches!(scope.kind(), "class_specifier" | "struct_specifier") {
                return;
            }
            ancestor = scope.parent();
        }
        let Some(arguments) = parent.child_by_field_name("arguments") else {
            return;
        };
        let mut cursor = arguments.walk();
        calls.push((
            name.to_owned(),
            parent.start_position().row + 1,
            arguments
                .named_children(&mut cursor)
                .map(|n| transparent_partition_value(n, &file.source))
                .collect::<Vec<_>>(),
        ));
    });
    for line in file
        .source
        .lines()
        .filter(|line| line.trim_start().starts_with('#'))
    {
        for token in identifier_tokens(line) {
            if definitions.contains_key(token) {
                invalid.insert(token.to_owned());
            }
        }
    }
    for _ in 0..4 {
        let mut additions = Vec::new();
        for (name, line, arguments) in &calls {
            if invalid.contains(name) {
                continue;
            }
            let (begin, end, parameters) = &definitions[name];
            if arguments.len() != parameters.len() {
                continue;
            }
            for (argument, parameter) in arguments.iter().zip(parameters) {
                if let Some(parameter) = parameter
                    && origins.supports_parallel_argument(argument, *line)
                {
                    additions.push((
                        *begin,
                        *end,
                        parameter.clone(),
                        origins.supports_runtime_identity(argument, *line),
                    ));
                }
            }
        }
        let mut changed = false;
        for (begin, end, parameter, runtime) in additions {
            if runtime {
                changed |= origins
                    .runtime_parameters
                    .insert((begin, end, parameter.clone()));
            }
            if let Some((_, _, parameters)) = origins
                .regions
                .iter_mut()
                .find(|(b, e, _)| *b == begin && *e == end)
            {
                changed |= parameters.insert(parameter);
            }
        }
        if !changed {
            break;
        }
    }
}

fn propagate_local_callback_partition_arguments(
    file: &ParsedCppFile,
    origins: &mut IndexPartitionOrigins,
    concurrent: &HashSet<usize>,
) {
    let Some(tree) = &file.tree else { return };
    let mut additions = Vec::new();
    walk_nodes(tree.root_node(), &mut |lambda| {
        if lambda.kind() != "lambda_expression" || lambda.has_error() {
            return;
        }
        let Some(binding) = lambda.parent().filter(|n| {
            n.kind() == "init_declarator" && n.child_by_field_name("value") == Some(lambda)
        }) else {
            return;
        };
        let Some(name_node) = binding
            .child_by_field_name("declarator")
            .filter(|n| n.kind() == "identifier")
        else {
            return;
        };
        let Some(binding_scope) = binding
            .parent()
            .and_then(|n| n.parent())
            .filter(|n| n.kind() == "compound_statement")
        else {
            return;
        };
        let Some(body) = lambda.child_by_field_name("body") else {
            return;
        };
        let mut scope = binding.parent();
        while scope
            .is_some_and(|n| !matches!(n.kind(), "function_definition" | "lambda_expression"))
        {
            scope = scope.and_then(|n| n.parent());
        }
        let Some(scope_body) = scope
            .and_then(|n| n.child_by_field_name("body"))
            .filter(|n| !n.has_error())
        else {
            return;
        };
        if body.start_position().row == scope_body.start_position().row
            && body.end_position().row == scope_body.end_position().row
        {
            return;
        }
        let name = node_text(name_node, &file.source);
        let mut parameters = Vec::new();
        walk_nodes(lambda, &mut |node| {
            if node.kind() == "parameter_declaration" && node.start_byte() < body.start_byte() {
                parameters.push(
                    node.child_by_field_name("declarator")
                        .and_then(|d| declarator_variable_name(d, &file.source)),
                );
            }
        });
        let mut safe = true;
        let mut inferred = HashSet::new();
        let mut calls = 0;
        walk_nodes(scope_body, &mut |node| {
            // Earlier calls or calls outside the declaration's block can bind
            // a different same-named function, not this local closure.
            if node.start_byte() < binding.end_byte()
                || node.start_byte() >= binding_scope.end_byte()
            {
                return;
            }
            if !safe
                || node.kind() != "identifier"
                || node_text(node, &file.source) != name
                || node == name_node
            {
                return;
            }
            let Some(call) = node.parent().filter(|n| {
                n.kind() == "call_expression" && n.child_by_field_name("function") == Some(node)
            }) else {
                safe = false;
                return;
            };
            if concurrent.contains(&(call.start_position().row + 1)) {
                // Argument-only replacement cannot withdraw execution-domain
                // evidence from a parallel caller.
                safe = false;
                return;
            }
            // Reject shadowing/reassignment/address escape above, and callback
            // calls from another lambda: those need their own binding summary.
            let mut parent = call.parent();
            while let Some(n) = parent {
                if n == scope_body {
                    break;
                }
                if matches!(n.kind(), "lambda_expression" | "function_definition") {
                    safe = false;
                    return;
                }
                parent = n.parent();
            }
            let Some(arguments) = call.child_by_field_name("arguments") else {
                safe = false;
                return;
            };
            let args = arguments
                .named_children(&mut arguments.walk())
                .collect::<Vec<_>>();
            if args.len() != parameters.len() {
                safe = false;
                return;
            }
            calls += 1;
            for (arg, parameter) in args.iter().zip(&parameters) {
                if let Some(parameter) = parameter
                    && origins
                        .supports(node_text(*arg, &file.source), call.start_position().row + 1)
                {
                    inferred.insert(parameter.clone());
                }
            }
        });
        if safe && calls > 0 {
            additions.push((
                body.start_position().row + 1,
                body.end_position().row + 1,
                inferred,
            ));
        }
    });
    for (start, end, parameters) in additions {
        if let Some((_, _, region)) = origins
            .regions
            .iter_mut()
            .find(|(s, e, _)| *s == start && *e == end)
        {
            // All observed references bind this nonescaping local callback.
            // Replace its parameter-name guesses positionally: a worker in
            // argument 2 cannot justify a data index arriving in argument 1.
            *region = parameters;
        }
    }
}

/// A local callback is not itself an externally callable partition API. Only
/// withdraw parameter seeds when all references are local assignments or
/// sequential direct calls, and no call supplies an existing partition value.
fn local_callback_has_only_sequential_data_calls(
    lambda: tree_sitter::Node<'_>,
    file: &ParsedCppFile,
    origins: &IndexPartitionOrigins,
    concurrent: &HashSet<usize>,
) -> bool {
    let Some(binding) = lambda.parent() else {
        return false;
    };
    let name_node = match binding.kind() {
        "init_declarator" if binding.child_by_field_name("value") == Some(lambda) => {
            binding.child_by_field_name("declarator")
        }
        "assignment_expression" if binding.child_by_field_name("right") == Some(lambda) => {
            binding.child_by_field_name("left")
        }
        _ => None,
    };
    let Some(name_node) = name_node.filter(|n| n.kind() == "identifier") else {
        return false;
    };
    let name = node_text(name_node, &file.source);
    let mut ancestor = binding.parent();
    let mut function = None;
    while let Some(node) = ancestor {
        if node.kind() == "lambda_expression" {
            return false;
        }
        if node.kind() == "function_definition" {
            function = Some(node);
            break;
        }
        ancestor = node.parent();
    }
    let Some(body) = function.and_then(|n| n.child_by_field_name("body")) else {
        return false;
    };
    if body.has_error() {
        return false;
    }
    if lambda
        .child_by_field_name("body")
        .is_some_and(|lambda_body| {
            lambda_body.start_position().row == body.start_position().row
                && lambda_body.end_position().row == body.end_position().row
        })
    {
        // Origins currently use line ranges. Do not clear a range also naming
        // the enclosing callable and accidentally erase its real API inputs.
        return false;
    }
    let mut declarations = Vec::new();
    walk_nodes(body, &mut |node| {
        if node.kind() != "declaration" {
            return;
        }
        for declaration in node.children_by_field_name("declarator", &mut node.walk()) {
            let id = if declaration.kind() == "init_declarator" {
                declaration.child_by_field_name("declarator")
            } else {
                Some(declaration)
            };
            if let Some(id) =
                id.filter(|id| id.kind() == "identifier" && node_text(*id, &file.source) == name)
            {
                declarations.push((id, node));
            }
        }
    });
    let [(declaration, statement)] = declarations.as_slice() else {
        return false;
    };
    if statement.start_byte() > lambda.start_byte()
        || identifier_tokens(node_text(*statement, &file.source))
            .any(|t| matches!(t, "static" | "thread_local" | "extern"))
    {
        return false;
    }
    let mut safe = true;
    let mut calls = 0;
    walk_nodes(body, &mut |use_node| {
        if !safe
            || use_node.kind() != "identifier"
            || node_text(use_node, &file.source) != name
            || use_node == *declaration
        {
            return;
        }
        let Some(parent) = use_node.parent() else {
            safe = false;
            return;
        };
        let mut scope = Some(parent);
        while let Some(node) = scope {
            if node == body {
                break;
            }
            if node.kind() == "lambda_expression" {
                safe = false;
                return;
            }
            scope = node.parent();
        }
        if parent.kind() == "assignment_expression"
            && parent.child_by_field_name("left") == Some(use_node)
        {
            return;
        }
        if parent.kind() != "call_expression"
            || parent.child_by_field_name("function") != Some(use_node)
            || concurrent.contains(&(use_node.start_position().row + 1))
        {
            safe = false;
            return;
        }
        let Some(arguments) = parent.child_by_field_name("arguments") else {
            safe = false;
            return;
        };
        if arguments
            .named_children(&mut arguments.walk())
            .any(|argument| {
                origins.supports(
                    node_text(argument, &file.source),
                    use_node.start_position().row + 1,
                )
            })
        {
            safe = false;
            return;
        }
        calls += 1;
    });
    safe && calls > 0
}

fn transparent_partition_value(node: tree_sitter::Node<'_>, source: &str) -> String {
    if node.kind() == "binary_expression"
        && node
            .child_by_field_name("operator")
            .is_some_and(|op| node_text(op, source) == "*")
        && ["left", "right"].iter().any(|side| {
            node.child_by_field_name(side)
                .is_some_and(|n| node_text(n, source).trim() == "0")
        })
        && ["left", "right"].iter().all(|side| {
            node.child_by_field_name(side)
                .is_some_and(|n| primitive_local_operand(n, source))
        })
    {
        return "0".to_string();
    }
    match node.kind() {
        "identifier" | "qualified_identifier" | "number_literal" => {
            node_text(node, source).to_string()
        }
        "field_expression" => {
            // A descriptor member may carry a partition, but loading a table
            // element indexed by a worker does not make its value an identity.
            if node
                .child_by_field_name("argument")
                .is_some_and(|argument| {
                    matches!(
                        argument.kind(),
                        "identifier" | "field_expression" | "qualified_identifier"
                    )
                })
            {
                node_text(node, source).to_string()
            } else {
                String::new()
            }
        }
        "call_expression" => {
            let callee = node
                .child_by_field_name("function")
                .map(|function| node_text(function, source))
                .unwrap_or("");
            let name = identifier_tokens(callee).last().unwrap_or("");
            if name.ends_with("get_thread_num")
                || name.ends_with("get_smp_processor_id")
                || matches!(name, "pthread_self" | "sched_getcpu" | "rte_lcore_id")
            {
                format!("{callee}()")
            } else {
                // A call argument is not a return-value flow summary. E.g.
                // snprintf(..., worker) returns a length, not a worker id.
                String::new()
            }
        }
        "binary_expression" => {
            let operator = node
                .child_by_field_name("operator")
                .map(|operator| node_text(operator, source))
                .unwrap_or("");
            if !matches!(
                operator,
                "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>"
            ) {
                return String::new();
            }
            let value = |field| {
                node.child_by_field_name(field)
                    .map(|child| transparent_partition_value(child, source))
                    .unwrap_or_default()
            };
            format!("{} {operator} {}", value("left"), value("right"))
        }
        "parenthesized_expression" => node
            .named_child(0)
            .map(|child| transparent_partition_value(child, source))
            .unwrap_or_default(),
        "cast_expression" => node
            .child_by_field_name("value")
            .map(|child| transparent_partition_value(child, source))
            .unwrap_or_default(),
        "unary_expression" => {
            let operator = node
                .child_by_field_name("operator")
                .map(|operator| node_text(operator, source))
                .unwrap_or("");
            if matches!(operator, "+" | "-" | "~") {
                node.child_by_field_name("argument")
                    .map(|child| transparent_partition_value(child, source))
                    .unwrap_or_default()
            } else {
                String::new()
            }
        }
        _ => String::new(),
    }
}

/// A name-only alignment proof cannot select among distinct type bindings.
/// In particular, tree-sitter retains mutually exclusive preprocessor branches.
/// Keep those candidates until a configuration/scope-aware binding is known.
fn discard_ambiguous_alignment_names(files: &[ParsedCppFile], names: &mut HashSet<String>) {
    let mut bindings: HashMap<String, usize> = HashMap::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            let name = match node.kind() {
                "struct_specifier" | "class_specifier" | "union_specifier" => {
                    if node.child_by_field_name("body").is_none() {
                        return;
                    }
                    node.child_by_field_name("name")
                }
                "alias_declaration" => node.child_by_field_name("name"),
                "type_definition" => {
                    let name = node.child_by_field_name("declarator");
                    // typedef struct X { ... } X declares one binding, not two.
                    if let (Some(alias), Some(tag)) = (
                        name,
                        node.child_by_field_name("type")
                            .and_then(|ty| ty.child_by_field_name("name")),
                    ) && node_text(alias, &file.source) == node_text(tag, &file.source)
                    {
                        return;
                    }
                    name
                }
                _ => return,
            };
            if let Some(name) = name {
                let name = node_text(name, &file.source);
                if names.contains(name) {
                    *bindings.entry(name.to_owned()).or_default() += 1;
                }
            }
        });
    }
    names.retain(|name| bindings.get(name).copied().unwrap_or(0) <= 1);
}

fn protected_indexed_symbols(lines: &[&str], aligned_types: &HashSet<String>) -> HashSet<String> {
    let mut protected = HashSet::new();
    for line in lines {
        let lower = line.to_ascii_lowercase();
        // Alignment on an enclosing record only aligns the first element of
        // that record.  It does not pad an array member's individual elements.
        let is_record_declaration = lower.contains("struct ") || lower.contains("class ");
        if !is_record_declaration
            && line.contains('[')
            && identifier_tokens(line).any(|token| aligned_types.contains(token))
            && let Some(name) = indexed_symbol(line)
        {
            protected.insert(name);
        }
    }
    protected
}

pub fn collect_static_hot_state_candidates(
    files: &[ParsedCppFile],
    structs: &[CppStructInfo],
    cache_line_size: usize,
) -> Vec<StaticHotStateCandidate> {
    collect_static_hot_state_candidates_with_commands(files, structs, cache_line_size, &[])
}

pub(super) fn collect_static_hot_state_candidates_with_commands(
    files: &[ParsedCppFile],
    structs: &[CppStructInfo],
    cache_line_size: usize,
    commands: &[super::types::CppCompileCommand],
) -> Vec<StaticHotStateCandidate> {
    let runtime_views = super::unevaluated::views(files, commands);
    let files = runtime_views.as_ref();
    let linkage_views = internal_index_api::views(files, commands);
    let files = linkage_views.as_ref();
    let mut candidates = Vec::new();
    let global_re = Regex::new(
        r"(?m)^\s*(?:static\s+)?(?:std::)?(?:atomic(?:<[^;]+>|_[A-Za-z0-9_]+)|[A-Za-z_][A-Za-z0-9_:<>]*\s+)([A-Za-z_][A-Za-z0-9_]*)\s*(?:\[[^\]]+\])?\s*(?:=|\{|\;)",
    )
    .ok();
    for file in files {
        let Some(re) = &global_re else {
            continue;
        };
        // A directive's replacement tokens are not storage declarations.
        // Ignore every physical line of a continued directive as well: its
        // braces must not change the surrounding C++ lexical scope.
        let mut in_directive = false;
        let directive_lines = file
            .source
            .lines()
            .enumerate()
            .filter_map(|(row, line)| {
                let directive = in_directive || line.trim_start().starts_with('#');
                in_directive = directive && line.trim_end().ends_with('\\');
                directive.then_some(row)
            })
            .collect::<HashSet<_>>();
        let mut scope_stack: Vec<bool> = Vec::new();
        for (idx, line) in file.source.lines().enumerate() {
            let line_start = line.trim_start();
            if directive_lines.contains(&idx) || is_comment_only_line(line) {
                continue;
            }
            let at_namespace_scope = scope_stack.iter().all(|is_namespace| *is_namespace);
            if !at_namespace_scope {
                update_scope_stack(line, &mut scope_stack);
                continue;
            }

            // Apply storage qualifiers before either the regex or fallback
            // branch. The fallback must not turn a const initializer's words
            // (for example a counter macro) into mutable static storage.
            let declaration_prefix = line.split('=').next().unwrap_or(line);
            if identifier_tokens(declaration_prefix)
                .any(|token| matches!(token, "const" | "constexpr" | "thread_local"))
            {
                update_scope_stack(line, &mut scope_stack);
                continue;
            }

            let captures = re.captures(line);
            let full_match = captures.as_ref().and_then(|caps| caps.get(0));
            let Some(full) = full_match else {
                let line_text = line.trim();
                if !line_text.contains(';') {
                    update_scope_stack(line, &mut scope_stack);
                    continue;
                }
                let lower = line_text.to_lowercase();
                let hot = lower.contains("atomic")
                    || lower.contains("counter")
                    || lower.contains("stats")
                    || lower.contains("bucket")
                    || lower.contains("shard")
                    || lower.contains("singleton")
                    || lower.contains("spinlock")
                    || (lower.contains("lock") && line_text.contains('['));
                if hot
                    && !static_candidate_is_protected(line_text, cache_line_size)
                    && let Some(name) = extract_static_candidate_name(line_text)
                {
                    let is_array_like = line_text.contains('[')
                        || lower.contains("pool_")
                        || lower.contains("locks")
                        || lower.contains("buckets")
                        || lower.contains("slots")
                        || lower.contains("shards")
                        || lower.contains("counters");
                    candidates.push(StaticHotStateCandidate {
                        file: file.path.clone(),
                        line: idx + 1,
                        snippet: line_text.to_string(),
                        field_name: Some(name),
                        is_array_like,
                        is_file_scope: true,
                        is_generic_array: false,
                        access_file: None,
                        access_line: None,
                        access_index: None,
                        access_function: None,
                        access_kind: None,
                        access_in_concurrent_context: false,
                        has_partitioned_index_evidence: false,
                        guard_ids: Vec::new(),
                        evidence: vec![
                            "全局状态证据: namespace/static 可变热点状态可能被多线程共享"
                                .to_string(),
                        ],
                    });
                }
                update_scope_stack(line, &mut scope_stack);
                continue;
            };
            let line_text = full.as_str().trim();
            let template_static_member_definition =
                line_start.starts_with("template ") && line.contains("::") && line.contains('[');
            if line_start.starts_with("enum ")
                || line_start.starts_with("struct ")
                || line_start.starts_with("class ")
                || line_start.starts_with("union ")
                || line_start.starts_with("namespace ")
                || (line_start.starts_with("template ") && !template_static_member_definition)
                || line_start.starts_with("using ")
                || line_start.starts_with("typedef ")
                || line_start.contains('(')
            {
                update_scope_stack(line, &mut scope_stack);
                continue;
            }
            if line_text.contains("thread_local")
                || line_text.contains("constexpr")
                || line_text.contains("const ")
            {
                update_scope_stack(line, &mut scope_stack);
                continue;
            }
            let lower = line_text.to_lowercase();
            let hot = lower.contains("atomic")
                || lower.contains("counter")
                || lower.contains("stats")
                || lower.contains("bucket")
                || lower.contains("shard")
                || lower.contains("singleton")
                || lower.contains("spinlock")
                || (lower.contains("lock") && line_text.contains('['));
            if !hot {
                update_scope_stack(line, &mut scope_stack);
                continue;
            }
            if static_candidate_is_protected(line_text, cache_line_size) {
                update_scope_stack(line, &mut scope_stack);
                continue;
            }
            let is_array_like = line_text.contains('[')
                || lower.contains("pool_")
                || lower.contains("locks")
                || lower.contains("buckets")
                || lower.contains("slots")
                || lower.contains("shards")
                || lower.contains("counters");
            candidates.push(StaticHotStateCandidate {
                file: file.path.clone(),
                line: idx + 1,
                snippet: line_text.to_string(),
                field_name: captures
                    .as_ref()
                    .and_then(|caps| caps.get(1))
                    .map(|m| m.as_str().to_string())
                    .or_else(|| extract_static_candidate_name(line_text)),
                is_array_like,
                is_file_scope: true,
                is_generic_array: false,
                access_file: None,
                access_line: None,
                access_index: None,
                access_function: None,
                access_kind: None,
                access_in_concurrent_context: false,
                has_partitioned_index_evidence: false,
                guard_ids: Vec::new(),
                evidence: vec![
                    "全局状态证据: namespace/static 可变热点状态可能被多线程共享".to_string(),
                ],
            });
            update_scope_stack(line, &mut scope_stack);
        }
        // Preprocessor alternatives and macro bodies can make a purely
        // lexical brace stack drift even though tree-sitter still recovers a
        // namespace/file-scope declaration.  Complement it with AST-backed
        // global array discovery and exclude function- and record-local
        // declarations by ancestor kind.
        if let Some(tree) = &file.tree {
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() != "declaration"
                    || directive_lines.contains(&node.start_position().row)
                {
                    return;
                }
                let mut ancestor = node.parent();
                while let Some(parent) = ancestor {
                    if matches!(
                        parent.kind(),
                        "function_definition"
                            | "lambda_expression"
                            | "struct_specifier"
                            | "class_specifier"
                    ) {
                        return;
                    }
                    ancestor = parent.parent();
                }
                let declaration = node_text(node, &file.source);
                let lower = declaration.to_ascii_lowercase();
                if !declaration.contains('[')
                    || identifier_tokens(declaration)
                        .any(|token| matches!(token, "const" | "constexpr" | "thread_local"))
                    || static_candidate_is_protected(declaration, cache_line_size)
                {
                    return;
                }
                let generic_array = !(lower.contains("atomic")
                    || lower.contains("spinlock")
                    || lower.contains("mutex")
                    || lower.contains("lock"));
                if generic_array && !identifier_tokens(declaration).any(|token| token == "LOCAL") {
                    return;
                }
                let mut cursor = node.walk();
                for declarator in node.children_by_field_name("declarator", &mut cursor) {
                    if declarator.kind() != "array_declarator" {
                        continue;
                    }
                    let Some(name) = declarator_variable_name(declarator, &file.source)
                        .or_else(|| extract_static_candidate_name(declaration))
                    else {
                        continue;
                    };
                    candidates.push(StaticHotStateCandidate {
                        file: file.path.clone(),
                        line: node.start_position().row + 1,
                        snippet: declaration.trim().to_string(),
                        field_name: Some(name),
                        is_array_like: true,
                        is_file_scope: true,
                        is_generic_array: generic_array,
                        access_file: None,
                        access_line: None,
                        access_index: None,
                        access_function: None,
                        access_kind: None,
                        access_in_concurrent_context: false,
                        has_partitioned_index_evidence: false,
                        guard_ids: Vec::new(),
                        evidence: vec![if generic_array {
                            "AST 全局数组证据: file/namespace-scope 可变数组可与同分区数组形成 sibling storage group".to_string()
                        } else {
                            "AST 全局状态证据: file/namespace-scope 同步对象数组".to_string()
                        }],
                    });
                }
            });
        }
        let mut fallback_scope_stack = Vec::new();
        for (offset, line) in file.source.lines().enumerate() {
            if directive_lines.contains(&offset) || is_comment_only_line(line) {
                continue;
            }
            let declaration = line.split("//").next().unwrap_or(line).trim();
            let at_namespace_scope = fallback_scope_stack
                .iter()
                .all(|is_namespace| *is_namespace);
            if !at_namespace_scope {
                update_scope_stack(line, &mut fallback_scope_stack);
                continue;
            }
            let lower = declaration.to_ascii_lowercase();
            if !declaration.contains('[')
                || identifier_tokens(declaration)
                    .any(|token| matches!(token, "const" | "constexpr" | "thread_local"))
                || static_candidate_is_protected(declaration, cache_line_size)
            {
                update_scope_stack(line, &mut fallback_scope_stack);
                continue;
            }
            if let Some(name) = extract_static_candidate_name(declaration) {
                let generic_array = !(lower.contains("atomic")
                    || lower.contains("spinlock")
                    || lower.contains("mutex")
                    || lower.contains("lock"));
                if generic_array && !identifier_tokens(declaration).any(|token| token == "LOCAL") {
                    update_scope_stack(line, &mut fallback_scope_stack);
                    continue;
                }
                candidates.push(StaticHotStateCandidate {
                    file: file.path.clone(),
                    line: offset + 1,
                    snippet: declaration.to_string(),
                    field_name: Some(name),
                    is_array_like: true,
                    is_file_scope: true,
                    is_generic_array: generic_array,
                    access_file: None,
                    access_line: None,
                    access_index: None,
                    access_function: None,
                    access_kind: None,
                    access_in_concurrent_context: false,
                    has_partitioned_index_evidence: false,
                    guard_ids: Vec::new(),
                    evidence: vec![if generic_array {
                        "file/namespace-scope 可变数组证据: 可与同分区数组形成 sibling storage group".to_string()
                    } else {
                        "显式 static 存储证据: 同步对象数组具有程序级共享生命周期".to_string()
                    }],
                });
            }
            update_scope_stack(line, &mut fallback_scope_stack);
        }
    }
    let mut aligned_types: HashSet<String> = structs
        .iter()
        .filter(|record| record.is_cache_aligned || record.has_cache_padding)
        .map(|record| record.name.clone())
        .collect();
    aligned_types.extend(source_declared_aligned_type_names(files, cache_line_size));
    discard_ambiguous_alignment_names(files, &mut aligned_types);
    candidates.retain(|candidate| {
        !aligned_types
            .iter()
            .any(|aligned| token_occurs(&candidate.snippet, aligned))
    });
    let files_by_path: HashMap<&str, &ParsedCppFile> = files
        .iter()
        .map(|file| (file.path.as_str(), file))
        .collect();
    for record in structs {
        for field in &record.static_fields {
            if !field.is_array
                || !field.is_hot_sync
                || field.is_cache_padded
                || aligned_types.iter().any(|aligned| {
                    field
                        .element_type
                        .as_deref()
                        .is_some_and(|element| token_occurs(element, aligned))
                        || token_occurs(&field.ty_str, aligned)
                })
            {
                continue;
            }
            let declaration = files_by_path
                .get(record.file.as_str())
                .and_then(|file| file.source.lines().nth(field.line.saturating_sub(1)))
                .unwrap_or("");
            candidates.push(StaticHotStateCandidate {
                file: record.file.clone(),
                line: field.line,
                snippet: declaration.trim().to_string(),
                field_name: Some(field.name.clone()),
                is_array_like: true,
                is_file_scope: false,
                is_generic_array: false,
                access_file: None,
                access_line: None,
                access_index: None,
                access_function: None,
                access_kind: None,
                access_in_concurrent_context: false,
                has_partitioned_index_evidence: false,
                guard_ids: Vec::new(),
                evidence: vec![
                    format!(
                        "类静态成员证据: '{}.{}' 是连续同步对象数组",
                        record.name, field.name
                    ),
                    "布局证据: 数组元素类型未见 cache-line 对齐".to_string(),
                ],
            });
        }
    }
    // Function-local `static` arrays have program lifetime just like
    // namespace-scope storage, but their lexical scope must remain attached
    // to the defining function so a same-named parameter in another callable
    // cannot donate an access witness.
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "declaration" || node.has_error() {
                return;
            }
            let declaration = node_text(node, &file.source);
            let lower = declaration.to_ascii_lowercase();
            if !identifier_tokens(declaration).any(|token| token == "static")
                || !declaration.contains('[')
                || !(lower.contains("atomic")
                    || lower.contains("mutex")
                    || lower.contains("spinlock")
                    || lower.contains("lock"))
                || static_candidate_is_protected(declaration, cache_line_size)
            {
                return;
            }
            let mut ancestor = node.parent();
            let mut in_function = false;
            while let Some(parent) = ancestor {
                if parent.kind() == "function_definition" {
                    in_function = true;
                    break;
                }
                ancestor = parent.parent();
            }
            if !in_function {
                return;
            }
            let name = extract_static_candidate_name(declaration).or_else(|| {
                let mut cursor = node.walk();
                node.children_by_field_name("declarator", &mut cursor)
                    .find(|child| child.kind() == "array_declarator")
                    .and_then(|array| declarator_variable_name(array, &file.source))
            });
            let Some(name) = name else { return };
            candidates.push(StaticHotStateCandidate {
                file: file.path.clone(),
                line: node.start_position().row + 1,
                snippet: declaration.trim().to_string(),
                field_name: Some(name),
                is_array_like: true,
                is_file_scope: false,
                is_generic_array: false,
                access_file: None,
                access_line: None,
                access_index: None,
                access_function: None,
                access_kind: None,
                access_in_concurrent_context: false,
                has_partitioned_index_evidence: false,
                guard_ids: Vec::new(),
                evidence: vec![
                    "函数局部 static 存储证据: 数组具有程序级共享生命周期".to_string(),
                    "布局证据: static 数组元素类型未见 cache-line 对齐".to_string(),
                ],
            });
        });
    }
    // A function's `static` specifier describes linkage, not the lifetime of
    // its array parameters. Reject only AST-proven parameter declarations;
    // function-pointer arrays and ambiguous/recovered syntax remain eligible.
    candidates.retain(|candidate| {
        // Generic candidates were admitted only from a file/namespace-scope
        // declaration, so walking the complete AST again for each one is
        // redundant and quadratic on large translation units.
        candidate.is_generic_array
            || !files_by_path
                .get(candidate.file.as_str())
                .is_some_and(|file| static_candidate_is_array_parameter(file, candidate))
    });
    // Preprocessor branches often declare the same platform abstraction
    // several times in one file.  Coalesce those alternatives before access
    // attachment so a unique accessor can bind to the logical storage symbol.
    let mut declaration_seen = HashSet::new();
    candidates.retain(|candidate| {
        declaration_seen.insert((candidate.file.clone(), candidate.field_name.clone()))
    });
    attach_static_access_sites(files, &mut candidates);
    promote_mutable_sync_array_accesses(files, structs, &mut candidates);
    let mut seen = HashSet::new();
    candidates
        .retain(|candidate| seen.insert((candidate.file.clone(), candidate.field_name.clone())));
    candidates
}

/// A static array of lock-like objects is mutated through a public mutable
/// reference accessor.  The access site itself is lexically a read
/// (`return pool_[i]`), while the caller mutates the selected element through
/// `lock`/`unlock`.  Preserve that write capability and indexed partition
/// witness without treating arbitrary array reference returns as writes.
fn promote_mutable_sync_array_accesses(
    files: &[ParsedCppFile],
    structs: &[CppStructInfo],
    candidates: &mut [StaticHotStateCandidate],
) {
    for candidate in candidates.iter_mut() {
        if !matches!(candidate.access_kind, Some(CppAccessKind::Read))
            || candidate.access_index.is_none()
            || candidate.access_function.is_none()
        {
            continue;
        }
        let Some(owner) = structs.iter().find(|record| {
            record.file == candidate.file
                && record
                    .static_fields
                    .iter()
                    .any(|field| Some(field.name.as_str()) == candidate.field_name.as_deref())
        }) else {
            continue;
        };
        let Some(field) = owner
            .static_fields
            .iter()
            .find(|field| Some(field.name.as_str()) == candidate.field_name.as_deref())
        else {
            continue;
        };
        let Some(element) = field.element_type.as_deref() else {
            continue;
        };
        let element_name = element.rsplit("::").next().unwrap_or(element).trim();
        let lock_like = structs.iter().any(|record| {
            record.name == element_name
                && record
                    .public_methods
                    .iter()
                    .any(|method| matches!(method.as_str(), "lock" | "unlock" | "try_lock"))
        });
        if !lock_like {
            continue;
        }
        let Some(file) = files.iter().find(|file| {
            candidate
                .access_file
                .as_deref()
                .is_some_and(|path| path == file.path)
        }) else {
            continue;
        };
        let access_line = candidate.access_line.unwrap_or_default();
        let function_name = candidate.access_function.as_deref().unwrap_or_default();
        let preceding_lines = file.source.lines().take(access_line).collect::<Vec<_>>();
        let mutable_accessor = preceding_lines
            .iter()
            .rev()
            .find(|line| line.contains(function_name) && line.contains('&'))
            .is_some_and(|line| !line.split('(').next().unwrap_or(line).contains("const"));
        if !mutable_accessor {
            continue;
        }
        candidate.access_kind = Some(CppAccessKind::ReadModifyWrite);
        candidate.has_partitioned_index_evidence = true;
        candidate.evidence.push(format!(
            "可变同步访问证据: '{}' 返回 '{}' 的 mutable reference；调用者可对索引元素执行 lock/unlock",
            function_name, element_name
        ));
        candidate.evidence.push(
            "分区证据: 每次 API 访问选择静态同步对象数组中的独立元素；元素布局未见 cache-line 对齐"
                .to_string(),
        );
    }
}

fn static_candidate_is_array_parameter(
    file: &ParsedCppFile,
    candidate: &StaticHotStateCandidate,
) -> bool {
    let (Some(tree), Some(symbol)) = (&file.tree, candidate.field_name.as_deref()) else {
        return false;
    };
    if !candidate.snippet.contains('(') {
        return false;
    }
    let mut offset = 0;
    for (index, line) in file.source.split_inclusive('\n').enumerate() {
        if index + 1 == candidate.line {
            offset += line.len() - line.trim_start().len();
            break;
        }
        offset += line.len();
    }
    let Some(mut node) = tree.root_node().descendant_for_byte_range(offset, offset) else {
        return false;
    };
    while !matches!(node.kind(), "declaration" | "field_declaration") {
        let Some(parent) = node.parent() else {
            return false;
        };
        node = parent;
    }
    if node.has_error() || node_text(node, &file.source).trim() != candidate.snippet.trim() {
        return false;
    }
    let mut parameter = false;
    let mut non_parameter = false;
    walk_nodes(node, &mut |identifier| {
        if identifier.kind() != "identifier" || node_text(identifier, &file.source) != symbol {
            return;
        }
        let mut ancestor = identifier.parent();
        while let Some(parent) = ancestor {
            if matches!(
                parent.kind(),
                "parameter_declaration" | "optional_parameter_declaration"
            ) {
                parameter = true;
                return;
            }
            if parent == node {
                break;
            }
            ancestor = parent.parent();
        }
        non_parameter = true;
    });
    parameter && !non_parameter
}

// Line-based access attachment must not resolve a local declaration to a
// same-named static object. Only claim complete interior lines of an ordinary
// block: mixed statements on declaration/closing lines remain conservative.
fn static_access_local_shadows(
    file: &ParsedCppFile,
) -> HashMap<String, Vec<(usize, usize, usize)>> {
    let mut shadows = HashMap::<String, Vec<(usize, usize, usize)>>::new();
    let Some(tree) = &file.tree else {
        return shadows;
    };
    let mut scope_texts = HashMap::<usize, (String, bool)>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "declaration" || node.has_error() {
            return;
        }
        let Some(scope) = node.parent().filter(|p| p.kind() == "compound_statement") else {
            return;
        };
        let mut ancestor = scope.parent();
        let mut local = false;
        while let Some(parent) = ancestor {
            if matches!(parent.kind(), "function_definition" | "lambda_expression") {
                local = true;
                break;
            }
            ancestor = parent.parent();
        }
        if !local {
            return;
        }
        let mut cursor = node.walk();
        for declarator in node.children_by_field_name("declarator", &mut cursor) {
            let Some(name) = declarator_variable_name(declarator, &file.source) else {
                continue;
            };
            // Keep an explicitly qualified alias of the global candidate.
            // Other alias provenance remains unresolved, not a name match.
            let (compact_scope, has_block_comment) =
                scope_texts.entry(scope.start_byte()).or_insert_with(|| {
                    let text = node_text(scope, &file.source);
                    (
                        text.chars().filter(|ch| !ch.is_whitespace()).collect(),
                        text.contains("/*"),
                    )
                });
            if compact_scope.contains(&format!("::{name}"))
                || *has_block_comment
                || declarator
                    .child_by_field_name("value")
                    .is_some_and(|value| token_occurs(node_text(value, &file.source), &name))
            {
                continue;
            }
            shadows.entry(name).or_default().push((
                node.end_position().row + 1,
                scope.end_position().row + 1,
                node.start_position().row + 1,
            ));
        }
    });
    shadows
}

fn attach_static_access_sites(files: &[ParsedCppFile], candidates: &mut [StaticHotStateCandidate]) {
    let macro_effects = indexed_macros::collect(files);
    let atomic_element = Regex::new(
        r"^\s*(?:(?:extern|static|inline|constinit)\s+)*(?:::)?std::atomic\s*<[^<>]+>\s*[A-Za-z_]",
    )
    .unwrap();
    let function_regions = files
        .iter()
        .map(|file| (file.path.as_str(), collect_function_regions(file)))
        .collect::<HashMap<_, _>>();
    let local_extents = candidates
        .iter()
        .map(|candidate| {
            function_regions
                .get(candidate.file.as_str())
                .and_then(|functions| {
                    functions
                        .iter()
                        .filter(|function| {
                            function.body_start_line <= candidate.line
                                && candidate.line <= function.body_end_line
                        })
                        .min_by_key(|function| function.body_end_line - function.body_start_line)
                        .map(|function| {
                            (
                                candidate.file.clone(),
                                candidate.line,
                                function.body_end_line,
                            )
                        })
                })
        })
        .collect::<Vec<_>>();
    let mut candidates_by_symbol = HashMap::<String, Vec<usize>>::new();
    for (index, candidate) in candidates.iter().enumerate() {
        if candidate.is_array_like
            && let Some(symbol) = candidate.field_name.as_deref()
        {
            candidates_by_symbol
                .entry(symbol.to_string())
                .or_default()
                .push(index);
        }
    }
    if candidates_by_symbol.is_empty() {
        return;
    }

    for file in files {
        let mut concurrent_lines = concurrent_context_lines(file);
        let locksets = collect_scoped_locksets(file);
        let functions = &function_regions[file.path.as_str()];
        extend_static_helper_execution(file, &mut concurrent_lines);
        let index_origins = collect_index_partition_origins(file, functions);
        let array_declarations = array_declaration_sites(file);
        let internal_linkage = candidates
            .iter()
            .map(|candidate| {
                identifier_tokens(&candidate.snippet)
                    .any(|token| matches!(token, "static" | "LOCAL"))
            })
            .collect::<Vec<_>>();
        let candidate_files = candidates
            .iter()
            .map(|candidate| candidate.file.clone())
            .collect::<Vec<_>>();
        let candidate_lines = candidates
            .iter()
            .map(|candidate| candidate.line)
            .collect::<Vec<_>>();
        let local_shadows = static_access_local_shadows(file);
        let source_lines = file.source.lines().collect::<Vec<_>>();
        let binding_eligible = |index: usize, symbol: &str, line: usize| {
            if local_shadows.get(symbol).is_some_and(|ranges| {
                ranges.iter().any(|(begin, end, declaration)| {
                    *begin < line
                        && line < *end
                        && !(candidate_files[index] == file.path
                            && candidate_lines[index] == *declaration)
                })
            }) && !source_lines
                .get(line.saturating_sub(1))
                .is_some_and(|source| source.contains("::"))
            {
                return false;
            }

            // A file-local global may be referenced from several source files
            // by name in an incomplete/preprocessor-heavy parse. Do not bind
            // such a candidate to a same-named array use from another
            // translation unit; its storage identity is file-local.
            if internal_linkage[index] && candidate_files[index] != file.path {
                return false;
            }
            local_extents[index]
                .as_ref()
                .is_none_or(|(path, begin, end)| {
                    *path == file.path && *begin <= line && line <= *end
                })
                && !functions.iter().any(|function| {
                    function.body_start_line <= line
                        && line <= function.body_end_line
                        && function_parameters(function)
                            .iter()
                            .any(|parameter| parameter == symbol)
                })
        };
        for (offset, line) in file.source.lines().enumerate() {
            let line_no = offset + 1;
            // Pointer/reference accessors are rare. Inspect only identifiers
            // present on a return line instead of testing every candidate
            // symbol against every source line. The indexed access path below
            // already performs symbol-directed lookup.
            let pointer_symbols = if line.trim_start().starts_with("return ")
                && (line.contains(" +") || line.contains('&'))
            {
                identifier_tokens(line).collect::<HashSet<_>>()
            } else {
                HashSet::new()
            };
            for symbol in pointer_symbols {
                let Some(candidate_indices) = candidates_by_symbol.get(symbol) else {
                    continue;
                };
                let candidate_indices = candidate_indices
                    .iter()
                    .copied()
                    .filter(|index| binding_eligible(*index, symbol, line_no))
                    .collect::<Vec<_>>();
                let pointer_selection = token_occurs(line, symbol)
                    && line.trim_start().starts_with("return ")
                    && (line.contains(&format!("{symbol} +"))
                        || line.contains(&format!("&{symbol}[")))
                    && functions
                        .iter()
                        .filter(|function| {
                            function.body_start_line <= line_no && line_no <= function.body_end_line
                        })
                        .min_by_key(|function| function.body_end_line - function.body_start_line)
                        .is_some_and(|function| {
                            let prefix = function.signature.split('(').next().unwrap_or("");
                            // Arithmetic reads and value-returning range builders
                            // are not mutable accessors of the static storage.
                            (prefix.contains('*') || prefix.contains('&'))
                                && !prefix.contains("const ")
                        });
                if !pointer_selection {
                    continue;
                }
                let local = candidate_indices
                    .iter()
                    .copied()
                    .filter(|candidate| candidates[*candidate].file == file.path)
                    .collect::<Vec<_>>();
                let selected = if local.len() == 1 {
                    Some(local[0])
                } else if candidate_indices.len() == 1 {
                    Some(candidate_indices[0])
                } else {
                    None
                };
                if let Some(candidate_index) = selected {
                    let candidate = &mut candidates[candidate_index];
                    candidate.access_file = Some(file.path.clone());
                    candidate.access_line = Some(line_no);
                    candidate.access_kind = Some(CppAccessKind::ReadModifyWrite);
                    candidate.has_partitioned_index_evidence = true;
                    candidate.access_in_concurrent_context = false;
                    candidate.evidence.push(format!(
                        "访问证据: mutable pointer/reference accessor partitions static storage '{}'",
                        symbol
                    ));
                }
            }
            let macro_targets = macro_effects.targets(file, line_no, line);
            if !line.contains('[') && macro_targets.is_empty() {
                continue;
            }
            let line_has_candidate_symbol =
                identifier_tokens(line).any(|token| candidates_by_symbol.contains_key(token));
            let synchronization_targets = [
                "pthread_mutex_lock",
                "pthread_mutex_unlock",
                "pthread_spin_lock",
                "pthread_spin_unlock",
                "mtx_lock",
                "mtx_unlock",
            ]
            .iter()
            .flat_map(|callee| call_argument_lists(line, callee))
            .filter_map(|args| args.into_iter().next())
            .filter_map(|target| indexed_accesses(&target).into_iter().next())
            .filter(|(_, expression)| identifier_tokens(expression).next().is_some())
            .chain(
                macro_targets
                    .iter()
                    .map(|target| (target.storage.clone(), target.index.clone())),
            )
            .collect::<HashSet<_>>();
            let mut accesses = indexed_mutations(line);
            accesses.extend(synchronization_targets.iter().map(|(symbol, expression)| {
                (
                    symbol.clone(),
                    expression.clone(),
                    CppAccessKind::ReadModifyWrite,
                )
            }));
            // A sibling-array finding may use a field as a read-only peer
            // while another array supplies the invalidating write. Preserve
            // indexed reads from macro/API arguments, but let the existing
            // mutation classification win when the same lvalue is updated.
            if line_has_candidate_symbol {
                for (symbol, expression) in indexed_accesses(line) {
                    if !accesses
                        .iter()
                        .any(|(existing, index, _)| existing == &symbol && index == &expression)
                    {
                        accesses.push((symbol, expression, CppAccessKind::Read));
                    }
                }
            }
            for (symbol, expression, access_kind) in accesses {
                if array_declarations.contains(&(line_no, symbol.clone())) {
                    continue;
                }
                let Some(candidate_indices) = candidates_by_symbol.get(symbol.as_str()) else {
                    continue;
                };
                let candidate_indices = candidate_indices
                    .iter()
                    .copied()
                    .filter(|index| binding_eligible(*index, &symbol, line_no))
                    .collect::<Vec<_>>();
                let local = candidate_indices
                    .iter()
                    .copied()
                    .filter(|candidate| candidates[*candidate].file == file.path)
                    .collect::<Vec<_>>();
                let selected = if local.len() == 1 {
                    Some(local[0])
                } else if candidate_indices.len() == 1 {
                    Some(candidate_indices[0])
                } else {
                    None
                };
                let Some(candidate_index) = selected else {
                    continue;
                };
                let semantic_partition = index_origins.supports(&expression, line_no);
                let in_concurrent_context = concurrent_lines.contains(&line_no)
                    || index_origins.supports_runtime_identity(&expression, line_no);
                // Atomic element RMW is a mutable synchronization API even
                // when callers supply metric/bucket IDs rather than CPU IDs.
                // Keep this conditional; it does not prove runtime MHP.
                let atomic_partition_api = access_kind == CppAccessKind::ReadModifyWrite
                    && atomic_element.is_match(&candidates[candidate_index].snippet)
                    && identifier_tokens(&expression).next().is_some();
                let partitioned = synchronization_targets
                    .contains(&(symbol.clone(), expression.clone()))
                    || atomic_partition_api
                    || semantic_partition
                    || (in_concurrent_context && is_parallel_loop_index_expression(&expression));
                let candidate = &mut candidates[candidate_index];
                let replace = candidate.access_kind.as_ref().is_none_or(|existing| {
                    (
                        partitioned || in_concurrent_context,
                        access_kind_strength(&access_kind),
                    ) > (
                        candidate.has_partitioned_index_evidence
                            || candidate.access_in_concurrent_context,
                        access_kind_strength(existing),
                    )
                });
                if replace {
                    candidate.access_file = Some(file.path.clone());
                    candidate.access_line = Some(line_no);
                    candidate.access_index = Some(expression.clone());
                    candidate.access_function = functions
                        .iter()
                        .filter(|function| {
                            function.body_start_line <= line_no && line_no <= function.body_end_line
                        })
                        .min_by_key(|function| function.body_end_line - function.body_start_line)
                        .map(|function| function.name.clone());
                    candidate.access_kind = Some(access_kind.clone());
                    candidate.access_in_concurrent_context = in_concurrent_context;
                    candidate.has_partitioned_index_evidence = partitioned;
                    candidate.guard_ids = locksets.get(&line_no).cloned().unwrap_or_default();
                    candidate.evidence.extend(
                        macro_targets
                            .iter()
                            .filter(|target| target.storage == symbol && target.index == expression)
                            .map(|target| target.evidence.clone()),
                    );
                    let operation = match access_kind {
                        CppAccessKind::Read => "发生读取",
                        CppAccessKind::Write | CppAccessKind::ReadModifyWrite => "发生写入",
                    };
                    candidate.evidence.push(format!(
                        "访问证据: static array '{}' 在索引 '{}' 上{}；{}",
                        symbol,
                        expression,
                        operation,
                        if in_concurrent_context {
                            "存在并发上下文或运行时分区来源"
                        } else if partitioned {
                            "条件分区/同步 API，尚未证明具体调用者同时执行"
                        } else {
                            "仅定位访问，尚无并发或分区来源"
                        }
                    ));
                }
            }
        }
    }
}

/// Preserve execution provenance through unambiguous, file-local free-function
/// calls. This is a may-execute fact, not a claim that API parameters are worker
/// identities. Do not cross receiver dispatch or deferred callable boundaries.
/// Seed only loop-contained calls; propagate that repetition through helpers,
/// without borrowing a thread's entire lifetime for one-shot setup/exit calls.
fn extend_static_helper_execution(file: &ParsedCppFile, concurrent: &mut HashSet<usize>) {
    let Some(tree) = &file.tree else { return };
    let mut definitions = HashMap::<String, Vec<Option<(usize, usize)>>>::new();
    let mut calls = Vec::new();
    let mut shadowed = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() == "declaration" {
            for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
                if declarator.kind() != "function_declarator"
                    && let Some(name) = declarator_variable_name(declarator, &file.source)
                {
                    shadowed.insert(name);
                }
            }
        }
        if matches!(node.kind(), "init_declarator" | "parameter_declaration")
            && let Some(declarator) = node.child_by_field_name("declarator")
            && let Some(name) = declarator_variable_name(declarator, &file.source)
        {
            shadowed.insert(name);
        }
        if node.kind() == "call_expression"
            && let Some(callee) = node.child_by_field_name("function")
            && callee.kind() == "identifier"
        {
            let mut ancestor = node.parent();
            let mut deferred = false;
            let mut repeated = false;
            while let Some(parent) = ancestor {
                deferred |= matches!(
                    parent.kind(),
                    "lambda_expression" | "class_specifier" | "struct_specifier"
                );
                repeated |= matches!(
                    parent.kind(),
                    "for_statement" | "for_range_loop" | "while_statement" | "do_statement"
                );
                ancestor = parent.parent();
            }
            if !deferred {
                calls.push((
                    node.start_position().row + 1,
                    node_text(callee, &file.source).to_owned(),
                    repeated,
                ));
            }
        }
        if node.kind() != "function_definition" {
            return;
        }
        let Some(declarator) = node.child_by_field_name("declarator") else {
            return;
        };
        let mut declarator = declarator;
        while declarator.kind() != "function_declarator" {
            let Some(inner) = declarator.child_by_field_name("declarator") else {
                return;
            };
            declarator = inner;
        }
        let Some(name) = declarator
            .child_by_field_name("declarator")
            .filter(|name| name.kind() == "identifier")
        else {
            return;
        };
        let Some(body) = node.child_by_field_name("body") else {
            return;
        };
        let mut deferred = false;
        walk_nodes(body, &mut |child| {
            deferred |= matches!(
                child.kind(),
                "lambda_expression" | "class_specifier" | "struct_specifier"
            );
        });
        let file_local = node
            .parent()
            .is_some_and(|parent| parent.kind() == "translation_unit")
            && node.named_children(&mut node.walk()).any(|child| {
                child.kind() == "storage_class_specifier"
                    && node_text(child, &file.source) == "static"
            });
        definitions
            .entry(node_text(name, &file.source).to_owned())
            .or_default()
            .push(
                (file_local && !body.has_error() && !deferred)
                    .then_some((body.start_position().row + 1, body.end_position().row + 1)),
            );
    });
    let mut repeated_helpers = HashSet::new();
    for _ in 0..4 {
        let mut added = HashSet::new();
        for (line, name, repeated) in &calls {
            if !concurrent.contains(line)
                || shadowed.contains(name)
                || (!repeated && !repeated_helpers.contains(line))
            {
                continue;
            }
            if let Some(definitions) = definitions.get(name)
                && let [Some((start, end))] = definitions.as_slice()
            {
                added.extend(*start..=*end);
            }
        }
        let before = repeated_helpers.len();
        repeated_helpers.extend(added.iter().copied());
        concurrent.extend(added);
        if repeated_helpers.len() == before {
            break;
        }
    }
}

fn is_parallel_loop_index_expression(expression: &str) -> bool {
    let tokens = identifier_tokens(expression).collect::<HashSet<_>>();
    tokens.iter().any(|token| {
        matches!(
            *token,
            "i" | "j" | "k" | "idx" | "index" | "slot" | "worker"
        )
    })
}

fn access_kind_strength(kind: &CppAccessKind) -> u8 {
    match kind {
        CppAccessKind::Read => 0,
        CppAccessKind::Write => 1,
        CppAccessKind::ReadModifyWrite => 2,
    }
}

fn is_comment_only_line(line: &str) -> bool {
    let trimmed = line.trim_start();
    trimmed.starts_with("//")
        || trimmed.starts_with("/*")
        || trimmed.starts_with('*')
        || trimmed.starts_with("*/")
}

fn static_candidate_is_protected(line: &str, cache_line_size: usize) -> bool {
    extract_align_bytes(line).is_some_and(|bytes| bytes >= cache_line_size)
}

fn update_scope_stack(line: &str, scopes: &mut Vec<bool>) {
    let bytes = line.as_bytes();
    for (offset, byte) in bytes.iter().enumerate() {
        match byte {
            b'}' => {
                scopes.pop();
            }
            b'{' => {
                let prefix = line[..offset].trim_start();
                let parent_is_namespace = scopes.iter().all(|is_namespace| *is_namespace);
                let is_namespace = parent_is_namespace
                    && (prefix.starts_with("namespace ")
                        || prefix == "namespace"
                        || prefix.starts_with("inline namespace ")
                        || prefix.starts_with("extern \"C\""));
                scopes.push(is_namespace);
            }
            _ => {}
        }
    }
}

fn extract_static_candidate_name(line_text: &str) -> Option<String> {
    let prefix = line_text
        .split('=')
        .next()
        .unwrap_or(line_text)
        .split('{')
        .next()
        .unwrap_or(line_text)
        .split(';')
        .next()
        .unwrap_or(line_text)
        .trim();
    let before_array = prefix.split('[').next().unwrap_or(prefix).trim();
    let tail = before_array
        .rsplit("::")
        .next()
        .unwrap_or(before_array)
        .trim();
    let token = tail
        .split_whitespace()
        .last()?
        .trim()
        .trim_matches('*')
        .trim_matches('&');
    let is_ident = token
        .chars()
        .next()
        .is_some_and(|ch| ch == '_' || ch.is_ascii_alphabetic())
        && token
            .chars()
            .all(|ch| ch == '_' || ch.is_ascii_alphanumeric());
    is_ident.then(|| token.to_string())
}

fn collect_api_evidence_for_struct(
    record_idx: usize,
    record: &CppStructInfo,
    evidence: &mut [CppEvidenceSet],
) {
    if !record.visibility.is_externally_exposed() {
        return;
    }

    evidence[record_idx].push_api_item(CppApiEvidence {
        description: format!(
            "API exposure: C++ {} '{}' is externally constructible or visible",
            match record.kind {
                super::types::CppRecordKind::Struct => "struct",
                super::types::CppRecordKind::Class => "class",
            },
            record.qualified_name
        ),
        file: record.file.clone(),
        line: record.line,
        score: 0.20,
    });

    if !record.public_fields.is_empty() {
        evidence[record_idx].push_api_item(CppApiEvidence {
            description: format!(
                "API exposure: public fields on '{}': {}",
                record.name,
                record.public_fields.join(", ")
            ),
            file: record.file.clone(),
            line: record.line,
            score: 0.25,
        });
    }

    for method in &record.public_methods {
        if method_name_suggests_hot_use(method) {
            evidence[record_idx].push_api_item(CppApiEvidence {
                description: format!(
                    "API usage hint: public method '{}::{}' suggests hot/concurrent use",
                    record.name, method
                ),
                file: record.file.clone(),
                line: record.line,
                score: 0.55,
            });
        }
    }

    if semantic_name_suggests_hot_use(&record.name)
        || record
            .fields
            .iter()
            .any(|field| semantic_name_suggests_hot_use(&field.name))
    {
        evidence[record_idx].push_api_item(CppApiEvidence {
            description: format!(
                "API semantic hint: '{}' or its fields look like hot runtime state",
                record.name
            ),
            file: record.file.clone(),
            line: record.line,
            score: 0.35,
        });
    }
}

fn collect_type_usage_evidence(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    evidence: &mut [CppEvidenceSet],
) {
    for (idx, raw_line) in file.source.lines().enumerate() {
        let line = raw_line.trim();
        if !looks_like_signature_or_reference(line) {
            continue;
        }
        if !(method_name_suggests_hot_use(line)
            || line.contains("shared_ptr")
            || line.contains('&'))
        {
            continue;
        }
        for token in identifier_tokens(line) {
            let Some(record_idx) = index.unambiguous_record_index(token, &file.path) else {
                continue;
            };
            let record = index.record(record_idx);
            if record.file == file.path || !signature_type_matches_scope(file, idx + 1, record) {
                continue;
            }
            evidence[record_idx].push_api_item(CppApiEvidence {
                description: format!(
                    "API usage hint: signature/reference mentions '{}' at {}:{}",
                    record.name,
                    file.path,
                    idx + 1
                ),
                file: file.path.clone(),
                line: idx + 1,
                score: 0.45,
            });
        }
    }
}

/// A short type name in a signature must be reachable by ordinary lexical
/// lookup. Directory proximity cannot make a nested record visible in another
/// namespace. Unresolved using/alias lookup does not supply this API proof.
fn signature_type_matches_scope(file: &ParsedCppFile, line: usize, record: &CppStructInfo) -> bool {
    let Some(tree) = &file.tree else { return false };
    let Some(text) = file.source.lines().nth(line - 1) else {
        return false;
    };
    static QUALIFIED_NAME: std::sync::LazyLock<Regex> = std::sync::LazyLock::new(|| {
        Regex::new(r"(?:::)?[A-Za-z_]\w*(?:\s*::\s*[A-Za-z_]\w*)*").unwrap()
    });
    let line_start = file
        .source
        .split_inclusive('\n')
        .take(line - 1)
        .map(str::len)
        .sum::<usize>();
    for matched in QUALIFIED_NAME.find_iter(text) {
        let name = matched.as_str().split_whitespace().collect::<String>();
        if name.rsplit("::").next() != Some(record.name.as_str()) {
            continue;
        }
        let start = line_start + matched.start();
        let Some(usage) = tree
            .root_node()
            .descendant_for_byte_range(start, line_start + matched.end())
        else {
            continue;
        };
        let mut type_name = usage;
        while type_name.kind() == "qualified_identifier" {
            let Some(name) = type_name.child_by_field_name("name") else {
                break;
            };
            type_name = name;
        }
        if type_name.kind() != "type_identifier" {
            continue;
        }
        let mut scopes = Vec::new();
        let mut ancestor = usage.parent();
        while let Some(node) = ancestor {
            if matches!(
                node.kind(),
                "namespace_definition" | "class_specifier" | "struct_specifier" | "union_specifier"
            ) && let Some(name) = node.child_by_field_name("name")
            {
                scopes.push(
                    node_text(name, &file.source)
                        .split_whitespace()
                        .collect::<String>(),
                );
            }
            ancestor = node.parent();
        }
        scopes.reverse();
        if let Some(absolute) = name.strip_prefix("::") {
            if absolute == record.qualified_name {
                return true;
            }
            continue;
        }
        for end in (0..=scopes.len()).rev() {
            let candidate = if end == 0 {
                name.to_owned()
            } else {
                format!("{}::{name}", scopes[..end].join("::"))
            };
            if candidate == record.qualified_name {
                return true;
            }
        }
    }
    false
}

fn collect_field_access_evidence(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    context: &FieldAccessContext<'_>,
    evidence: &mut [CppEvidenceSet],
    syntax_accesses: HashMap<usize, Vec<field_access::SyntaxAccess>>,
) -> HashMap<usize, Vec<field_access::SyntaxAccess>> {
    let functions = collect_function_regions(file);
    let index_origins = collect_index_partition_origins(file, &functions);
    // Bounded configuration alternatives, not macro expansion. An #else
    // assignment does not execute after the first arm in the same build.
    let mut conditional_origins = Vec::new();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if conditional_origins.len() >= 16
                || !matches!(node.kind(), "preproc_if" | "preproc_ifdef")
            {
                return;
            }
            let Some(alternative) = node.child_by_field_name("alternative") else {
                return;
            };
            let start = node.start_position().row + 1;
            let split = alternative.start_position().row + 1;
            let end = node.end_position().row + 1;
            if !index_origins.assignments.iter().any(|(line, _, rhs)| {
                start < *line && *line < split && is_thread_index_expression(rhs)
            }) {
                return;
            }
            let mut selected = index_origins.clone();
            selected
                .assignments
                .retain(|(line, _, _)| *line < split || *line >= end);
            conditional_origins.push((start, split, end, selected));
        });
    }
    let mut loop_scopes: Vec<i32> = Vec::new();
    let mut brace_depth = 0i32;

    for (idx, raw_line) in file.source.lines().enumerate() {
        while loop_scopes
            .last()
            .is_some_and(|loop_depth| brace_depth < *loop_depth)
        {
            loop_scopes.pop();
        }
        let line_no = idx + 1;
        let line = raw_line.trim();
        let function_name = enclosing_function_name(&functions, line_no);
        if omp_thread_work_directive(line)
            || line.contains("std::thread")
            || line.contains("pthread_create")
            || line.contains("std::async")
            || line.contains("parallel_for")
            || line.contains("parallel_reduce")
        {
            add_record_wide_concurrency(
                file,
                index,
                context.variable_types,
                line_no,
                line,
                evidence,
            );
        }
        let starts_loop = line.contains("for ")
            || line.contains("for(")
            || line.contains("while ")
            || line.contains("while(");
        if starts_loop && raw_line.contains('{') {
            let loop_scope = brace_depth + raw_line.matches('{').count() as i32;
            loop_scopes.push(loop_scope);
        }

        let in_concurrent_context = context.concurrent_lines.contains(&line_no);
        let is_declaration = context.declaration_lines.contains(&line_no)
            || line.starts_with("using ")
            || line.starts_with("typedef ")
            || line.starts_with("#define ");
        if !is_declaration || syntax_accesses.contains_key(&line_no) {
            let fallback_mentions = mentioned_fields_in_line(
                line,
                index,
                context.variable_types,
                context.implicit_records.get(&line_no).copied(),
                &file.path,
            );
            let fallback_accesses = fallback_mentions
                .into_iter()
                .filter_map(|(record, field)| {
                    classify_field_access(line, field).map(|kind| field_access::SyntaxAccess {
                        needs_line_fallback: false,
                        element_member_path: Vec::new(),
                        record,
                        field: field.to_string(),
                        kind,
                        start_byte: 0,
                        // Recovered syntax cannot attribute an operation on
                        // another expression to this field. Retain only typed
                        // inline atomic evidence in the fallback.
                        atomic: index.record(record).fields.iter().any(|info| {
                            info.name == field
                                && info.is_atomic
                                && !field_access::without_template_arguments(&info.ty_str)
                                    .contains(['*', '&'])
                        }),
                        receiver: field_access_tokens(line)
                            .into_iter()
                            .find_map(|(receiver, name)| {
                                (name == field).then_some(receiver).flatten()
                            })
                            .map(ToOwned::to_owned),
                        raw_pointer: line.contains("->"),
                        initialization: function_name
                            .as_deref()
                            .is_some_and(|name| is_record_constructor(name, index.record(record))),
                        function: function_name.clone(),
                        loop_depth: None,
                        // Spelling-only recovery cannot bind the constructor
                        // owner, especially across same-named record scopes.
                        in_record_constructor: false,
                        // A spelling-only fallback cannot prove that this use
                        // names a particular TLS or nonescaping declaration.
                        thread_local: false,
                        nonescaping_local: false,
                        automatic_receiver: false,
                        contiguous_element: false,
                        element_index: None,
                    })
                })
                .collect::<Vec<_>>();
            let known = syntax_accesses.get(&line_no);
            let merged = known
                .filter(|accesses| accesses.iter().any(|access| access.needs_line_fallback))
                .map(|accesses| {
                    let mut merged = accesses.clone();
                    // A bound receiver/member occurrence already supplies
                    // its precise owner, mutation and initialization facts.
                    // Do not replace it with a row-wide lexical guess merely
                    // because another operand could not be resolved.
                    merged.extend(
                        fallback_accesses
                            .iter()
                            .filter(|fallback| {
                                !accesses.iter().any(|resolved| {
                                    resolved.field == fallback.field
                                        && resolved.receiver == fallback.receiver
                                })
                            })
                            .cloned(),
                    );
                    merged
                });
            let accesses = merged.as_ref().or(known).unwrap_or(&fallback_accesses);
            let active_loop_depth =
                loop_scopes.len() + usize::from(starts_loop && !raw_line.contains('{'));
            let hotness = if active_loop_depth > 0 {
                (active_loop_depth as f32).powi(2)
                    * if line.contains("1000") || line.contains("size()") {
                        8.0
                    } else {
                        6.0
                    }
            } else {
                1.0
            };
            for access in accesses {
                let in_concurrent_context = in_concurrent_context
                    || access.element_index.as_deref().is_some_and(|expression| {
                        index_origins.supports_runtime_identity(expression, line_no)
                            || conditional_origins
                                .iter()
                                .any(|(start, split, end, selected)| {
                                    line_no > *start
                                        && (line_no < *split || line_no >= *end)
                                        && selected.supports_runtime_identity(expression, line_no)
                                })
                    });
                let hotness = access.loop_depth.map_or(hotness, |depth| {
                    if depth == 0 {
                        1.0
                    } else {
                        6.0 * (depth as f32).powi(2)
                    }
                });
                let record_idx = access.record;
                let field = access.field.as_str();
                let access_kind = access.kind.clone();
                let kind = if access.contiguous_element {
                    CppEvidenceKind::ContiguousElementAccess
                } else if access.atomic {
                    CppEvidenceKind::AtomicFieldOps
                } else if in_concurrent_context {
                    CppEvidenceKind::ConcurrentFieldAccess
                } else {
                    CppEvidenceKind::HotScalarWrite
                };
                let record = index.record(record_idx);
                evidence[record_idx].push_item(CppEvidenceItem {
                    element_member_path: access.element_member_path.clone(),
                    concurrent_call_path: context
                        .concurrent_call_paths
                        .get(&line_no)
                        .cloned()
                        .unwrap_or_default(),
                    kind,
                    access_kind: Some(access_kind.clone()),
                    field_name: Some(field.to_string()),
                    hotness_score: hotness,
                    in_concurrent_context,
                    through_shared_indirection: access.receiver.as_ref().is_some_and(|receiver| {
                        context.shared_reachable_variables.contains(receiver)
                    }),
                    through_raw_pointer: access.raw_pointer,
                    through_thread_local: access.thread_local,
                    through_nonescaping_local: access.nonescaping_local,
                    through_automatic_receiver: access.automatic_receiver,
                    guard_ids: context
                        .locksets_by_line
                        .get(&line_no)
                        .cloned()
                        .unwrap_or_default(),
                    initialization_phase: access.initialization,
                    in_record_constructor: access.in_record_constructor,
                    function_name: access.function.clone().or_else(|| function_name.clone()),
                    description: format!(
                        "C++ field access '{}' on '{}.{}' at {}:{}",
                        line, record.name, field, file.path, line_no
                    ),
                    file: file.path.clone(),
                    line: line_no,
                });
                if hotness >= 5.0 && !access.contiguous_element {
                    evidence[record_idx].push_item(CppEvidenceItem {
                        element_member_path: Vec::new(),
                        concurrent_call_path: context
                            .concurrent_call_paths
                            .get(&line_no)
                            .cloned()
                            .unwrap_or_default(),
                        kind: CppEvidenceKind::LoopHotness,
                        access_kind: Some(access_kind.clone()),
                        field_name: Some(field.to_string()),
                        hotness_score: hotness,
                        in_concurrent_context,
                        through_shared_indirection: access.receiver.as_ref().is_some_and(
                            |receiver| context.shared_reachable_variables.contains(receiver),
                        ),
                        through_raw_pointer: access.raw_pointer,
                        through_thread_local: access.thread_local,
                        through_nonescaping_local: access.nonescaping_local,
                        through_automatic_receiver: access.automatic_receiver,
                        guard_ids: context
                            .locksets_by_line
                            .get(&line_no)
                            .cloned()
                            .unwrap_or_default(),
                        initialization_phase: access.initialization,
                        in_record_constructor: access.in_record_constructor,
                        function_name: access.function.clone().or_else(|| function_name.clone()),
                        description: format!(
                            "loop hotness {:.1} around '{}.{}' at {}:{}",
                            hotness, record.name, field, file.path, line_no
                        ),
                        file: file.path.clone(),
                        line: line_no,
                    });
                }
            }
        }

        if line.contains(".lock()")
            || line.contains("lock_guard")
            || line.contains("unique_lock")
            || line.contains("scoped_lock")
        {
            // The syntax collector already binds RAII arguments to their
            // receiver and lexical owner, including shadowing and guard modes.
            // A neighbouring record with the same member name is not a write
            // target. Keep this fallback non-access evidence only.
            for record_idx in identifier_tokens(line)
                .filter_map(|token| index.unambiguous_record_index(token, &file.path))
            {
                let record = index.record(record_idx);
                evidence[record_idx].push_item(CppEvidenceItem {
                    element_member_path: Vec::new(),
                    concurrent_call_path: context
                        .concurrent_call_paths
                        .get(&line_no)
                        .cloned()
                        .unwrap_or_default(),
                    kind: CppEvidenceKind::LockProtected,
                    access_kind: None,
                    field_name: None,
                    hotness_score: 1.0,
                    in_concurrent_context,
                    through_shared_indirection: false,
                    through_raw_pointer: false,
                    through_thread_local: false,
                    through_nonescaping_local: false,
                    through_automatic_receiver: false,
                    guard_ids: Vec::new(),
                    initialization_phase: false,
                    in_record_constructor: false,
                    function_name: function_name.clone(),
                    description: format!(
                        "lock evidence near '{}' at {}:{}",
                        record.name, file.path, line_no
                    ),
                    file: file.path.clone(),
                    line: line_no,
                });
            }
        }

        brace_depth += raw_line.matches('{').count() as i32;
        brace_depth -= raw_line.matches('}').count() as i32;
    }
    syntax_accesses
}

fn collect_shared_ownership_evidence(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    concurrent_lines: &HashSet<usize>,
    evidence: &mut [CppEvidenceSet],
) -> HashSet<String> {
    #[derive(Debug)]
    struct SharedDeclaration<'a> {
        line_no: usize,
        end_line: usize,
        record_idx: usize,
        scope: &'a str,
        scope_line: usize,
        symbol: Option<String>,
        function_local: bool,
    }

    let mut shared_reachable_variables = HashSet::new();
    if !file.source.contains("shared_ptr") && !file.source.contains("make_shared") {
        return shared_reachable_variables;
    }
    let mut declarations = Vec::new();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(
                node.kind(),
                "declaration"
                    | "field_declaration"
                    | "parameter_declaration"
                    | "function_definition"
            ) {
                return;
            }
            let declared_owner = node
                .child_by_field_name("type")
                .and_then(|ty| shared_owner_record(node_text(ty, &file.source), "shared_ptr"))
                .and_then(|name| index.unambiguous_record_index(&name, &file.path));
            let mut ancestor = node.parent();
            let mut function = None;
            while let Some(parent) = ancestor {
                if parent.kind() == "function_definition" {
                    function = Some(parent);
                    break;
                }
                ancestor = parent.parent();
            }
            let function_local = function.is_some()
                && node.kind() != "parameter_declaration"
                && !node_text(node, &file.source)
                    .trim_start()
                    .starts_with("static ");
            let scope = function
                .map(|function| node_text(function, &file.source))
                .unwrap_or(&file.source);
            let mut cursor = node.walk();
            for declarator in node.children_by_field_name("declarator", &mut cursor) {
                // The initializer must itself create the shared owner. A call
                // receiving make_shared<T>() may return an unrelated type.
                let initialized_owner = declarator
                    .child_by_field_name("value")
                    .filter(|value| value.kind() == "call_expression")
                    .and_then(|value| value.child_by_field_name("function"))
                    .and_then(|callee| {
                        shared_owner_record(node_text(callee, &file.source), "make_shared")
                    })
                    .and_then(|name| index.unambiguous_record_index(&name, &file.path));
                let Some(record_idx) = declared_owner.or(initialized_owner) else {
                    continue;
                };
                declarations.push(SharedDeclaration {
                    line_no: node.start_position().row + 1,
                    end_line: node.end_position().row + 1,
                    record_idx,
                    scope,
                    scope_line: function.map_or(1, |function| function.start_position().row + 1),
                    symbol: declarator_variable_name(declarator, &file.source),
                    function_local,
                });
            }
        });
    } else {
        // A parser failure cannot justify non-escape. Recover only the actual
        // pointee type, never every record token from a mixed signature.
        for (offset, line) in file.source.lines().enumerate() {
            for owner in ["shared_ptr", "make_shared"] {
                let Some(start) = line.find(owner) else {
                    continue;
                };
                let Some(record_idx) = shared_owner_record(&line[start..], owner)
                    .and_then(|name| index.unambiguous_record_index(&name, &file.path))
                else {
                    continue;
                };
                declarations.push(SharedDeclaration {
                    line_no: offset + 1,
                    end_line: offset + 1,
                    record_idx,
                    scope: &file.source,
                    scope_line: 1,
                    symbol: None,
                    function_local: false,
                });
            }
        }
    }

    for declaration in declarations {
        let reaches_outside_local_scope = !declaration.function_local
            || declaration.symbol.as_ref().is_some_and(|symbol| {
                declaration.scope.lines().enumerate().any(|(offset, line)| {
                    let line_no = declaration.scope_line + offset;
                    !(declaration.line_no..=declaration.end_line).contains(&line_no)
                        && symbol_may_escape_line(line, symbol)
                })
            });
        if !reaches_outside_local_scope {
            continue;
        }
        if let Some(symbol) = &declaration.symbol {
            shared_reachable_variables.insert(symbol.clone());
        }
        let record = index.record(declaration.record_idx);
        evidence[declaration.record_idx].push_item(CppEvidenceItem {
            element_member_path: Vec::new(),
            concurrent_call_path: Vec::new(),
            kind: CppEvidenceKind::SharedOwnership,
            access_kind: None,
            field_name: None,
            hotness_score: 1.0,
            in_concurrent_context: concurrent_lines.contains(&declaration.line_no),
            through_shared_indirection: true,
            through_raw_pointer: false,
            through_thread_local: false,
            through_nonescaping_local: false,
            through_automatic_receiver: false,
            guard_ids: Vec::new(),
            initialization_phase: false,
            in_record_constructor: false,
            function_name: None,
            description: format!(
                "std::shared_ptr shares '{}' at {}:{}",
                record.name, file.path, declaration.line_no
            ),
            file: file.path.clone(),
            line: declaration.line_no,
        });
    }
    shared_reachable_variables
}

/// Bind the direct pointee of a shared-owner declaration or factory. Nested
/// template arguments, return types and neighboring parameters are not owners
/// merely because they occur on the same source line.
fn shared_owner_record(type_text: &str, owner: &str) -> Option<String> {
    let (head, arguments) = type_text.split_once('<')?;
    if head.trim().rsplit("::").next()?.trim() != owner {
        return None;
    }
    let mut depth = 0usize;
    let mut end = None;
    for (offset, ch) in arguments.char_indices() {
        match ch {
            '<' => depth += 1,
            '>' if depth == 0 => {
                end = Some(offset);
                break;
            }
            '>' => depth -= 1,
            ',' if depth == 0 => {
                end = Some(offset);
                break;
            }
            _ => {}
        }
    }
    let pointee = arguments[..end?].trim();
    if pointee.contains('*') || pointee.contains('[') || pointee.contains('&') {
        return None;
    }
    let base = pointee.split('<').next()?.trim();
    Some(clean_type_name(base))
}

fn collect_object_storage_evidence(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    evidence: &mut [CppEvidenceSet],
) {
    let functions = collect_function_regions(file);
    let mut aliases = file
        .source
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            let tail = line.strip_prefix("using ")?;
            let (alias, target) = tail.split_once('=')?;
            let alias = identifier_tokens(alias).last()?.to_string();
            if field_access::without_template_arguments(target).contains(['*', '&']) {
                return None;
            }
            // Alias the outer value type, not a nested pointee or container
            // element (using P = unique_ptr<T> does not make P an inline T).
            let target = clean_type_name(&field_access::without_template_arguments(
                target.trim().trim_end_matches(';'),
            ));
            index.record_indices_for_name(&target)?;
            Some((alias, target))
        })
        .collect::<HashMap<_, _>>();
    // A container alias names a layout; it does not allocate any elements.
    // Resolve alias chains separately so only a later storage use contributes
    // adjacency evidence. Do not borrow writes merely from a type definition.
    let mut container_alias_targets = Vec::new();
    let mut storage_source = file.source.as_bytes().to_vec();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            let name_field = match node.kind() {
                "alias_declaration" => "name",
                "type_definition" => "declarator",
                _ => return,
            };
            // Mask the entire syntax node, retaining line numbers and any
            // subsequent declaration. This also handles multiline aliases.
            for byte in &mut storage_source[node.byte_range()] {
                if !matches!(*byte, b'\n' | b'\r') {
                    *byte = b' ';
                }
            }
            let (Some(name), Some(target)) = (
                node.child_by_field_name(name_field),
                node.child_by_field_name("type"),
            ) else {
                return;
            };
            let name = node_text(name, &file.source).trim();
            if !identifier_tokens(name).eq(std::iter::once(name)) {
                return;
            }
            container_alias_targets.push((
                name.to_owned(),
                node_text(target, &file.source).trim().to_owned(),
            ));
        });
    }
    // This collector has no cross-scope alias identity yet. An ambiguous
    // spelling cannot prove a particular element type in another scope.
    let mut alias_counts = HashMap::new();
    for (name, _) in &container_alias_targets {
        *alias_counts.entry(name.clone()).or_insert(0usize) += 1;
    }
    container_alias_targets.retain(|(name, _)| alias_counts.get(name) == Some(&1));
    for (name, target) in &container_alias_targets {
        let outer = field_access::without_template_arguments(target);
        let record_name = clean_type_name(&outer);
        if !outer.contains(['*', '&']) && index.record_indices_for_name(&record_name).is_some() {
            aliases.insert(name.clone(), record_name);
        }
    }
    let mut container_aliases: HashMap<String, Vec<usize>> = HashMap::new();
    for _ in 0..container_alias_targets.len() {
        let mut changed = false;
        for (alias, target) in &container_alias_targets {
            if container_aliases.contains_key(alias) {
                continue;
            }
            let compact = target.replace(char::is_whitespace, "");
            let mut targets = container_aliases.get(target).cloned().unwrap_or_default();
            let outer = field_access::without_template_arguments(&compact);
            if matches!(
                clean_type_name(&outer).as_str(),
                "vector" | "array" | "FixedArray"
            ) && !outer.contains(['*', '&'])
                && let Some(element) = field_access::first_template_argument(&compact)
            {
                let element = field_access::without_template_arguments(element);
                let name = clean_type_name(&element);
                let name = name.as_str();
                let record_name = aliases.get(name).map(String::as_str).unwrap_or(name);
                if !element.contains(['*', '&'])
                    && let Some(record_idx) =
                        index.unambiguous_record_index(record_name, &file.path)
                {
                    targets.push(record_idx);
                }
            }
            targets.sort_unstable();
            targets.dedup();
            if !targets.is_empty() {
                container_aliases.insert(alias.clone(), targets);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut alias_storage_uses = HashSet::new();
    let mut private_storage_lines: HashMap<usize, bool> = HashMap::new();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(node.kind(), "declaration" | "field_declaration") {
                return;
            }
            let Some(type_node) = node.child_by_field_name("type") else {
                return;
            };
            let alias = node_text(type_node, &file.source).trim();
            let declaration = node_text(node, &file.source);
            // Only scan a callable's uses for declarations that can supply
            // contiguous storage, not every scalar local in large functions.
            let storage_shape = container_aliases.contains_key(alias)
                || alias.contains("vector<")
                || alias.contains("array<")
                || alias.contains("FixedArray<")
                || declaration.contains('[');
            let private =
                storage_shape && field_access::storage_declaration_is_private(node, &file.source);
            for line in node.start_position().row + 1..=node.end_position().row + 1 {
                private_storage_lines
                    .entry(line)
                    .and_modify(|value| *value &= private)
                    .or_insert(private);
            }
            if !container_aliases.contains_key(alias) {
                return;
            }
            let mut cursor = node.walk();
            for mut declarator in node.children_by_field_name("declarator", &mut cursor) {
                if declarator.kind() == "init_declarator" {
                    let Some(inner) = declarator.child_by_field_name("declarator") else {
                        continue;
                    };
                    declarator = inner;
                }
                // Pointer/reference declarations and function return types do
                // not establish adjacent element storage.
                if matches!(
                    declarator.kind(),
                    "identifier" | "field_identifier" | "array_declarator"
                ) {
                    alias_storage_uses
                        .insert((type_node.start_position().row + 1, alias.to_owned()));
                }
            }
        });
    }
    // Replacing complete node byte ranges with ASCII whitespace preserves
    // UTF-8 outside those ranges, including source locations.
    let storage_source = String::from_utf8(storage_source).expect("masked C++ source is UTF-8");
    let mut inert_construction = HashMap::new();
    for (idx, raw_line) in storage_source.lines().enumerate() {
        let line = raw_line.trim();
        if line.starts_with("struct ")
            || line.starts_with("class ")
            || line.starts_with("enum ")
            || is_comment_only_line(line)
        {
            continue;
        }
        let compact = line.replace(char::is_whitespace, "");
        let names = identifier_tokens(line).collect::<Vec<_>>();
        let storage_names = names
            .iter()
            .filter(|name| alias_storage_uses.contains(&(idx + 1, name.to_string())))
            .flat_map(|name| {
                container_aliases
                    .get(*name)
                    .into_iter()
                    .flatten()
                    .map(|&record_idx| (*name, record_idx))
            });
        let direct_names = names.iter().filter_map(|&name| {
            let record_name = aliases.get(name).map(String::as_str).unwrap_or(name);
            index
                .unambiguous_record_index(record_name, &file.path)
                .map(|record_idx| (name, record_idx))
        });
        for (name, record_idx) in direct_names.chain(storage_names) {
            let contiguous = container_aliases.contains_key(name)
                || container_stores_inline_record(&compact, name)
                || compact.contains(&format!("{name}[]"))
                || compact.contains(&format!("new{name}["))
                || declaration_has_array_of(&compact, name);
            let allocator = compact.contains(&format!("new{name}"))
                || compact.contains(&format!("make_unique<{name}"))
                || compact.contains(&format!("make_shared<{name}"))
                || compact.contains(&format!("malloc(sizeof({name})"))
                || compact.contains(&format!("calloc(1,sizeof({name})"))
                || (compact.contains("aligned_alloc(")
                    && compact.contains(&format!("sizeof({name})")));
            let kind = if contiguous {
                Some(CppEvidenceKind::ContiguousObjectStorage)
            } else if allocator {
                Some(CppEvidenceKind::AllocatorObjectStorage)
            } else {
                None
            };
            let Some(kind) = kind else {
                continue;
            };
            let record = index.record(record_idx);
            evidence[record_idx].push_item(CppEvidenceItem {
                element_member_path: Vec::new(),
                concurrent_call_path: Vec::new(),
                kind,
                access_kind: None,
                field_name: None,
                hotness_score: 1.0,
                in_concurrent_context: false,
                through_shared_indirection: false,
                through_raw_pointer: false,
                through_thread_local: false,
                through_automatic_receiver: false,
                through_nonescaping_local: contiguous
                    && private_storage_lines.get(&(idx + 1)) == Some(&true)
                    && *inert_construction.entry(record_idx).or_insert_with(|| {
                        field_access::record_construction_is_inert(file, record)
                    }),
                guard_ids: Vec::new(),
                initialization_phase: false,
                in_record_constructor: false,
                function_name: enclosing_function_name(&functions, idx + 1),
                description: format!(
                    "C++ object storage for '{}' at {}:{}: {}{}",
                    record.name,
                    file.path,
                    idx + 1,
                    line,
                    if compact.contains("aligned_alloc(")
                        && compact.contains(&format!(",sizeof({name}))"))
                        && record
                            .total_estimated_size
                            .is_some_and(|size| { size > 0 && size % record.cache_line_size != 0 })
                    {
                        // A raw sizeof argument is not proof of an unrounded
                        // size: complete objects can already occupy whole
                        // cache lines. Unknown symbolic extents cannot supply
                        // the missing remainder through placeholder offsets.
                        " [unrounded aligned_alloc size]"
                    } else {
                        ""
                    }
                ),
                file: file.path.clone(),
                line: idx + 1,
            });
        }
    }
}

fn declaration_has_array_of(compact: &str, record: &str) -> bool {
    let Some(record_offset) = compact.find(record) else {
        return false;
    };
    let suffix = &compact[record_offset + record.len()..];
    let Some(open) = suffix.find('[') else {
        return false;
    };
    let before_open = &suffix[..open];
    !before_open.is_empty()
        && before_open
            .bytes()
            .all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
}

fn container_stores_inline_record(compact: &str, record: &str) -> bool {
    ["vector<", "array<", "FixedArray<"]
        .iter()
        .any(|container| {
            compact.match_indices(container).any(|(offset, _)| {
                let element = field_access::first_template_argument(&compact[offset..]);
                element.is_some_and(|element| {
                    let outer = field_access::without_template_arguments(element);
                    !outer.contains(['*', '&']) && clean_type_name(&outer) == record
                })
            })
        })
}

fn add_record_wide_concurrency(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    variable_types: &HashMap<String, Vec<usize>>,
    line_no: usize,
    line: &str,
    evidence: &mut [CppEvidenceSet],
) {
    let mut record_indices: HashSet<usize> = HashSet::new();
    for token in identifier_tokens(line) {
        if let Some(indices) = variable_types.get(token) {
            record_indices.extend(indices.iter().copied());
        }
    }
    for record_idx in record_indices {
        let record = index.record(record_idx);
        evidence[record_idx].push_item(CppEvidenceItem {
            element_member_path: Vec::new(),
            concurrent_call_path: Vec::new(),
            kind: if line.contains("#pragma omp") {
                CppEvidenceKind::OpenMp
            } else if contains_parallel_library_token(line) {
                CppEvidenceKind::ParallelLibrary
            } else {
                CppEvidenceKind::ThreadSpawn
            },
            access_kind: None,
            field_name: None,
            hotness_score: 1.0,
            in_concurrent_context: true,
            through_shared_indirection: false,
            through_raw_pointer: false,
            through_thread_local: false,
            through_nonescaping_local: false,
            through_automatic_receiver: false,
            guard_ids: Vec::new(),
            initialization_phase: false,
            in_record_constructor: false,
            function_name: None,
            description: format!(
                "C++ parallel construct near '{}' at {}:{}",
                record.name, file.path, line_no
            ),
            file: file.path.clone(),
            line: line_no,
        });
    }
}

fn concurrent_context_lines(file: &ParsedCppFile) -> HashSet<usize> {
    let mut lines = HashSet::new();
    if !contains_concurrency_token(&file.source) && !contains_parallel_library_token(&file.source) {
        return lines;
    }
    if let Some(tree) = &file.tree {
        // This grammar can misparse C++23 `[] -> T { ... }` callbacks as
        // ERROR nodes. Reparse only AST-recognized capture lists with an
        // immediately following trailing-return arrow, adding the equivalent
        // empty parameter list. Only line facts are reused; original offsets,
        // source text and field binding remain untouched.
        if tree.root_node().has_error() {
            let mut insertions = Vec::new();
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() == "lambda_capture_specifier"
                    && file.source[node.end_byte()..]
                        .trim_start()
                        .starts_with("->")
                {
                    insertions.push(node.end_byte());
                }
            });
            if !insertions.is_empty() {
                insertions.sort_unstable();
                insertions.dedup();
                let mut source = file.source.clone();
                for offset in insertions.into_iter().rev() {
                    source.insert_str(offset, "()");
                }
                let mut parser = tree_sitter::Parser::new();
                if parser
                    .set_language(&tree_sitter_cpp::LANGUAGE.into())
                    .is_ok()
                    && let Some(tree) = parser.parse(&source, None)
                {
                    lines.extend(concurrent_context_lines(&ParsedCppFile {
                        is_c: file.is_c,
                        allow_internal_linkage_proof: file.allow_internal_linkage_proof,
                        path: file.path.clone(),
                        source,
                        tree: Some(tree),
                    }));
                }
            }
        }
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "lambda_expression" {
                return;
            }
            let mut ancestor = node.parent();
            let mut parallel_call = false;
            let mut constructor_callback = false;
            while let Some(parent) = ancestor {
                if matches!(parent.kind(), "argument_list" | "initializer_list")
                    && parent.named_child(0) == Some(node)
                {
                    constructor_callback = true;
                }
                if parent.kind() == "declaration" {
                    // Direct construction is not a call_expression in this
                    // grammar. Only the first constructor argument is the
                    // thread entry callable; later lambdas may be plain data.
                    parallel_call = constructor_callback
                        && parent.child_by_field_name("type").is_some_and(|ty| {
                            matches!(
                                node_text(ty, &file.source)
                                    .split_whitespace()
                                    .collect::<String>()
                                    .trim_start_matches("::"),
                                "std::thread" | "std::jthread"
                            )
                        });
                    break;
                }
                if parent.kind() == "call_expression" {
                    // Inspect the callee and execution policy, not the callback
                    // body: a sequential wrapper may itself contain a thread
                    // creation call without making its entire body concurrent.
                    let callee = parent
                        .child_by_field_name("function")
                        .map(|callee| {
                            // A chained call's receiver can contain an earlier
                            // parallel callback. That callback does not make
                            // this call's argument a parallel entry point.
                            let callee = if callee.kind() == "field_expression"
                                && callee
                                    .child_by_field_name("argument")
                                    .is_some_and(|receiver| receiver.kind() == "call_expression")
                            {
                                callee.child_by_field_name("field").unwrap_or(callee)
                            } else {
                                callee
                            };
                            node_text(callee, &file.source)
                        })
                        .unwrap_or("");
                    let policy = parent
                        .child_by_field_name("arguments")
                        .and_then(|arguments| arguments.named_child(0))
                        .map(|argument| node_text(argument, &file.source))
                        .unwrap_or("");
                    parallel_call = contains_concurrency_token(callee)
                        || contains_parallel_library_token(callee)
                        || policy.starts_with("std::execution::par");
                    break;
                }
                if matches!(parent.kind(), "function_definition" | "compound_statement") {
                    break;
                }
                ancestor = parent.parent();
            }
            if parallel_call {
                for line in (node.start_position().row + 1)..=(node.end_position().row + 1) {
                    lines.insert(line);
                }
            }
        });

        let functions = collect_function_regions(file);
        // Thread entry functions are concurrent even when the worker index is
        // recovered from an opaque `void *` argument.  Model the callback
        // position of standard/POSIX and common GLib creation APIs instead of
        // relying on identifier spellings inside the worker body.
        for (api, callback_position) in [
            ("pthread_create", 2usize),
            ("thrd_create", 1usize),
            ("g_thread_new", 1usize),
            ("kthread_run", 0usize),
            ("kthread_run_on_cpu", 0usize),
        ] {
            for arguments in call_argument_lists(&file.source, api)
                .into_iter()
                .filter(|arguments| arguments.len() > callback_position)
            {
                let Some(worker) = callable_identifier(&arguments[callback_position]) else {
                    continue;
                };
                if let Some(function) = functions.iter().find(|function| function.name == worker) {
                    lines.extend(function.body_start_line..=function.body_end_line);
                }
            }
        }
        // Do not expand the enclosing function merely because it constructs a
        // `std::thread`.  The lambda/declaration handling above already marks
        // the actual entry callable body.  The enclosing function also contains
        // setup and teardown code which remains sequential; treating all of it
        // as concurrent creates spurious indexed-write conflicts.
        // Named entry functions still need their own body marked.  Resolve only
        // the first constructor argument, which is the callable position.
        let mut in_block_comment = false;
        for source_line in file.source.lines() {
            let mut code = String::new();
            let mut remainder = source_line;
            while !remainder.is_empty() {
                if in_block_comment {
                    let Some(end) = remainder.find("*/") else {
                        remainder = "";
                        continue;
                    };
                    in_block_comment = false;
                    remainder = &remainder[end + 2..];
                } else if let Some(start) = remainder.find("/*") {
                    code.push_str(&remainder[..start]);
                    in_block_comment = true;
                    remainder = &remainder[start + 2..];
                } else {
                    code.push_str(remainder);
                    remainder = "";
                }
            }
            let code = code
                .split_once("//")
                .map_or(code.as_str(), |(code, _)| code);
            let source_line = code;
            let trimmed = source_line.trim_start();
            if trimmed.starts_with("//")
                || trimmed.is_empty()
                || (!source_line.contains("std::thread") && !source_line.contains("std::jthread"))
            {
                continue;
            }
            let Some(open) = source_line.find(['(', '{']) else {
                continue;
            };
            let remainder = &source_line[open + 1..];
            let callback = remainder
                .split([',', ')', '}'])
                .next()
                .map(str::trim)
                .and_then(|value| value.split_whitespace().last())
                .map(|value| value.trim_matches('&'));
            let Some(callback) = callback else { continue };
            if callback.is_empty() || callback.contains('[') || callback.contains('(') {
                continue;
            }
            if let Some(function) = functions.iter().find(|function| function.name == callback) {
                lines.extend(function.body_start_line..=function.body_end_line);
            }
        }
    } else {
        for (idx, line) in file.source.lines().enumerate() {
            // OpenMP pragmas are handled below with the exact controlled
            // statement extent. Do not apply the broad lexical window here,
            // since it can mark unrelated writes after the loop as concurrent.
            if line.trim_start().starts_with("#pragma") {
                continue;
            }
            if contains_concurrency_token(line) || contains_parallel_library_token(line) {
                let line_no = idx + 1;
                for near in line_no.saturating_sub(2)..=line_no + 12 {
                    lines.insert(near);
                }
            }
        }
    }

    let source_lines = file.source.lines().collect::<Vec<_>>();
    for (idx, line) in source_lines.iter().enumerate() {
        if !line.trim_start().starts_with("#pragma") {
            continue;
        }
        let mut directive_end = idx;
        while source_lines[directive_end].trim_end().ends_with('\\')
            && directive_end + 1 < source_lines.len()
        {
            directive_end += 1;
        }
        let directive = source_lines[idx..=directive_end]
            .join(" ")
            .replace('\\', " ");
        if !omp_thread_work_directive(&directive) {
            continue;
        }
        let Some(body_start) = source_lines
            .iter()
            .enumerate()
            .skip(directive_end + 1)
            .find(|(_, candidate)| {
                let candidate = candidate.trim();
                !candidate.is_empty()
                    && !matches!(
                        candidate.split_whitespace().next(),
                        Some("#if" | "#ifdef" | "#ifndef" | "#else" | "#elif" | "#endif")
                    )
            })
            .map(|(line, _)| line)
        else {
            continue;
        };
        let body_end = syntax_controlled_statement_end(file, body_start)
            .unwrap_or_else(|| braced_scope_end_allow_next_line(&source_lines, body_start));
        for line in (body_start + 1)..=(body_end + 1) {
            lines.insert(line);
        }
    }
    // Some portability layers expose OpenMP regions through statement-like
    // macros (for example `vendor_omp_parallel { ... }`).  The semantic token
    // is still explicit and the following lexical block has the same MHP
    // meaning as a pragma region.
    for (idx, line) in source_lines.iter().enumerate() {
        let lower = line.to_ascii_lowercase();
        if !lower.contains("omp_parallel") || line.trim_start().starts_with('#') {
            continue;
        }
        let body_end = braced_scope_end_allow_next_line(&source_lines, idx);
        for line in (idx + 1)..=(body_end + 1) {
            lines.insert(line);
        }
    }
    lines
}

fn syntax_controlled_statement_end(file: &ParsedCppFile, start: usize) -> Option<usize> {
    let tree = file.tree.as_ref()?;
    let mut best = None;
    walk_nodes(tree.root_node(), &mut |node| {
        if node.start_position().row == start
            && matches!(
                node.kind(),
                "for_statement" | "for_range_loop" | "while_statement" | "do_statement"
            )
        {
            best = Some(best.map_or(node.end_position().row, |end: usize| {
                end.max(node.end_position().row)
            }));
        }
    });
    best
}

fn braced_scope_end_allow_next_line(lines: &[&str], start: usize) -> usize {
    if lines.get(start).is_some_and(|line| line.contains('{')) {
        return braced_scope_end(lines, start);
    }
    let next = (start + 1..lines.len()).find(|line| !lines[*line].trim().is_empty());
    if next.is_some_and(|line| lines[line].trim_start().starts_with('{')) {
        return braced_scope_end(lines, next.unwrap());
    }
    start
}

fn contains_concurrency_token(source: &str) -> bool {
    source.contains("std::thread")
        || source.contains("pthread_create")
        || source.contains("thrd_create")
        || source.contains("g_thread_new")
        || source.contains("kthread_run")
        || source.contains("std::async")
        || source.contains("thread_pool")
        || source.contains("ThreadPool")
        || source.contains("std::jthread")
        || source.lines().any(omp_thread_work_directive)
}

// SIMD lanes do not establish execution on different CPU threads. Standalone
// atomic/barrier/declaration directives likewise do not create a parallel body.
// Worksharing constructs are retained for orphaned regions called by a team;
// combined `parallel for simd` still has an explicit threading construct.
fn omp_thread_work_directive(source: &str) -> bool {
    let Some(directive) = source.trim_start().strip_prefix("#pragma") else {
        return false;
    };
    let mut tokens = directive.split_whitespace();
    if tokens.next() != Some("omp") {
        return false;
    }
    let mut construct = tokens.next();
    if construct == Some("target") {
        construct = tokens.next();
    }
    matches!(
        construct,
        Some("parallel" | "for" | "sections" | "task" | "taskloop" | "teams" | "distribute")
    )
}

fn contains_parallel_library_token(source: &str) -> bool {
    source.contains("parallel_for")
        || source.contains("parallel_reduce")
        || source.contains("particle_loop")
        || source.contains("omp_parallel")
        || source.contains("omp_for")
        || source.contains("tbb::parallel_")
        || source.contains("std::execution::par")
}

fn line_mentions_field(line: &str, field: &str) -> bool {
    line.contains(&format!(".{field}"))
        || line.contains(&format!("->{field}"))
        || line.contains(&format!(" {field}"))
        || line.contains(&format!("{field}."))
        || token_occurs(line, field)
}

fn mentioned_fields_in_line<'a>(
    line: &'a str,
    index: &'a EvidenceIndex<'a>,
    variable_types: &HashMap<String, Vec<usize>>,
    implicit_record: Option<usize>,
    usage_file: &str,
) -> Vec<(usize, &'a str)> {
    let mut mentions = Vec::new();
    let mut seen = HashSet::new();
    for (receiver, field) in field_access_tokens(line) {
        if !index.is_known_field(field) {
            continue;
        }
        if !line_mentions_field(line, field) {
            continue;
        }
        if let Some(record_idx) = resolve_field_owner(
            field,
            receiver,
            index,
            variable_types,
            implicit_record,
            usage_file,
        ) && seen.insert((record_idx, field))
        {
            mentions.push((record_idx, field));
        }
    }
    mentions
}

fn collect_variable_types(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
) -> HashMap<String, Vec<usize>> {
    let mut variables: HashMap<String, Vec<usize>> = HashMap::new();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(node.kind(), "declaration" | "parameter_declaration") {
                return;
            }
            let Some(type_node) = node.child_by_field_name("type") else {
                return;
            };
            let type_text = node_text(type_node, &file.source);
            let mut record_indices: Vec<usize> = identifier_tokens(type_text)
                .filter_map(|name| index.unambiguous_record_index(name, &file.path))
                .collect::<HashSet<_>>()
                .into_iter()
                .collect();
            if record_indices.is_empty() {
                let declaration = node_text(node, &file.source);
                if declaration.contains("make_unique<") || declaration.contains("make_shared<") {
                    record_indices = identifier_tokens(declaration)
                        .filter_map(|name| index.unambiguous_record_index(name, &file.path))
                        .collect::<HashSet<_>>()
                        .into_iter()
                        .collect();
                }
            }
            if record_indices.len() != 1 {
                return;
            }
            let mut cursor = node.walk();
            for declarator in node.children_by_field_name("declarator", &mut cursor) {
                if let Some(variable) = declarator_variable_name(declarator, &file.source) {
                    variables
                        .entry(variable)
                        .or_default()
                        .extend(record_indices.iter().copied());
                }
            }
        });
        for candidates in variables.values_mut() {
            candidates.sort_unstable();
            candidates.dedup();
        }
        // Keep supplementing from source text.  A mostly valid tree can still
        // place a macro-decorated C function signature under ERROR, omitting
        // precisely the pointer parameter that binds later field accesses.
    }

    for line in file.source.lines() {
        let line = line.trim();
        if line.starts_with('#')
            || line.starts_with("using ")
            || line.starts_with("typedef ")
            || is_comment_only_line(line)
        {
            continue;
        }
        let tokens: Vec<&str> = identifier_tokens(line).collect();
        for (position, token) in tokens.iter().enumerate() {
            let Some(record_indices) = index.record_indices_for_name(token) else {
                continue;
            };
            let Some(variable) = tokens.get(position + 1).copied() else {
                continue;
            };
            if variable == *token || !looks_like_variable_name(variable) {
                continue;
            }
            let entry = variables.entry(variable.to_string()).or_default();
            for record_idx in record_indices {
                if !entry.contains(record_idx) {
                    entry.push(*record_idx);
                }
            }
        }
    }
    variables
}

fn declarator_variable_name(node: tree_sitter::Node<'_>, source: &str) -> Option<String> {
    // Some generated C++ declarators are nested deeply enough to exhaust the
    // process stack. Keep this traversal iterative; the outer tree walk is
    // already recursive and should not gain another unbounded recursion level.
    let mut pending = vec![node];
    while let Some(candidate) = pending.pop() {
        if candidate.kind() == "function_declarator" {
            continue;
        }
        if matches!(candidate.kind(), "identifier" | "field_identifier") {
            return Some(node_text(candidate, source).to_string());
        }
        let mut cursor = candidate.walk();
        let children: Vec<_> = candidate.named_children(&mut cursor).collect();
        pending.extend(children.into_iter().rev());
    }
    None
}

fn collect_implicit_record_lines(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
) -> HashMap<usize, usize> {
    let mut by_line = HashMap::new();
    let Some(tree) = &file.tree else {
        return by_line;
    };
    // Node::parent() asks tree-sitter to recover an ancestor by searching for
    // its descendant. Repeating that for every function in a very wide source
    // tree is quadratic. Carry the lexical record while walking each node
    // once instead, and cache out-of-line owner resolution by scope.
    let mut pending = vec![(tree.root_node(), None)];
    let mut qualified_owners = HashMap::<String, Option<usize>>::new();
    while let Some((node, inherited_owner)) = pending.pop() {
        let lexical_owner = if matches!(node.kind(), "struct_specifier" | "class_specifier") {
            node.child_by_field_name("name")
                .map_or(inherited_owner, |name| {
                    index.unambiguous_record_index(node_text(name, &file.source), &file.path)
                })
        } else {
            inherited_owner
        };
        if node.kind() == "function_definition" {
            let mut owner = lexical_owner;
            if owner.is_none()
                && let Some(mut declarator) = node.child_by_field_name("declarator")
            {
                while let Some(inner) = declarator.child_by_field_name("declarator") {
                    declarator = inner;
                }
                let mut qualified = String::new();
                let mut depth = 0usize;
                for ch in node_text(declarator, &file.source).chars() {
                    match ch {
                        '<' => depth += 1,
                        '>' if depth > 0 => depth -= 1,
                        _ if depth == 0 && !ch.is_whitespace() => qualified.push(ch),
                        _ => {}
                    }
                }
                if let Some((scope, _)) = qualified.rsplit_once("::") {
                    owner = *qualified_owners
                        .entry(scope.to_string())
                        .or_insert_with(|| {
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
                                        == scope.trim_start_matches("::")
                                });
                                if let Some(candidate) = exact.next()
                                    && exact.next().is_none()
                                {
                                    return Some(candidate);
                                }
                                return index.unambiguous_record_index(name, &file.path);
                            }
                            None
                        });
                }
            }
            if let Some(owner) = owner {
                let body = node.child_by_field_name("body").unwrap_or(node);
                for line in (body.start_position().row + 1)..=(body.end_position().row + 1) {
                    by_line.insert(line, owner);
                }
            }
        }
        let mut cursor = node.walk();
        let children = node.children(&mut cursor).collect::<Vec<_>>();
        pending.extend(
            children
                .into_iter()
                .rev()
                .map(|child| (child, lexical_owner)),
        );
    }
    by_line
}

fn field_declaration_lines(file: &ParsedCppFile) -> HashSet<usize> {
    let mut lines = HashSet::new();
    let Some(tree) = &file.tree else {
        return lines;
    };
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "field_declaration" {
            return;
        }
        for line in (node.start_position().row + 1)..=(node.end_position().row + 1) {
            lines.insert(line);
        }
    });
    lines
}

fn looks_like_variable_name(token: &str) -> bool {
    !matches!(
        token,
        "alignas"
            | "class"
            | "const"
            | "delete"
            | "enum"
            | "final"
            | "new"
            | "noexcept"
            | "override"
            | "private"
            | "protected"
            | "public"
            | "return"
            | "sizeof"
            | "static"
            | "struct"
            | "template"
            | "typedef"
            | "typename"
            | "using"
            | "volatile"
    )
}

fn resolve_field_owner(
    field: &str,
    receiver: Option<&str>,
    index: &EvidenceIndex<'_>,
    variable_types: &HashMap<String, Vec<usize>>,
    implicit_record: Option<usize>,
    _usage_file: &str,
) -> Option<usize> {
    index.record_indices_for_field(field)?;

    if let Some(receiver) = receiver {
        if let Some(variable_candidates) = variable_types.get(receiver) {
            let mut matching = variable_candidates.iter().copied().filter(|candidate| {
                index
                    .record(*candidate)
                    .fields
                    .iter()
                    .any(|candidate_field| candidate_field.name == field)
            });
            if let Some(first) = matching.next()
                && matching.next().is_none()
            {
                return Some(first);
            }
        }
        if receiver == "this"
            && let Some(owner) = implicit_record
            && index
                .record(owner)
                .fields
                .iter()
                .any(|candidate_field| candidate_field.name == field)
        {
            return Some(owner);
        }
    } else if let Some(owner) = implicit_record
        && index
            .record(owner)
            .fields
            .iter()
            .any(|candidate_field| candidate_field.name == field)
    {
        return Some(owner);
    }

    // A bare token outside a member function is not field evidence. Falling
    // back to the only same-named field in a file attached unrelated locals,
    // enum values and macros to records in large translation units.
    None
}

fn classify_field_access(line: &str, field: &str) -> Option<CppAccessKind> {
    if let Some(kind) = macro_field_mutation(line, field) {
        return Some(kind);
    }
    let bytes = line.as_bytes();
    let has_qualified_occurrence = line.match_indices(field).any(|(start, _)| {
        let end = start + field.len();
        let bounded_before = start == 0 || !is_ident_continue(bytes[start - 1]);
        let bounded_after = end == bytes.len() || !is_ident_continue(bytes[end]);
        let before = line[..start].trim_end();
        bounded_before && bounded_after && (before.ends_with('.') || before.ends_with("->"))
    });
    let mut offset = 0usize;
    let mut best = None;
    while offset < bytes.len() {
        while offset < bytes.len() && !is_ident_start(bytes[offset]) {
            offset += 1;
        }
        let start = offset;
        while offset < bytes.len() && is_ident_continue(bytes[offset]) {
            offset += 1;
        }
        if start == offset {
            break;
        }
        if &line[start..offset] != field {
            continue;
        }
        let before = line[..start].trim_end();
        if has_qualified_occurrence && !(before.ends_with('.') || before.ends_with("->")) {
            continue;
        }
        let after = line[offset..].trim_start();
        let exact_mutation = mutation_kind_around(before, after);
        let indexed_tail = after
            .starts_with('[')
            .then(|| after.find(']').map(|end| after[end + 1..].trim_start()))
            .flatten();
        let access = if let Some(kind) = exact_mutation {
            kind
        } else if before.ends_with("++")
            || before.ends_with("--")
            || after.starts_with("++")
            || after.starts_with("--")
            || ["+=", "-=", "*=", "/=", "%=", "|=", "&=", "^="]
                .iter()
                .any(|operator| after.starts_with(operator))
            || [
                ".fetch_",
                ".exchange(",
                ".compare_exchange",
                ".test_and_set(",
                ".lock(",
                ".unlock(",
                ".try_lock(",
                ".tryLock(",
                ".lockShared(",
                ".unlockShared(",
                ".tryLockShared(",
            ]
            .iter()
            .any(|method| after.starts_with(method))
            || indexed_tail.is_some_and(|tail| {
                tail.starts_with("++")
                    || tail.starts_with("--")
                    || ["+=", "-=", "*=", "/=", "%=", "|=", "&=", "^="]
                        .iter()
                        .any(|operator| tail.starts_with(operator))
            })
        {
            CppAccessKind::ReadModifyWrite
        } else if after.starts_with(".store(")
            || after.starts_with(".clear(")
            || (after.starts_with('=') && !after.starts_with("=="))
            || indexed_tail.is_some_and(|tail| tail.starts_with('=') && !tail.starts_with("=="))
        {
            CppAccessKind::Write
        } else {
            CppAccessKind::Read
        };
        if matches!(access, CppAccessKind::ReadModifyWrite) {
            return Some(access);
        }
        if best.is_none() || matches!(access, CppAccessKind::Write) {
            best = Some(access);
        }
    }
    best
}

fn macro_field_mutation(line: &str, field: &str) -> Option<CppAccessKind> {
    let mut best = None;
    // Read, output-buffer and expected-value operands have different roles.
    // Exact summaries avoid treating every argument of an "atomic"-named
    // function as the mutated target.
    for call in identifier_tokens(line).collect::<HashSet<_>>() {
        if explicit_atomic_argument_access(call, 0).is_none() {
            continue;
        }
        for arguments in call_argument_lists(line, call) {
            for (argument, target) in arguments.iter().enumerate() {
                if contains_identifier(target, field)
                    && let Some(kind) = explicit_atomic_argument_access(call, argument)
                    && best.as_ref().is_none_or(|existing| {
                        access_kind_strength(&kind) > access_kind_strength(existing)
                    })
                {
                    best = Some(kind);
                }
            }
        }
    }
    for (call, kind) in [
        ("atomicIncr", CppAccessKind::ReadModifyWrite),
        ("atomicDecr", CppAccessKind::ReadModifyWrite),
        ("atomicAdd", CppAccessKind::ReadModifyWrite),
        ("atomicSub", CppAccessKind::ReadModifyWrite),
        ("atomicSet", CppAccessKind::Write),
        ("atomicSetWithSync", CppAccessKind::Write),
        ("__atomic_store_n", CppAccessKind::Write),
        ("__atomic_fetch_add", CppAccessKind::ReadModifyWrite),
        ("__atomic_fetch_sub", CppAccessKind::ReadModifyWrite),
        ("atomic_store", CppAccessKind::Write),
        ("atomic_fetch_add", CppAccessKind::ReadModifyWrite),
        ("atomic_fetch_sub", CppAccessKind::ReadModifyWrite),
        ("atomic_inc", CppAccessKind::ReadModifyWrite),
        ("atomic_dec", CppAccessKind::ReadModifyWrite),
        ("atomic_dec_if_positive", CppAccessKind::ReadModifyWrite),
        ("atomic_set", CppAccessKind::Write),
    ] {
        let target_matches = call_argument_lists(line, call)
            .into_iter()
            .filter_map(|arguments| arguments.into_iter().next())
            .any(|target| contains_identifier(&target, field));
        if target_matches
            && best
                .as_ref()
                .is_none_or(|existing| access_kind_strength(&kind) > access_kind_strength(existing))
        {
            best = Some(kind);
        }
    }
    best
}

fn explicit_atomic_argument_access(callee: &str, argument: usize) -> Option<CppAccessKind> {
    let name = callee.trim().trim_start_matches("::");
    let name = name.strip_prefix("std::").unwrap_or(name);
    let first = match name {
        "atomic_load" | "atomic_load_explicit" | "__atomic_load" | "__atomic_load_n" => {
            CppAccessKind::Read
        }
        "atomic_init"
        | "atomic_store"
        | "atomic_store_explicit"
        | "atomic_flag_clear"
        | "atomic_flag_clear_explicit"
        | "__atomic_store"
        | "__atomic_store_n"
        | "__atomic_clear" => CppAccessKind::Write,
        "atomic_exchange"
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
        | "__atomic_test_and_set" => CppAccessKind::ReadModifyWrite,
        _ => {
            // Runtime and portability layers commonly prefix the standard
            // atomic operation name (jl_atomic_store, rte_atomic_fetch_add,
            // project_atomic_cmpswap, ...).  Classify the operation suffix,
            // but retain the standard first-argument contract instead of
            // treating every argument of an "atomic"-named call as a write.
            let lower = name.to_ascii_lowercase();
            if !lower.contains("atomic") && !lower.starts_with("__sync_") {
                return None;
            }
            if lower.contains("load") {
                CppAccessKind::Read
            } else if lower.contains("store") || lower.ends_with("_clear") {
                CppAccessKind::Write
            } else if lower.contains("compare_exchange")
                || lower.contains("cmpswap")
                || lower.contains("exchange")
                || lower.contains("fetch_")
                || lower.starts_with("__sync_")
                || lower.ends_with("_inc")
                || lower.ends_with("_dec")
            {
                CppAccessKind::ReadModifyWrite
            } else {
                return None;
            }
        }
    };
    if argument == 0 {
        return Some(first);
    }
    match (name, argument) {
        ("__atomic_load", 1) | ("__atomic_exchange", 2) => Some(CppAccessKind::Write),
        ("__atomic_store" | "__atomic_exchange", 1) => Some(CppAccessKind::Read),
        (
            "atomic_compare_exchange_strong"
            | "atomic_compare_exchange_strong_explicit"
            | "atomic_compare_exchange_weak"
            | "atomic_compare_exchange_weak_explicit"
            | "__atomic_compare_exchange"
            | "__atomic_compare_exchange_n",
            1,
        ) => Some(CppAccessKind::ReadModifyWrite),
        ("__atomic_compare_exchange", 2) => Some(CppAccessKind::Read),
        _ => None,
    }
}

fn looks_like_signature_or_reference(line: &str) -> bool {
    line.contains('(')
        || line.contains("shared_ptr")
        || line.contains('&')
        || line.contains('*')
        || line.contains('<')
}

fn field_access_tokens(line: &str) -> Vec<(Option<&str>, &str)> {
    let mut tokens = Vec::new();
    let bytes = line.as_bytes();
    let mut idx = 0usize;
    while idx < bytes.len() {
        let marker_len = if bytes[idx] == b'.' {
            1
        } else if idx + 1 < bytes.len() && bytes[idx] == b'-' && bytes[idx + 1] == b'>' {
            2
        } else {
            idx += 1;
            continue;
        };
        let receiver = receiver_before_marker(line, idx);
        idx += marker_len;
        while idx < bytes.len() && !is_ident_start(bytes[idx]) {
            idx += 1;
        }
        let start = idx;
        while idx < bytes.len() && is_ident_continue(bytes[idx]) {
            idx += 1;
        }
        if start < idx {
            tokens.push((receiver, &line[start..idx]));
        }
    }
    tokens.extend(bare_field_tokens(line));
    tokens
}

fn bare_field_tokens(line: &str) -> Vec<(Option<&str>, &str)> {
    let bytes = line.as_bytes();
    let mut tokens = Vec::new();
    let mut offset = 0usize;
    while offset < bytes.len() {
        while offset < bytes.len() && !is_ident_start(bytes[offset]) {
            offset += 1;
        }
        let start = offset;
        while offset < bytes.len() && is_ident_continue(bytes[offset]) {
            offset += 1;
        }
        if offset - start < 3 {
            continue;
        }
        let before = start.checked_sub(1).map(|idx| bytes[idx]);
        let after = bytes.get(offset).copied();
        if start == 0
            || before.is_some_and(|byte| byte.is_ascii_whitespace())
            || after == Some(b'.')
        {
            tokens.push((None, &line[start..offset]));
        }
    }
    tokens
}

fn receiver_before_marker(line: &str, marker: usize) -> Option<&str> {
    let bytes = line.as_bytes();
    let mut end = marker;
    while end > 0 && bytes[end - 1].is_ascii_whitespace() {
        end -= 1;
    }
    if end > 0 && bytes[end - 1] == b']' {
        let mut depth = 1usize;
        end -= 1;
        while end > 0 && depth > 0 {
            end -= 1;
            match bytes[end] {
                b']' => depth += 1,
                b'[' => depth -= 1,
                _ => {}
            }
        }
        while end > 0 && bytes[end - 1].is_ascii_whitespace() {
            end -= 1;
        }
    }
    let mut start = end;
    while start > 0 && is_ident_continue(bytes[start - 1]) {
        start -= 1;
    }
    (start < end).then(|| &line[start..end])
}

fn identifier_tokens(source: &str) -> impl Iterator<Item = &str> {
    IdentifierTokens { source, offset: 0 }
}

struct IdentifierTokens<'a> {
    source: &'a str,
    offset: usize,
}

impl<'a> Iterator for IdentifierTokens<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        let bytes = self.source.as_bytes();
        while self.offset < bytes.len() && !is_ident_start(bytes[self.offset]) {
            self.offset += 1;
        }
        let start = self.offset;
        while self.offset < bytes.len() && is_ident_continue(bytes[self.offset]) {
            self.offset += 1;
        }
        if start == self.offset {
            return None;
        }
        Some(&self.source[start..self.offset])
    }
}

fn is_ident_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic()
}

fn is_ident_continue(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphanumeric()
}

fn is_record_constructor(function_name: &str, record: &CppStructInfo) -> bool {
    function_name == record.name
        || function_name
            .rsplit("::")
            .next()
            .is_some_and(|name| name == record.name)
}

fn method_name_suggests_hot_use(name: &str) -> bool {
    [
        "inc", "add", "update", "record", "track", "push", "pop", "enqueue", "dequeue", "run",
        "poll", "tick", "advance", "reserve", "publish", "consume", "dispatch", "schedule", "lock",
        "unlock",
    ]
    .iter()
    .any(|keyword| name.to_lowercase().contains(keyword))
}

fn semantic_name_suggests_hot_use(name: &str) -> bool {
    let clean = clean_type_name(name).to_lowercase();
    [
        "counter", "counters", "stats", "metric", "bucket", "shard", "slot", "queue", "ring",
        "worker", "thread", "epoch", "state", "cache",
    ]
    .iter()
    .any(|keyword| clean.contains(keyword))
}

pub fn container_field_element_name(
    field_ty: &str,
    explicit_element: Option<&str>,
) -> Option<String> {
    explicit_element
        .map(clean_type_name)
        .or_else(|| element_type_name(field_ty))
}

pub(super) fn container_has_atomic_elements(field: &super::types::CppFieldInfo) -> bool {
    let element = if field.is_array {
        field.element_type.as_deref()
    } else {
        field_access::first_template_argument(&field.ty_str)
    };
    element.is_some_and(super::layout::is_cpp_atomic_type)
}

pub fn is_container_field_name(name: &str, ty: &str) -> bool {
    if !is_hot_container_name(name) {
        return false;
    }
    let outer = field_access::without_template_arguments(ty);
    if outer.contains(['*', '&']) {
        return false;
    }
    // Only an outer sequence owns these slots. A vector appearing inside a
    // map, optional, pointer wrapper or other template argument says nothing
    // about the enclosing field's element stride.
    outer.contains('[')
        || matches!(
            outer
                .split_whitespace()
                .last()
                .unwrap_or("")
                .trim_start_matches("::"),
            "std::vector" | "vector" | "std::array" | "absl::FixedArray" | "folly::small_vector"
        )
}

/// Bind declaration-only rule families through the same native-array index.
/// No binding is inferred for sibling storage groups or class-static members.
pub(super) fn bind_declared_storage(
    files: &[ParsedCppFile],
    findings: &mut [crate::types::Finding],
) {
    use crate::types::{CandidateKind, ColocationPattern};
    if !findings.iter().any(|f| {
        matches!(
            f.candidate_kind,
            CandidateKind::StaticData | CandidateKind::AtomicArray
        )
    }) {
        return;
    }
    let index = storage_identity::StorageIndex::new(files);
    for finding in findings {
        if finding.struct_name.is_some()
            || !matches!(
                finding.candidate_kind,
                CandidateKind::StaticData | CandidateKind::AtomicArray
            )
            || finding.static_pattern.as_ref().is_none_or(|p| {
                p.colocation_pattern != ColocationPattern::ContiguousElements
                    && !(finding.candidate_kind == CandidateKind::StaticData
                        && finding.field_list.len() == 1
                        && p.colocation_pattern == ColocationPattern::StaticStorage)
            })
        {
            continue;
        }
        let mut identities = finding
            .field_list
            .iter()
            .filter_map(|name| index.definition(&finding.file, name));
        if let Some((line, identity)) = identities.next()
            && identities.next().is_none()
            && (finding.candidate_kind == CandidateKind::AtomicArray || finding.line == line)
        {
            finding.storage_identity = Some(identity);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn container_candidate_storage_comes_from_outer_type_not_template_arguments() {
        for ty in [
            "std::vector<int>",
            "std::array<int, 8>",
            "int[8]",
            "std::vector<std::vector<int>>",
            "absl::FixedArray<int>",
        ] {
            assert!(is_container_field_name("slots", ty), "{ty}");
        }
        for ty in [
            "std::unordered_map<int, std::vector<int>>",
            "std::optional<std::array<int, 8>>",
            "std::unique_ptr<std::vector<int>>",
            "std::vector<int>*",
            "std::vector<int>&",
            "Wrapper<int[8]>",
        ] {
            assert!(!is_container_field_name("slots", ty), "{ty}");
        }
    }

    #[test]
    fn method_body_recovery_does_not_erase_a_complete_base_interface() {
        let files = super::super::parser::parse_cpp_files(vec![CppFile {
            path: "interfaces.cpp".into(),
            source: "struct Base { virtual void run() { ???; } };\nstruct Broken { ???; };\nstruct Derived : Base {};".into(),
        }]);
        assert!(files[0].tree.as_ref().unwrap().root_node().has_error());
        let interfaces = index_method_interfaces(&files);
        assert_eq!(interfaces["Base"][0].bases, Some(Vec::new()));
        assert!(interfaces["Base"][0].methods.contains("run"));
        assert!(interfaces["Broken"][0].bases.is_none());
        let tree = files[0].tree.as_ref().unwrap();
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() == "struct_specifier"
                && node
                    .child_by_field_name("name")
                    .is_some_and(|n| node_text(n, &files[0].source) == "Derived")
            {
                assert!(index_bases_exclude_method(
                    node,
                    &files[0].source,
                    "privateHelper",
                    &interfaces
                ));
                assert!(!index_bases_exclude_method(
                    node,
                    &files[0].source,
                    "run",
                    &interfaces
                ));
            }
        });
    }

    #[test]
    fn checked_c_lock_dominates_only_success_continuation() {
        for condition in [
            "pthread_mutex_lock(&mutex)",
            "pthread_mutex_lock(&mutex) != 0",
            "0 != pthread_mutex_lock(&mutex)",
        ] {
            let source = format!(
                "void worker() {{\n if ({condition}) throw Error();\n observe();\n if (failed) {{\n  pthread_mutex_unlock(&mutex);\n  cleanup();\n  throw Error();\n }}\n observe_again();\n pthread_mutex_unlock(&mutex);\n outside();\n}}\n"
            );
            let files = super::super::parser::parse_cpp_files(vec![CppFile {
                path: "locks.cpp".into(),
                source,
            }]);
            let guards = collect_scoped_locksets(&files[0]);
            for line in [3, 9] {
                assert!(
                    guards
                        .get(&line)
                        .is_some_and(|set| set.iter().any(|g| g == "mutex")),
                    "{condition}: {guards:?}"
                );
            }
            for line in [6, 11] {
                assert!(!guards.contains_key(&line), "{condition}: {guards:?}");
            }
        }
    }

    #[test]
    fn conditional_lock_failure_must_not_fabricate_guard() {
        for (condition, failure) in [
            ("pthread_mutex_lock(&mutex)", "log_error();"),
            ("pthread_mutex_lock(&mutex) == 0", "return;"),
            ("pthread_mutex_trylock(&mutex)", "return;"),
            ("enabled && pthread_mutex_lock(&mutex)", "return;"),
        ] {
            let source =
                format!("void worker() {{\n if ({condition}) {failure}\n observe();\n}}\n");
            let files = super::super::parser::parse_cpp_files(vec![CppFile {
                path: "locks.cpp".into(),
                source,
            }]);
            assert!(!collect_scoped_locksets(&files[0]).contains_key(&3));
        }
        let source = "void worker() {\n try {\n if (pthread_mutex_lock(&mutex)) throw Error();\n } catch (...) {}\n observe();\n}\n";
        let files = super::super::parser::parse_cpp_files(vec![CppFile {
            path: "locks.cpp".into(),
            source: source.into(),
        }]);
        assert!(!collect_scoped_locksets(&files[0]).contains_key(&5));
    }
    use crate::cpp_detection::layout::collect_cpp_structs;
    use crate::cpp_detection::parser::parse_cpp_files;
    use crate::cpp_detection::types::CppFile;

    #[test]
    fn control_keywords_are_not_mutator_function_names() {
        for declarator in [
            "for (int i = 0; i < n; ++i)",
            "if (ready)",
            "while (ready)",
            "switch (mode)",
            "catch (Error e)",
        ] {
            assert!(callable_name(declarator).is_none(), "{declarator}");
        }
        assert_eq!(
            callable_name("void update(unsigned index)"),
            Some("update".to_string())
        );
    }

    #[test]
    fn recovered_field_access_function_is_a_bounded_callable_not_a_branch() {
        let mut files = parse_cpp_files(vec![CppFile {
            path: "branches.c".into(),
            source: "struct State { int counter; };\nvoid update(struct State* state) {\nif(state) {\nstate->counter++;\n}\nswitch(state->counter) {\ndefault: state->counter = 0;\n}\n}\nvoid next(struct State* state) {\nstate->counter++;\n}\n".into(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        files[0].tree = None;
        let evidence = collect_cpp_evidence(&files, &records);
        let names = evidence
            .iter()
            .flat_map(|set| &set.items)
            .filter(|item| item.access_kind.is_some())
            .filter_map(|item| item.function_name.as_deref())
            .collect::<HashSet<_>>();
        assert!(names.contains("update"));
        assert!(names.contains("next"));
        assert!(
            !names
                .iter()
                .any(|name| matches!(*name, "if" | "switch" | "default"))
        );
    }

    #[test]
    fn atomic_evidence_belongs_to_the_object_not_the_whole_line() {
        let files = parse_cpp_files(vec![CppFile {
            path: "atomic.cpp".into(),
            source: r#"
            struct State {
                std::vector<int> values;
                std::atomic<int> counter;
                int plain;
                int target;
                int output;
                int* pointer;
                void update() {
                    values.clear(); plain++;
                    plain = counter.load();
                    __atomic_fetch_add(&target, plain, 0);
                    __atomic_load(&target, &output, 0);
                    __atomic_fetch_add(pointer, 1, 0);
                }
            };
            "#
            .into(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        for field in ["values", "plain", "output", "pointer"] {
            assert!(
                facts[0]
                    .items
                    .iter()
                    .any(|item| item.field_name.as_deref() == Some(field)),
                "{field}"
            );
            assert!(
                !facts[0]
                    .items
                    .iter()
                    .any(|item| item.field_name.as_deref() == Some(field)
                        && item.kind == CppEvidenceKind::AtomicFieldOps),
                "{field}"
            );
        }
        for field in ["counter", "target"] {
            assert!(
                facts[0]
                    .items
                    .iter()
                    .any(|item| item.field_name.as_deref() == Some(field)
                        && item.kind == CppEvidenceKind::AtomicFieldOps),
                "{field}"
            );
        }
    }

    #[test]
    fn mutation_requires_the_actual_indexed_lvalue_not_a_later_expression() {
        for line in [
            "consume(values[worker_id]); other++;",
            "consume(values[worker_id], other.fetch_add(1));",
            "if (values[worker_id]) other = 1;",
            "values[worker_id].lookup(other.fetch_add(1));",
        ] {
            assert!(indexed_mutations(line).is_empty(), "{line}");
        }
        for line in [
            "values[worker_id].counter++;",
            "values[worker_id].nested.counter += 1;",
            "values[worker_id].at(0).counter++;",
            "values[worker_id].counter.fetch_add(1);",
        ] {
            assert!(!indexed_mutations(line).is_empty(), "{line}");
        }
    }

    #[test]
    fn c_mutator_pointer_arguments_do_not_write_pointer_members() {
        let files = parse_cpp_files(vec![CppFile {
            path: "pointers.cpp".into(),
            source: "struct State { pthread_mutex_t* lock; long* count; long* target; pthread_mutex_t own; };\nvoid update(State* s) { pthread_mutex_lock(s->lock); __atomic_fetch_add(s->count, 1, 0); __atomic_store_n(&s->target, nullptr, 0); pthread_mutex_lock(&s->own); }".into(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let evidence = collect_cpp_evidence(&files, &records);
        for field in ["lock", "count"] {
            assert!(
                evidence[0]
                    .items
                    .iter()
                    .any(|item| item.field_name.as_deref() == Some(field)
                        && item.access_kind == Some(CppAccessKind::Read))
            );
            assert!(
                !evidence[0]
                    .items
                    .iter()
                    .any(|item| item.field_name.as_deref() == Some(field)
                        && matches!(
                            item.access_kind,
                            Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                        ))
            );
        }
        for field in ["target", "own"] {
            assert!(
                evidence[0]
                    .items
                    .iter()
                    .any(|item| item.field_name.as_deref() == Some(field)
                        && matches!(
                            item.access_kind,
                            Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                        )),
                "{field}"
            );
        }
    }

    #[test]
    fn smart_pointer_alias_does_not_prove_contiguous_pointee_objects() {
        for ty in ["std::unique_ptr<Item>", "Item*"] {
            let files = parse_cpp_files(vec![CppFile {
                path: "alias.cpp".into(),
                source: format!(
                    "struct Item {{ int value; }};\nusing Alias = {ty};\nstd::vector<Alias> items;"
                ),
            }]);
            let records = collect_cpp_structs(&files, "fixture", 64);
            let facts = collect_cpp_evidence(&files, &records);
            let index = records.iter().position(|r| r.name == "Item").unwrap();
            assert!(!facts[index].has_contiguous_object_storage(), "{ty}");
        }
    }

    #[test]
    fn object_storage_distinguishes_inline_elements_from_pointer_elements() {
        for ty in [
            "std::vector<Item*>",
            "std::array<Item*,8>",
            "std::vector<std::unique_ptr<Item>>",
        ] {
            assert!(!container_stores_inline_record(ty, "Item"), "{ty}");
        }
        for ty in [
            "std::vector<Item>",
            "std::array<Item,8>",
            "std::vector<Item<int>>",
        ] {
            assert!(container_stores_inline_record(ty, "Item"), "{ty}");
        }
        assert!(!declaration_has_array_of("Item*items[8];", "Item"));
        assert!(declaration_has_array_of("Itemitems[8];", "Item"));
    }

    #[test]
    fn reference_member_write_is_not_an_inline_storage_write() {
        let files = parse_cpp_files(vec![CppFile {
            path: "reference.cpp".into(),
            source: "struct State { unsigned& external; unsigned own; void a() { external++; } void b() { own++; } };".into(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let evidence = collect_cpp_evidence(&files, &records);
        let items = &evidence[0].items;
        assert!(
            items
                .iter()
                .any(|item| item.field_name.as_deref() == Some("external")
                    && item.access_kind == Some(CppAccessKind::Read))
        );
        assert!(
            !items
                .iter()
                .any(|item| item.field_name.as_deref() == Some("external")
                    && matches!(
                        item.access_kind,
                        Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                    ))
        );
        assert!(
            items
                .iter()
                .any(|item| item.field_name.as_deref() == Some("own")
                    && item.access_kind == Some(CppAccessKind::ReadModifyWrite))
        );
    }

    #[test]
    fn alias_mutations_do_not_escape_function_or_match_longer_identifiers() {
        let lines = [
            "void f() {",
            "auto& slot = slots[id];",
            "slot_count++;",
            "}",
            "void g() {",
            "slot++;",
            "}",
        ];
        let functions = [FunctionRegion {
            name: "f".into(),
            declarator: String::new(),
            signature: String::new(),
            body_start_line: 1,
            body_end_line: 4,
        }];
        assert_eq!(pointer_alias_mutation(&lines, 1, "slot", &functions), None);
        let mut writes = lines;
        writes[2] = "slot++;";
        assert_eq!(
            pointer_alias_mutation(&writes, 1, "slot", &functions),
            Some(CppAccessKind::ReadModifyWrite)
        );
    }

    #[test]
    fn std_array_at_member_mutation_is_contiguous_element_evidence() {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.hpp".to_string(),
            source: r#"
                struct Counter { std::atomic<unsigned long> value; };
                class Metrics {
                    std::array<Counter, 256> request_counters;
                public:
                    void request(unsigned kind) { request_counters.at(kind).value++; }
                };
            "#
            .to_string(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let evidence = collect_cpp_evidence(&files, &records);
        let metrics = records
            .iter()
            .position(|record| record.name == "Metrics")
            .expect("Metrics record");
        let field = records[metrics]
            .fields
            .iter()
            .find(|field| field.name == "request_counters")
            .expect("request_counters field");
        let index = EvidenceIndex::new(&records);
        let mut direct = None;
        walk_nodes(files[0].tree.as_ref().unwrap().root_node(), &mut |node| {
            if node.kind() == "identifier"
                && node_text(node, &files[0].source) == "request_counters"
            {
                direct =
                    field_access::contiguous_element_access_kind(node, field, &files[0], &index);
            }
        });
        assert_eq!(direct, Some(CppAccessKind::ReadModifyWrite));
        assert!(
            evidence[metrics].items.iter().any(|item| {
                item.kind == CppEvidenceKind::ContiguousElementAccess
                    && item.field_name.as_deref() == Some("request_counters")
                    && item.access_kind == Some(CppAccessKind::ReadModifyWrite)
            }),
            "records={records:#?}\nevidence={:#?}",
            evidence[metrics]
        );
    }

    #[test]
    fn duplicate_record_names_bind_out_of_line_accesses_by_unique_directory() {
        let files = parse_cpp_files(vec![
            CppFile {
                path: "module_a/metrics.hpp".to_string(),
                source: r#"
                    struct Counter { std::atomic<unsigned long> value; };
                    class Metrics {
                        std::array<Counter, 256> request_counters;
                    public:
                        void request(unsigned kind);
                    };
                "#
                .to_string(),
            },
            CppFile {
                path: "module_a/metrics.cpp".to_string(),
                source:
                    "void Metrics::request(unsigned kind) { request_counters.at(kind).value++; }"
                        .to_string(),
            },
            CppFile {
                path: "module_a/generated/metrics.hpp".to_string(),
                source: r#"
                    struct Counter { std::atomic<unsigned long> value; };
                    class Metrics { std::array<Counter, 8> request_counters; };
                "#
                .to_string(),
            },
        ]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let evidence = collect_cpp_evidence(&files, &records);
        let metrics = records
            .iter()
            .position(|record| record.name == "Metrics" && record.file == "module_a/metrics.hpp")
            .expect("module_a Metrics record");
        assert!(evidence[metrics].items.iter().any(|item| {
            item.kind == CppEvidenceKind::ContiguousElementAccess
                && item.field_name.as_deref() == Some("request_counters")
                && item.access_kind == Some(CppAccessKind::ReadModifyWrite)
        }));
    }

    #[test]
    fn indexed_mutation_rejects_rhs_reads_and_address_taking() {
        assert!(indexed_mutations("const auto & value = values[worker_id];").is_empty());
        assert!(indexed_mutations("auto * ptr = &values[worker_id];").is_empty());
        assert!(indexed_mutations("consume(values[worker_id]);").is_empty());
    }

    #[test]
    fn indexed_mutation_tracks_the_actual_target_and_kind() {
        assert_eq!(
            indexed_mutations("values[worker_id] = input;"),
            vec![(
                "values".to_string(),
                "worker_id".to_string(),
                CppAccessKind::Write,
            )]
        );
        assert_eq!(
            indexed_mutations("values[worker_id].count += 1;"),
            vec![(
                "values".to_string(),
                "worker_id".to_string(),
                CppAccessKind::ReadModifyWrite,
            )]
        );
        assert_eq!(
            indexed_mutations("values[worker_id].fetch_add(1);"),
            vec![(
                "values".to_string(),
                "worker_id".to_string(),
                CppAccessKind::ReadModifyWrite,
            )]
        );
    }

    #[test]
    fn field_access_classification_distinguishes_lhs_and_rhs() {
        assert_eq!(
            classify_field_access("local = object.counter;", "counter"),
            Some(CppAccessKind::Read)
        );
        assert_eq!(
            classify_field_access("object.counter = local;", "counter"),
            Some(CppAccessKind::Write)
        );
        assert_eq!(
            classify_field_access("object.counter.fetch_add(1);", "counter"),
            Some(CppAccessKind::ReadModifyWrite)
        );
        assert_eq!(
            classify_field_access("Counter *counter = object.counter[index];", "counter"),
            Some(CppAccessKind::Read)
        );
        assert_eq!(
            classify_field_access("object.counters.at(index).value++;", "counters"),
            Some(CppAccessKind::ReadModifyWrite)
        );
    }

    #[test]
    fn atomic_alias_mutable_index_accessor_is_a_write_capability() {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.hpp".to_string(),
            source: r#"
                using Counter = std::atomic<unsigned long>;
                class Counters {
                    Counter * counters = nullptr;
                public:
                    Counter & operator[](unsigned event) {
                        return counters[event];
                    }
                };
            "#
            .to_string(),
        }]);
        let candidates = collect_atomic_alias_array_candidates(&files);
        assert!(candidates.iter().any(|candidate| {
            candidate.alias == "Counter"
                && candidate.storage_name == "counters"
                && candidate.access_is_mutable_api
                && candidate.access_kind == Some(CppAccessKind::Write)
        }));
    }

    #[test]
    fn aligned_owner_does_not_hide_indexed_member_elements() {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.cpp".to_string(),
            source: r#"
                struct alignas(64) Stats { unsigned long packets[128]; };
                Stats shared;
                void update() {
                    shared.packets[rte_lcore_id()]++;
                }
            "#
            .to_string(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let candidates = collect_indexed_write_candidates(&files, &records, 64);
        assert!(
            candidates
                .iter()
                .any(|candidate| candidate.field_name.as_deref() == Some("packets")),
            "records={records:#?}\ncontiguous={:#?}\nnoncontiguous={:#?}\ntls={:#?}\naligned={:#?}\nprotected={:#?}\ndeclarations={:#?}\nreceivers={:#?}\nmutations={:#?}\nthread={}\nsupports={}\ncandidates={candidates:#?}",
            contiguous_indexed_symbols(&files[0]),
            non_contiguous_indexed_symbols(&files[0]),
            thread_local_symbols(&files[0]),
            source_aligned_type_names(&files, 64),
            protected_indexed_symbols(
                &files[0].source.lines().collect::<Vec<_>>(),
                &source_aligned_type_names(&files, 64)
            ),
            array_declaration_sites(&files[0]),
            cache_aligned_receiver_fields(&files[0], &records.iter().collect::<Vec<_>>()),
            indexed_mutations("shared.packets[rte_lcore_id()]++;"),
            is_thread_index_expression("rte_lcore_id()"),
            collect_index_partition_origins(&files[0], &collect_function_regions(&files[0]))
                .supports("rte_lcore_id()", 5)
        );
    }

    #[test]
    fn c11_atomic_typedef_accesses_bind_to_the_recovered_record() {
        let files = parse_cpp_files(vec![CppFile {
            path: "queue.h".to_string(),
            source: r#"
                typedef struct {
                    _Atomic(long) top;
                    _Atomic(long) bottom;
                    _Atomic(void *) array;
                } Queue;
                static inline void push(Queue *q) JL_NOTSAFEPOINT
                { jl_atomic_store_relaxed(&q->bottom, 1); }
                static inline void steal(Queue *q) JL_NOTSAFEPOINT
                { jl_atomic_cmpswap(&q->top, 0, 1); }
            "#
            .to_string(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let evidence = collect_cpp_evidence(&files, &records);
        assert_eq!(records.len(), 1);
        assert!(
            records[0].visibility.is_externally_exposed(),
            "{:#?}",
            records[0]
        );
        assert!(evidence[0].has_api_signal(), "{:#?}", evidence[0]);
        assert!(
            evidence[0]
                .written_fields_matching(&records[0].atomic_fields)
                .len()
                >= 2,
            "records={records:#?}\nevidence={:#?}",
            evidence[0]
        );
    }

    #[test]
    fn bpf_array_map_frontend_recovers_map_and_cpu_origin() {
        let files = parse_cpp_files(vec![CppFile {
            path: "sample.bpf.c".to_string(),
            source: r#"
                struct {
                    __uint(type, BPF_MAP_TYPE_ARRAY);
                    __type(key, u32);
                    __type(value, u64);
                } counters SEC(".maps");
                int sample() {
                    u32 cpu = bpf_get_smp_processor_id();
                    u64 value = 1;
                    bpf_map_update_elem(&counters, &cpu, &value, 0);
                    return 0;
                }
            "#
            .to_string(),
        }]);
        let functions = collect_function_regions(&files[0]);
        let origins = collect_index_partition_origins(&files[0], &functions);
        assert_eq!(
            bpf_array_map_symbols(&files[0]),
            HashSet::from(["counters".to_string()])
        );
        assert!(origins.supports("cpu", 10));
        assert!(!collect_indexed_write_candidates(&files, &[], 64).is_empty());
    }

    #[test]
    fn contiguous_storage_resolves_a_template_record_through_a_using_alias() {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.cpp".to_string(),
            source: r#"
                template <int Role>
                class SearchTask {
                    unsigned long nodes = 0;
                    unsigned long state = 0;
                public:
                    void run() { nodes += 1; }
                    unsigned long status() const { return state; }
                };
                using WorkerTask = SearchTask<1>;
                struct Pool {
                    std::vector<WorkerTask> tasks;
                };
            "#
            .to_string(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let evidence = collect_cpp_evidence(&files, &records);
        let index = records
            .iter()
            .position(|record| record.name == "SearchTask")
            .expect("template record");
        assert!(
            evidence[index].has_contiguous_object_storage(),
            "records={records:#?}\nevidence={:#?}",
            evidence[index]
        );
        assert!(
            evidence[index]
                .written_fields_matching(
                    &records[index]
                        .fields
                        .iter()
                        .map(|field| field.name.clone())
                        .collect::<Vec<_>>()
                )
                .contains("nodes"),
            "records={records:#?}\nevidence={:#?}",
            evidence[index]
        );
    }

    #[test]
    fn allocator_topology_keeps_the_enclosing_function() {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.c".to_string(),
            source: r#"
                typedef struct Accumulator { unsigned long counter; } Accumulator;
                Accumulator *initialize_accumulator(void) {
                    Accumulator *result = aligned_alloc(64, sizeof(Accumulator));
                    return result;
                }
            "#
            .to_string(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let evidence = collect_cpp_evidence(&files, &records);
        let item = evidence
            .iter()
            .flat_map(|set| &set.items)
            .find(|item| item.kind == CppEvidenceKind::AllocatorObjectStorage)
            .expect("allocator topology");
        assert_eq!(
            item.function_name.as_deref(),
            Some("initialize_accumulator")
        );
    }

    #[test]
    fn direct_standard_thread_construction_marks_only_the_entry_callable() {
        for (prefix, suffix, expected) in [
            ("std::thread worker(", ");", true),
            ("std::jthread worker{", "};", true),
            ("OtherThread worker(", ");", false),
            ("std::thread worker(wrap(", "));", false),
            ("std::thread worker(consume, ", ");", false),
        ] {
            let source = format!("void launch() {{\n{prefix}[] {{\n touch();\n}}{suffix}\n}}");
            let files = parse_cpp_files(vec![CppFile {
                path: "thread.cpp".into(),
                source,
            }]);
            assert_eq!(
                concurrent_context_lines(&files[0]).contains(&3),
                expected,
                "prefix={prefix}"
            );
        }
    }

    #[test]
    fn standard_thread_setup_does_not_mark_outer_function_as_concurrent() {
        let files = parse_cpp_files(vec![CppFile {
            path: "thread_setup.cpp".into(),
            source: "void launch(State *state) {\n  std::thread worker([&] { state->counter++; });\n  state->setup = 1;\n  worker.join();\n}".into(),
        }]);
        let lines = concurrent_context_lines(&files[0]);
        assert!(lines.contains(&2), "entry lambda should be concurrent");
        assert!(
            !lines.contains(&3),
            "setup after construction is sequential"
        );
    }

    #[test]
    fn commented_thread_tokens_do_not_create_concurrent_entries() {
        let files = parse_cpp_files(vec![CppFile {
            path: "comments.cpp".into(),
            source: "void worker() {\n  /* std::thread fake(fake_entry);\n     std::jthread also_fake; */\n  state->counter++; // std::thread fake2(fake_entry)\n}".into(),
        }]);
        assert!(concurrent_context_lines(&files[0]).is_empty());
    }

    #[test]
    fn local_callback_inherits_only_common_guards_without_release_or_escape() {
        for (body, extra_call, expected) in [
            ("state.counter++;", "", true),
            ("state.counter++;", "update();", false),
            (
                "state.counter++;",
                "{ std::lock_guard other(different);\nupdate();\n}",
                false,
            ),
            ("pthread_mutex_unlock(&mutex); state.counter++;", "", false),
            ("release(mutex); state.counter++;", "", false),
            ("release_unknown(); state.counter++;", "", false),
            ("std::thread task([&] { state.counter++; });", "", false),
        ] {
            let files = parse_cpp_files(vec![CppFile {
                path: "guards.cpp".into(),
                source: format!(
                    "void run() {{\n auto update = [&] {{\n{body}\n }};\n {{\n std::lock_guard guard(mutex);\n update();\n }}\n{extra_call}\n}}"
                ),
            }]);
            let guards = collect_scoped_locksets(&files[0]);
            assert_eq!(
                guards
                    .get(&3)
                    .is_some_and(|g| g.contains(&"mutex".to_owned())),
                expected,
                "body={body}, extra_call={extra_call}, guards={guards:#?}"
            );
        }
        let files = parse_cpp_files(vec![CppFile {
            path: "argument_effect.cpp".into(),
            source: "void run() {\n auto update = [&](int value) {\n state.counter += value;\n };\n std::lock_guard guard(mutex);\n update(release_unknown());\n}".into(),
        }]);
        assert!(
            !collect_scoped_locksets(&files[0]).contains_key(&3),
            "argument evaluation may release the guard before callback entry"
        );
    }
}
