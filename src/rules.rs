use std::collections::{HashMap, HashSet};

use quote::ToTokens;
use syn::spanned::Spanned;
use syn::visit::Visit;

use crate::helpers::{is_cache_padded_type, is_whole_container_lock_type, normalize_type_name};
use crate::pattern_model::{build_pattern_context, core_predicate_holds};
use crate::rust_findings::{make_finding, with_risk_factors};
use crate::types::{
    AccessPattern, AnalysisOptions, ApiUsageEvidenceSet, AtomicAccessKind, CandidateKind,
    ColocationPattern, ConcurrencyEvidenceSet, EvidenceItem, EvidenceKind, FieldInfo, Finding,
    LayoutByteRange, LayoutCacheLineRange, LayoutContext, LayoutFieldContext, ParallelismEvidence,
    RiskCategory, Severity, StaticPatternContext, StructInfo, StructKey,
};

/// Apply struct-based rules using layout info, in-project evidence and API-usage evidence.
pub fn apply_struct_rules(
    structs: &[StructInfo],
    evidence_map: &HashMap<StructKey, ConcurrencyEvidenceSet>,
    api_usage_map: &HashMap<StructKey, ApiUsageEvidenceSet>,
    storage_topologies: &StorageTopologyIndex,
    options: &AnalysisOptions,
) -> Vec<Finding> {
    let mut findings = Vec::new();

    for si in structs {
        let key = struct_key(si);
        let evidence = evidence_map.get(&key);
        let effective_evidence =
            allocator_embedded_evidence(si, evidence, structs, evidence_map, storage_topologies);
        let api_usage = api_usage_map.get(&key);
        let evidence_descs = effective_evidence
            .as_ref()
            .map_or_else(Vec::new, ConcurrencyEvidenceSet::descriptions);

        if options.candidate_enabled(CandidateKind::FieldGroup) {
            for same_object_fields in same_object_candidate_groups(si, evidence)
                .into_iter()
                .filter(|fields| fields.len() >= 2)
            {
                let allow_symbolic_layout = !si.cache_line_groups_precise
                    && has_multiple_concurrent_writes(evidence, &same_object_fields);
                let Some(assessment) = assess_struct_field_risk(
                    si,
                    &same_object_fields,
                    evidence,
                    api_usage,
                    false,
                    allow_symbolic_layout,
                ) else {
                    continue;
                };
                let pattern = build_pattern_context(
                    Some(si),
                    CandidateKind::FieldGroup,
                    same_object_fields.clone(),
                    ColocationPattern::SameObjectFields,
                    has_strong_share_signal(si, &same_object_fields) || allow_symbolic_layout,
                    evidence,
                    api_usage,
                    false,
                    None,
                    assessment.repetition_evidence,
                    true,
                );
                if core_predicate_holds(&pattern) {
                    findings.push(with_risk_factors(
                        make_finding(
                            assessment.category,
                            CandidateKind::FieldGroup,
                            "同一对象内的独立访问位置可能共享缓存行",
                            assessment.severity,
                            &si.file,
                            si.line,
                            si.crate_name.as_deref(),
                            format!(
                                "struct {} {{ {} }}",
                                si.name,
                                same_object_fields.join(", ")
                            ),
                            "按访问主体拆分字段，或使用满足本次配置粒度的 CachePadded<T>/repr(align) 将独立写入位置隔离。",
                            assessment.confidence,
                            Some(&si.name),
                            &same_object_fields,
                            &assessment.evidence_descs,
                            evidence,
                        )
                        .with_layout_context(si)
                        .with_static_pattern(pattern),
                        assessment.risk_factors,
                    ));
                }
            }
        }

        if options.candidate_enabled(CandidateKind::ContainerElements)
            || options.candidate_enabled(CandidateKind::WriterNeighbor)
            || options.candidate_enabled(CandidateKind::ObjectInstances)
        {
            findings.extend(cache_sensitive_field_findings(
                si,
                structs,
                evidence_descs.as_slice(),
                effective_evidence.as_ref(),
                api_usage,
                storage_topologies,
                options,
            ));
        }
    }

    findings
}

/// Lift evidence from inline child records to an allocator-escaped parent.
///
/// Access collection resolves `cell.header.state` against `Header`, while the
/// placement relation is established by `Box::new(Cell { ... })`.  These are
/// the same abstract object, so the parent field must inherit the child's
/// write and cross-agent reachability witnesses before object_instances can evaluate the
/// allocator-object predicate.  The lift is deliberately restricted to an
/// allocator topology and to inline fields; an ordinary stack/nested record
/// therefore keeps the stricter direct-evidence behavior.
fn allocator_embedded_evidence(
    si: &StructInfo,
    direct: Option<&ConcurrencyEvidenceSet>,
    structs: &[StructInfo],
    evidence_map: &HashMap<StructKey, ConcurrencyEvidenceSet>,
    storage_topologies: &StorageTopologyIndex,
) -> Option<ConcurrencyEvidenceSet> {
    if !storage_topologies.allows_embedded_lift(si) {
        return direct.cloned();
    }
    let mut visited = HashSet::new();
    Some(collect_embedded_evidence(
        si,
        direct,
        structs,
        evidence_map,
        &mut visited,
    ))
}

fn collect_embedded_evidence(
    si: &StructInfo,
    direct: Option<&ConcurrencyEvidenceSet>,
    structs: &[StructInfo],
    evidence_map: &HashMap<StructKey, ConcurrencyEvidenceSet>,
    visited: &mut HashSet<StructKey>,
) -> ConcurrencyEvidenceSet {
    let key = struct_key(si);
    if !visited.insert(key.clone()) {
        return direct.cloned().unwrap_or_default();
    }
    let mut merged = direct.cloned().unwrap_or_default();
    let crate_name = si.crate_name.as_deref().unwrap_or("unknown");
    for field in &si.fields {
        if field.is_indirect || field.is_cache_padded {
            continue;
        }
        let Some(type_name) = normalize_type_name(&field.ty_str) else {
            continue;
        };
        let candidates: Vec<&StructInfo> = structs
            .iter()
            .filter(|nested| {
                nested.name == type_name
                    && nested.crate_name.as_deref().unwrap_or("unknown") == crate_name
                    && (nested.module_path == si.module_path
                        || structs
                            .iter()
                            .filter(|other| {
                                other.name == type_name
                                    && other.crate_name.as_deref().unwrap_or("unknown")
                                        == crate_name
                            })
                            .count()
                            == 1)
            })
            .collect();
        for nested in candidates {
            let nested_evidence = collect_embedded_evidence(
                nested,
                evidence_map.get(&struct_key(nested)),
                structs,
                evidence_map,
                visited,
            );
            for item in &nested_evidence.evidence {
                let mut lifted = item.clone();
                lifted.field_name = Some(field.name.clone());
                lifted.through_raw_pointer = true;
                if !lifted
                    .semantic_contexts
                    .iter()
                    .any(|context| context == "embedded_allocator_escape")
                {
                    lifted
                        .semantic_contexts
                        .push("embedded_allocator_escape".to_string());
                }
                lifted.description = format!(
                    "embedded field '{}.{}' inherits child evidence: {}",
                    field.name, type_name, item.description
                );
                merged.evidence.push(lifted);
            }
        }
    }
    visited.remove(&key);
    merged
}

fn cache_sensitive_field_findings(
    si: &StructInfo,
    structs: &[StructInfo],
    evidence_descs: &[String],
    evidence: Option<&ConcurrencyEvidenceSet>,
    api_usage: Option<&ApiUsageEvidenceSet>,
    storage_topologies: &StorageTopologyIndex,
    options: &AnalysisOptions,
) -> Vec<Finding> {
    let has_evidence = evidence.is_some_and(ConcurrencyEvidenceSet::has_evidence);
    let mut findings = Vec::new();

    if options.candidate_enabled(CandidateKind::ContainerElements)
        && let Some(field) = si.fields.iter().find(|field| {
            is_unisolated_hot_field(field)
                && contiguous_element_type(&field.ty_str).is_some()
                && !contiguous_elements_are_isolated(si, field, structs)
                && !is_whole_container_lock_type(&field.ty_str)
                && (field.is_hot_sync
                    || field.is_atomic
                    || field.ty_str.contains("Mutex")
                    || field.ty_str.contains("RwLock")
                    || field.ty_str.contains("Atomic")
                    || field.ty_str.contains("SeqLock"))
        })
        && let Some(assessment) =
            assess_container_risk(si, field, has_evidence, evidence_descs, evidence, api_usage)
    {
        let locations = vec![format!("{}[i]", field.name), format!("{}[j]", field.name)];
        let pattern = build_pattern_context(
            Some(si),
            CandidateKind::ContainerElements,
            locations,
            ColocationPattern::ContiguousElements,
            true,
            evidence,
            api_usage,
            true,
            None,
            assessment.repetition_evidence,
            true,
        );
        if core_predicate_holds(&pattern) {
            findings.push(with_risk_factors(
                make_finding(
                    assessment.category,
                    CandidateKind::ContainerElements,
                    "连续分片容器元素可能共享缓存行",
                    assessment.severity,
                    &si.file,
                    si.line,
                    si.crate_name.as_deref(),
                    format!("{}.{}: {}", si.name, field.name, field.ty_str),
                    "将连续分片元素改为满足本次配置粒度的 CachePadded<T> 或 repr(align) 包装类型，避免相邻槽位被不同线程写入时共享缓存行。",
                    assessment.confidence,
                    Some(&si.name),
                    std::slice::from_ref(&field.name),
                    &assessment.evidence_descs,
                    evidence,
                )
                .with_layout_context(si)
                .with_static_pattern(pattern),
                assessment.risk_factors,
            ));
        }
    }

    let object_alignment_fields = if storage_topologies.has_per_agent_storage(si) {
        per_agent_object_candidate_fields(si, evidence)
    } else {
        same_object_candidate_fields(si, evidence)
    };
    let object_topology = storage_topologies.object_topology(si);
    let object_access_signal = match object_topology {
        Some(ColocationPattern::AllocatorObjects) => has_allocator_escape_access(
            evidence,
            &object_alignment_fields,
            storage_topologies.allows_embedded_lift(si),
            storage_topologies.has_per_agent_storage(si),
        ),
        _ => evidence.is_some_and(has_shared_object_access),
    };
    let needs_object_alignment = object_topology.is_some()
        && !object_alignment_fields.is_empty()
        && object_access_signal
        && !same_field_object_stride_excludes_colocation(si, &object_alignment_fields);

    if options.candidate_enabled(CandidateKind::ObjectInstances)
        && !si.repr_align
        && needs_object_alignment
        && let Some(assessment) = assess_object_alignment_risk(
            si,
            &object_alignment_fields,
            has_evidence,
            evidence_descs,
            evidence,
            api_usage,
            ObjectPlacementContext {
                topology: object_topology.unwrap_or(ColocationPattern::AdjacentObjects),
                per_agent_storage: storage_topologies.has_per_agent_storage(si),
            },
        )
    {
        let representative = object_alignment_fields
            .iter()
            .find(|field| {
                container_elements_has_mutation_signal(evidence, std::slice::from_ref(field))
            })
            .cloned()
            .unwrap_or_else(|| "state".to_string());
        let locations = vec![
            format!("{}[i].{}", si.name, representative),
            format!("{}[j].{}", si.name, representative),
        ];
        let mut pattern = build_pattern_context(
            Some(si),
            CandidateKind::ObjectInstances,
            locations,
            object_topology.unwrap_or(ColocationPattern::AdjacentObjects),
            true,
            evidence,
            api_usage,
            container_elements_has_mutation_signal(evidence, &object_alignment_fields),
            storage_topologies
                .has_per_agent_storage(si)
                .then_some(ParallelismEvidence::SharedReachability),
            assessment.repetition_evidence,
            true,
        );
        pattern.access_pattern = AccessPattern::WriteWrite;
        if core_predicate_holds(&pattern) {
            findings.push(with_risk_factors(
                make_finding(
                    assessment.category,
                    CandidateKind::ObjectInstances,
                    "连续存储的热点对象实例可能跨对象共享缓存行",
                    assessment.severity,
                    &si.file,
                    si.line,
                    si.crate_name.as_deref(),
                    format!(
                        "struct {} {{ {} }}",
                        si.name,
                        object_alignment_fields.join(", ")
                    ),
                    "对连续存储的元素类型使用满足本次配置粒度的 repr(align) 或 CachePadded，确保对象 stride 提供缓存行隔离。",
                    assessment.confidence,
                    Some(&si.name),
                    &object_alignment_fields,
                    &assessment.evidence_descs,
                    evidence,
                )
                .with_layout_context(si)
                .with_static_pattern(pattern),
                assessment.risk_factors,
            ));
        }
    }

    let unisolated_atomic_fields: Vec<String> = si
        .fields
        .iter()
        .filter(|field| field.is_atomic && is_unisolated_hot_field(field))
        .map(|field| field.name.clone())
        .collect();
    let single_field_risk = unisolated_atomic_fields.len() == 1
        && has_neighbor_payload(si, &unisolated_atomic_fields[0])
        && container_elements_has_mutation_signal(evidence, &unisolated_atomic_fields)
        && (has_evidence || api_usage.is_some_and(ApiUsageEvidenceSet::has_usage_signal));

    if options.candidate_enabled(CandidateKind::WriterNeighbor) && single_field_risk {
        let field = unisolated_atomic_fields[0].clone();
        for neighbor in unisolated_neighbors(si, &field) {
            let assessment =
                assess_single_field_risk(si, &field, evidence_descs, evidence, api_usage);
            let pair = vec![field.clone(), neighbor.clone()];
            let pattern = build_pattern_context(
                Some(si),
                CandidateKind::WriterNeighbor,
                pair.clone(),
                ColocationPattern::SameObjectFields,
                true,
                evidence,
                api_usage,
                false,
                None,
                assessment.repetition_evidence,
                true,
            );
            if core_predicate_holds(&pattern) {
                findings.push(with_risk_factors(
                make_finding(
                    assessment.category,
                    CandidateKind::WriterNeighbor,
                    "单个写热点可能与邻接位置共享缓存行",
                    assessment.severity,
                    &si.file,
                    si.line,
                    si.crate_name.as_deref(),
                    format!("struct {} {{ {} }}", si.name, pair.join(", ")),
                    "对写热点使用 CachePadded<T>，或将其移动到独立缓存行，避免与邻接读写位置发生缓存行干扰。",
                    assessment.confidence,
                    Some(&si.name),
                    &pair,
                    &assessment.evidence_descs,
                    evidence,
                )
                .with_layout_context(si)
                .with_static_pattern(pattern),
                assessment.risk_factors,
            ));
            }
        }
    }

    findings
}

/// Apply file-level rules that don't need cross-file evidence.
pub fn apply_file_rules(
    source: &str,
    file_path: &str,
    ast: &syn::File,
    crate_name: Option<&str>,
    options: &AnalysisOptions,
) -> Vec<Finding> {
    let mut findings = apply_file_rules_with_accessors(
        source,
        file_path,
        ast,
        crate_name,
        options,
        &HashMap::new(),
    );
    let file = crate::types::ParsedFile {
        path: file_path.into(),
        module_path: String::new(),
        source: source.into(),
        ast: ast.clone(),
        crate_name: crate_name.map(str::to_string),
    };
    let mut structs =
        crate::struct_layout::collect_structs_from_file(&file, options.cache_line_size);
    crate::struct_layout::enrich_structs_with_type_registry(&mut structs, options.cache_line_size);
    findings.extend(crate::rust_statics::collect_findings(
        &[file],
        &structs,
        options,
    ));
    findings
}

/// Discover index-preserving reference accessors from native slice/array bodies.
/// The method's spelling is irrelevant; both conditional returns must select
/// the same caller-supplied index from `self`.
pub(crate) fn collect_indexed_accessors(
    files: &[crate::types::ParsedFile],
) -> HashMap<String, usize> {
    fn tail(block: &syn::Block) -> Option<&syn::Expr> {
        match block.stmts.as_slice() {
            [syn::Stmt::Expr(expr, _)] => Some(expr),
            _ => None,
        }
    }
    fn selector(expr: &syn::Expr, parameters: &[String]) -> Option<usize> {
        let parameter = |expr: &syn::Expr| match expr {
            syn::Expr::Path(path) if path.path.segments.len() == 1 => parameters
                .iter()
                .position(|parameter| path.path.is_ident(parameter)),
            _ => None,
        };
        match expr {
            syn::Expr::Reference(reference) => selector(&reference.expr, parameters),
            syn::Expr::Paren(paren) => selector(&paren.expr, parameters),
            syn::Expr::Return(returned) => selector(returned.expr.as_deref()?, parameters),
            syn::Expr::Block(block) => selector(tail(&block.block)?, parameters),
            syn::Expr::Unsafe(block) => selector(tail(&block.block)?, parameters),
            syn::Expr::Index(index) if matches!(&*index.expr, syn::Expr::Path(path) if path.path.is_ident("self")) => {
                parameter(&index.index)
            }
            syn::Expr::MethodCall(call)
                if matches!(
                    call.method.to_string().as_str(),
                    "get" | "get_mut" | "get_unchecked" | "get_unchecked_mut"
                ) && matches!(&*call.receiver, syn::Expr::Path(path) if path.path.is_ident("self")) =>
            {
                parameter(call.args.first()?)
            }
            syn::Expr::MethodCall(call)
                if matches!(call.method.to_string().as_str(), "unwrap" | "expect") =>
            {
                selector(&call.receiver, parameters)
            }
            syn::Expr::If(branch)
                if matches!(&*branch.cond, syn::Expr::Macro(expr) if expr.mac.path.is_ident("cfg"))
                    || matches!(
                        &*branch.cond,
                        syn::Expr::Lit(syn::ExprLit {
                            lit: syn::Lit::Bool(_),
                            ..
                        })
                    ) =>
            {
                let left = selector(tail(&branch.then_branch)?, parameters)?;
                (selector(&branch.else_branch.as_ref()?.1, parameters)? == left).then_some(left)
            }
            _ => None,
        }
    }
    struct Collector<'a>(&'a mut HashMap<String, Option<usize>>);
    impl<'ast> Visit<'ast> for Collector<'_> {
        fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
            if !matches!(&*item.self_ty, syn::Type::Slice(_) | syn::Type::Array(_)) {
                return;
            }
            for method in &item.items {
                let syn::ImplItem::Fn(method) = method else {
                    continue;
                };
                if !matches!(&method.sig.output, syn::ReturnType::Type(_, ty) if matches!(&**ty, syn::Type::Reference(_)))
                {
                    continue;
                }
                let parameters: Option<Vec<_>> = method
                    .sig
                    .inputs
                    .iter()
                    .filter_map(|argument| match argument {
                        syn::FnArg::Typed(argument) => Some(&*argument.pat),
                        _ => None,
                    })
                    .map(|pattern| match pattern {
                        syn::Pat::Ident(ident) => Some(ident.ident.to_string()),
                        _ => None,
                    })
                    .collect();
                let result = parameters.and_then(|parameters| {
                    tail(&method.block).and_then(|expr| selector(expr, &parameters))
                });
                self.0
                    .entry(method.sig.ident.to_string())
                    .and_modify(|existing| {
                        if *existing != result {
                            *existing = None;
                        }
                    })
                    .or_insert(result);
            }
        }
    }
    let mut summaries = HashMap::new();
    for file in files {
        Collector(&mut summaries).visit_file(&file.ast);
    }
    summaries
        .into_iter()
        .filter_map(|(name, index)| index.map(|index| (name, index)))
        .collect()
}

pub(crate) fn apply_file_rules_with_accessors(
    _source: &str,
    file_path: &str,
    ast: &syn::File,
    crate_name: Option<&str>,
    options: &AnalysisOptions,
    accessors: &HashMap<String, usize>,
) -> Vec<Finding> {
    let mut findings = Vec::new();

    if options.candidate_enabled(CandidateKind::IndexedWrites)
        && !options.ablated(crate::types::AblationComponent::Write)
        && !options.ablated(crate::types::AblationComponent::MayParallel)
    {
        let mut visitor = ParallelIndexedWriteVisitor {
            cache_line_size: options.cache_line_size,
            indexed_accessors: accessors.clone(),
            ..Default::default()
        };
        visitor.collect_imports(ast);
        visitor.collect_element_alignments(ast);
        syn::visit::visit_file(&mut visitor, ast);
        for matched in &visitor.matches {
            let logical_locations: Vec<String> = matched.logical_location.iter().cloned().collect();
            let witness_locations = logical_locations
                .iter()
                .flat_map(|location| [format!("{location}[i]"), format!("{location}[j]")])
                .collect();
            let mut pattern = build_pattern_context(
                None,
                CandidateKind::IndexedWrites,
                if logical_locations.is_empty() {
                    vec!["indexed[i]".to_string(), "indexed[j]".to_string()]
                } else {
                    witness_locations
                },
                ColocationPattern::ContiguousElements,
                true,
                None,
                None,
                true,
                Some(ParallelismEvidence::ConcurrentContext),
                true,
                true,
            );
            pattern.access_pattern = AccessPattern::WriteWrite;
            if core_predicate_holds(&pattern) {
                findings.push(
                    make_finding(
                        RiskCategory::ColdOrConditional,
                        CandidateKind::IndexedWrites,
                        "并行索引写入的不同元素可能共享缓存行",
                        Severity::Medium,
                        file_path,
                        matched.line,
                        crate_name,
                        matched.snippet.clone(),
                        "改为每线程局部缓冲并 reduce，或确保不同线程写入的相邻元素使用 CachePadded/repr(align) 隔离。",
                        0.45,
                        None,
                        &logical_locations,
                        &[],
                        None,
                    )
                    .with_static_pattern(pattern),
                );
                if let Some(line) = matched.declaration_line {
                    findings.last_mut().unwrap().storage_identity = Some(format!(
                        "{file_path}::{}@{line}",
                        logical_locations.join("+")
                    ));
                }
            }
        }
    }

    findings
}

#[derive(Clone)]
struct RiskAssessment {
    category: RiskCategory,
    severity: Severity,
    confidence: f32,
    repetition_evidence: bool,
    risk_factors: Vec<String>,
    evidence_descs: Vec<String>,
}

#[derive(Clone, Copy)]
struct ObjectPlacementContext {
    topology: ColocationPattern,
    per_agent_storage: bool,
}

fn assess_struct_field_risk(
    si: &StructInfo,
    field_names: &[String],
    evidence: Option<&ConcurrencyEvidenceSet>,
    api_usage: Option<&ApiUsageEvidenceSet>,
    allow_single_hot_field: bool,
    allow_symbolic_layout: bool,
) -> Option<RiskAssessment> {
    let strong_layout = if allow_single_hot_field && field_names.len() == 1 {
        has_neighbor_payload(si, &field_names[0])
            || si
                .total_estimated_size
                .map(|size| size <= si.cache_line_size)
                .unwrap_or(false)
    } else {
        has_strong_share_signal(si, field_names)
    };
    let api_usage_signal = api_usage.is_some_and(ApiUsageEvidenceSet::has_usage_signal);

    if !strong_layout && !allow_single_hot_field && !allow_symbolic_layout {
        return None;
    }

    let summary = candidate_summary(evidence, field_names);
    let written_fields = &summary.written_fields;
    let concurrent_written_fields = &summary.concurrent_written_fields;
    let hot_written_fields = &summary.hot_written_fields;
    let read_only_fields = &summary.read_fields;
    let total_hotness = summary.total_hotness;
    let max_hotness = summary.max_hotness;
    let has_concurrency = summary.has_concurrency;
    let has_strong_parallel = summary.has_strong_parallel;
    let has_shared_ownership = summary.has_shared_ownership;
    let lock_protected = summary.lock_protected;
    let likely_true_sharing = summary.likely_true_sharing;
    let ownership_partitioned = summary.ownership_partitioned;
    let exclusive_plain_writes_only = summary.exclusive_plain_writes_only;
    let shared_or_concurrent_writes = summary.shared_or_concurrent_writes;
    let independent_accesses = has_independent_shared_methods(evidence, field_names);
    let candidate_set: HashSet<&str> = field_names.iter().map(String::as_str).collect();
    let relevant_accesses: Vec<&EvidenceItem> = evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .filter(|item| {
            item.field_name
                .as_deref()
                .is_some_and(|field| candidate_set.contains(field))
        })
        .collect();
    let read_mostly =
        written_fields.is_empty() && !read_only_fields.is_empty() && !api_usage_signal;

    // A task may execute concurrently with other tasks while still owning its
    // value exclusively.  For same-object fields, Rust-safe exclusive writes
    // cannot overlap on one instance; cross-object adjacency is handled by
    // object_instances and must not be inferred by weakening this ownership fact.
    let exclusively_owned_same_object = !relevant_accesses.is_empty()
        && relevant_accesses
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .count()
            > 0
        && relevant_accesses
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .all(|item| {
                // The final Rust reference capability dominates a coarser
                // caller/path summary: obtaining `&mut T` (including a lock
                // guard dereference or an owned clone passed into a task)
                // excludes simultaneous safe access to that same T.  Raw
                // pointers remain unknown because they can bypass this fact.
                item.access_mode.is_exclusive() && !item.through_raw_pointer
            });
    if exclusively_owned_same_object {
        return None;
    }
    if lock_protected && concurrent_written_fields.is_empty() {
        return None;
    }
    if likely_true_sharing && !independent_accesses && (!has_strong_parallel || si.has_cache_padded)
    {
        return None;
    }
    if exclusive_plain_writes_only && !shared_or_concurrent_writes && !independent_accesses {
        return None;
    }
    if ownership_partitioned && !independent_accesses {
        return None;
    }
    if read_mostly {
        return None;
    }
    if written_fields.is_empty()
        && concurrent_written_fields.is_empty()
        && hot_written_fields.is_empty()
        && !api_usage_signal
        && !has_concurrency
    {
        return None;
    }

    let mut risk_factors = Vec::new();
    let mut evidence_descs = evidence.map_or_else(Vec::new, ConcurrencyEvidenceSet::descriptions);
    let api_descs = api_usage.map_or_else(Vec::new, ApiUsageEvidenceSet::descriptions);

    if strong_layout {
        risk_factors.push("布局证据: 多个热点位置可能落在同一缓存行".to_string());
    } else if allow_symbolic_layout {
        risk_factors.push(
            "布局证据: 异构热点字段未隔离；类型大小未知，按 symbolic may-share 降级".to_string(),
        );
    } else {
        risk_factors
            .push("布局证据: 单热点字段可能与邻接 payload 或相邻对象共享缓存行".to_string());
    }
    if !written_fields.is_empty() {
        risk_factors.push(format!(
            "访问证据: 检测到热点字段写入 ({})",
            sorted_names(written_fields).join(", ")
        ));
    }
    if !concurrent_written_fields.is_empty() {
        risk_factors.push(format!(
            "并发证据: 并发上下文中写入 ({})",
            sorted_names(concurrent_written_fields).join(", ")
        ));
    } else if has_strong_parallel {
        risk_factors.push("并发证据: 类型在 spawn/scope/par_iter 等上下文中使用".to_string());
    } else if has_shared_ownership {
        risk_factors.push("并发证据: 类型经 Arc 共享，可能跨线程使用".to_string());
    }
    if max_hotness > 5.0 {
        risk_factors.push(format!(
            "热度证据: 循环/重复访问最高热度 {:.1}",
            max_hotness
        ));
        evidence_descs.push(format!("高热度访问 (total score: {:.1})", total_hotness));
    }
    if api_usage_signal {
        risk_factors.push(
            "API 使用启发: 公开 API 的签名/命名暗示外部正常使用可能触发高频并发访问".to_string(),
        );
        evidence_descs.extend(api_descs);
    }
    if independent_accesses {
        risk_factors.push(
            "访问分离证据: 不同共享接收者方法分别访问独立字段，排除仅有同一操作共同更新的形状"
                .to_string(),
        );
    }
    if let Some(max_depth) = relevant_accesses
        .iter()
        .map(|item| item.propagation_depth)
        .max()
        .filter(|depth| *depth > 0)
    {
        risk_factors.push(format!(
            "过程间证据: 同 crate 函数摘要沿调用链传播，最大深度 {max_depth}"
        ));
    }
    if relevant_accesses.iter().any(|item| {
        item.semantic_contexts.iter().any(|context| {
            matches!(
                context.as_str(),
                "clone_impl" | "drop_impl" | "handle_lifecycle"
            )
        })
    }) {
        risk_factors.push("生命周期证据: Clone/Drop/handle 操作触达共享状态".to_string());
    }
    if relevant_accesses.iter().any(|item| {
        item.semantic_contexts
            .iter()
            .any(|context| matches!(context.as_str(), "trait_impl" | "generic"))
    }) {
        risk_factors.push("泛化证据: 访问来自 trait impl 或泛型实现".to_string());
    }
    if relevant_accesses.iter().any(|item| {
        item.semantic_contexts
            .iter()
            .any(|context| matches!(context.as_str(), "async_fn" | "async_block"))
    }) {
        risk_factors.push("异步证据: 访问位于 async 函数/块，并由并发入口决定是否重叠".to_string());
    }
    if relevant_accesses
        .iter()
        .any(|item| item.through_raw_pointer)
    {
        risk_factors
            .push("指针证据: 访问经过 unsafe/raw pointer，所有权按 unknown 保守处理".to_string());
    }

    let has_multi_field_write = concurrent_written_fields.len() >= 2
        || (written_fields.len() >= 2 && has_concurrency)
        || (hot_written_fields.len() >= 2 && has_shared_ownership);
    let category = if strong_layout
        && has_multi_field_write
        && has_concurrency
        && !lock_protected
        && !likely_true_sharing
    {
        RiskCategory::HotInProject
    } else if (strong_layout || allow_symbolic_layout) && api_usage_signal {
        RiskCategory::ApiUsageLatent
    } else if !written_fields.is_empty()
        || !concurrent_written_fields.is_empty()
        || !hot_written_fields.is_empty()
        || has_concurrency
    {
        RiskCategory::ColdOrConditional
    } else {
        return None;
    };

    let mut confidence: f32 = if strong_layout {
        0.48
    } else if allow_symbolic_layout {
        0.40
    } else {
        0.36
    };
    if !written_fields.is_empty() {
        confidence += 0.10;
    }
    if written_fields.len() >= 2 {
        confidence += 0.10;
    }
    if has_shared_ownership {
        confidence += 0.08;
    }
    if has_strong_parallel {
        confidence += 0.12;
    }
    if concurrent_written_fields.len() >= 2 {
        confidence += 0.12;
    }
    if max_hotness > 5.0 {
        confidence += 0.08;
    }
    if api_usage_signal {
        confidence += api_usage
            .map_or(0.0, ApiUsageEvidenceSet::max_score)
            .min(0.16);
    }
    if category == RiskCategory::HotInProject {
        confidence = confidence.max(0.80);
    }
    if category == RiskCategory::ApiUsageLatent {
        confidence = confidence.clamp(0.62, 0.82);
    }

    Some(RiskAssessment {
        category,
        severity: if max_hotness > 5.0
            || concurrent_written_fields.len() >= 2
            || has_multi_field_write
        {
            Severity::High
        } else {
            Severity::Medium
        },
        confidence: confidence.clamp(0.30, 0.95),
        repetition_evidence: max_hotness > 1.0 || independent_accesses,
        risk_factors,
        evidence_descs,
    })
}

fn candidate_summary(
    evidence: Option<&ConcurrencyEvidenceSet>,
    field_names: &[String],
) -> crate::types::CandidateEvidenceSummary {
    evidence
        .map(|evidence| evidence.summarize_for_candidates(field_names, 5.0))
        .unwrap_or_default()
}

fn container_elements_has_mutation_signal(
    evidence: Option<&ConcurrencyEvidenceSet>,
    field_names: &[String],
) -> bool {
    let summary = candidate_summary(evidence, field_names);
    !summary.written_fields.is_empty()
        || !summary.concurrent_written_fields.is_empty()
        || !summary.hot_written_fields.is_empty()
}

fn has_multiple_concurrent_writes(
    evidence: Option<&ConcurrencyEvidenceSet>,
    fields: &[String],
) -> bool {
    let candidates: HashSet<&str> = fields.iter().map(String::as_str).collect();
    evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .filter(|item| item.in_concurrent_context)
        .filter(|item| {
            matches!(
                item.access_kind,
                Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
            )
        })
        .filter_map(|item| item.field_name.as_deref())
        .filter(|field| candidates.contains(field))
        .collect::<HashSet<_>>()
        .len()
        >= 2
}

/// Enumerate the write-capable or actually accessed abstract locations in one
/// object, then retain one cache-line-equivalence class.  This is the complete
/// field_group candidate set relative to the recovered field and layout abstractions;
/// it does not depend on record, field, project, or PR names.
fn same_object_candidate_fields(
    si: &StructInfo,
    evidence: Option<&ConcurrencyEvidenceSet>,
) -> Vec<String> {
    same_object_candidate_groups(si, evidence)
        .into_iter()
        .max_by_key(Vec::len)
        .unwrap_or_default()
}

fn per_agent_object_candidate_fields(
    si: &StructInfo,
    evidence: Option<&ConcurrencyEvidenceSet>,
) -> Vec<String> {
    let declared: HashSet<&str> = si
        .fields
        .iter()
        .filter(|field| !field.is_cache_padded && !field.is_manual_padding)
        .map(|field| field.name.as_str())
        .collect();
    let mut accessed: Vec<String> = evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        // Neighboring per-agent objects can also interfere through reads.
        // The separate mutation gate and representative still require a write.
        .filter(|item| item.access_kind.is_some())
        .filter_map(|item| item.field_name.clone())
        .filter(|field| declared.contains(field.as_str()))
        .collect();
    accessed.sort();
    accessed.dedup();
    accessed
}

fn same_object_candidate_groups(
    si: &StructInfo,
    evidence: Option<&ConcurrencyEvidenceSet>,
) -> Vec<Vec<String>> {
    let accessed: HashSet<String> = evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .filter(|item| item.access_kind.is_some())
        .filter_map(|item| item.field_name.clone())
        .collect();
    let candidates: HashSet<String> = si
        .fields
        .iter()
        .filter(|field| is_unisolated_hot_field(field))
        .filter(|field| !field.is_indirect)
        .filter(|field| !is_whole_container_lock_type(&field.ty_str))
        .filter(|field| {
            field.is_atomic
                || field.is_hot_sync
                || ((field.is_hot_scalar || accessed.contains(&field.name))
                    && accessed.contains(&field.name))
        })
        .map(|field| field.name.clone())
        .collect();

    if candidates.is_empty() {
        return Vec::new();
    }

    if si.cache_line_groups_precise {
        let mut groups: Vec<Vec<String>> = si
            .cache_line_groups
            .iter()
            .map(|group| {
                group
                    .iter()
                    .filter(|field| candidates.contains(*field))
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .filter(|group| !group.is_empty())
            .collect();
        groups.sort();
        groups.dedup();
        return groups;
    }

    vec![
        si.fields
            .iter()
            .filter(|field| candidates.contains(&field.name))
            .map(|field| field.name.clone())
            .collect(),
    ]
}

#[derive(Clone, Debug, Default)]
pub struct StorageTopologyIndex {
    contiguous_types: HashSet<StructKey>,
    allocator_types: HashSet<StructKey>,
    erased_allocator_types: HashSet<StructKey>,
    per_agent_types: HashSet<StructKey>,
}

impl StorageTopologyIndex {
    fn object_topology(&self, si: &StructInfo) -> Option<ColocationPattern> {
        let key = StructKey::from_struct(si);
        if self.contiguous_types.contains(&key) {
            Some(ColocationPattern::AdjacentObjects)
        } else if self.allocator_types.contains(&key) {
            Some(ColocationPattern::AllocatorObjects)
        } else {
            None
        }
    }

    fn allows_embedded_lift(&self, si: &StructInfo) -> bool {
        self.erased_allocator_types
            .contains(&StructKey::from_struct(si))
    }

    fn has_per_agent_storage(&self, si: &StructInfo) -> bool {
        self.per_agent_types.contains(&StructKey::from_struct(si))
    }
}

/// Recover object-placement relationships without relying on record names.
/// Language-level arrays/slices establish exact adjacency classes; repeated
/// Box/Arc/Owned allocation establishes the weaker allocator-slot topology.
pub fn collect_storage_topologies(
    files: &[crate::types::ParsedFile],
    structs: &[StructInfo],
) -> StorageTopologyIndex {
    let by_name: HashMap<&str, Vec<StructKey>> =
        structs.iter().fold(HashMap::new(), |mut index, si| {
            index
                .entry(si.name.as_str())
                .or_default()
                .push(StructKey::from_struct(si));
            index
        });
    let mut index = StorageTopologyIndex::default();
    for si in structs {
        for field in &si.fields {
            if let Some(element) = contiguous_element_type(&field.ty_str) {
                add_unique_type_relation(&mut index.contiguous_types, &by_name, &element);
            }
        }
    }
    for file in files {
        let mut visitor = AllocationTopologyVisitor {
            by_name: &by_name,
            allocator_types: &mut index.allocator_types,
            erased_allocator_types: &mut index.erased_allocator_types,
        };
        syn::visit::visit_file(&mut visitor, &file.ast);
        let agent_parameters = collect_repeated_call_parameters(&file.ast);
        let mut per_agent = PerAgentStorageVisitor::new(
            &by_name,
            &file.module_path,
            &agent_parameters,
            &mut index.allocator_types,
            &mut index.erased_allocator_types,
            &mut index.per_agent_types,
        );
        syn::visit::visit_file(&mut per_agent, &file.ast);
    }
    index
}

fn add_unique_type_relation(
    output: &mut HashSet<StructKey>,
    by_name: &HashMap<&str, Vec<StructKey>>,
    type_name: &str,
) {
    if let Some(keys) = by_name.get(type_name)
        && keys.len() == 1
    {
        output.insert(keys[0].clone());
    }
}

fn add_scoped_type_relation(
    output: &mut HashSet<StructKey>,
    by_name: &HashMap<&str, Vec<StructKey>>,
    module_path: &str,
    type_name: &str,
) {
    let Some(keys) = by_name.get(type_name) else {
        return;
    };
    if let Some(exact) = keys.iter().find(|key| key.module_path == module_path) {
        output.insert(exact.clone());
    } else if keys.len() == 1 {
        output.insert(keys[0].clone());
    } else {
        let mut ranked: Vec<_> = keys
            .iter()
            .map(|key| {
                let common_prefix = key
                    .module_path
                    .split("::")
                    .zip(module_path.split("::"))
                    .take_while(|(left, right)| left == right)
                    .count();
                (common_prefix, key)
            })
            .collect();
        ranked.sort_by_key(|(prefix, _)| std::cmp::Reverse(*prefix));
        if ranked.first().is_some_and(|(prefix, _)| {
            *prefix > 0
                && ranked
                    .get(1)
                    .is_none_or(|(next_prefix, _)| next_prefix < prefix)
        }) {
            output.insert(ranked[0].1.clone());
        }
    }
}

struct AllocationTopologyVisitor<'a> {
    by_name: &'a HashMap<&'a str, Vec<StructKey>>,
    allocator_types: &'a mut HashSet<StructKey>,
    erased_allocator_types: &'a mut HashSet<StructKey>,
}

impl syn::visit::Visit<'_> for AllocationTopologyVisitor<'_> {
    fn visit_expr_call(&mut self, node: &syn::ExprCall) {
        if allocator_constructor(&node.func) {
            for argument in &node.args {
                if let Some(type_name) = allocated_type_name(argument) {
                    add_unique_type_relation(self.allocator_types, self.by_name, &type_name);
                }
            }
        }
        if raw_box_escape(&node.func) {
            for argument in &node.args {
                if let Some(type_name) = escaped_allocated_type_name(argument) {
                    add_unique_type_relation(self.allocator_types, self.by_name, &type_name);
                    add_unique_type_relation(self.erased_allocator_types, self.by_name, &type_name);
                }
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &syn::ExprMethodCall) {
        if node.method == "into_shared"
            && let Some(type_name) = allocator_expression_type(&node.receiver)
        {
            add_unique_type_relation(self.allocator_types, self.by_name, &type_name);
            add_unique_type_relation(self.erased_allocator_types, self.by_name, &type_name);
        }
        syn::visit::visit_expr_method_call(self, node);
    }
}

/// Recover formal parameters that receive a symbolic iteration/closure value.
/// This is a bounded call-site summary used by the per-agent points-to pass:
/// ordinary function parameters are not treated as agent identities merely
/// because they are parameters.
fn collect_repeated_call_parameters(file: &syn::File) -> HashMap<String, HashSet<usize>> {
    #[derive(Default)]
    struct Collector {
        agent_scopes: Vec<HashSet<String>>,
        parameters: HashMap<String, HashSet<usize>>,
    }

    impl Collector {
        fn enter_scope(&mut self) {
            self.agent_scopes.push(HashSet::new());
        }

        fn leave_scope(&mut self) {
            self.agent_scopes.pop();
        }

        fn declare(&mut self, pattern: &syn::Pat) {
            let mut names = Vec::new();
            collect_pattern_names(pattern, &mut names);
            if let Some(scope) = self.agent_scopes.last_mut() {
                scope.extend(names);
            }
        }

        fn depends_on_agent(&self, expression: &syn::Expr) -> bool {
            expression_identifiers(expression).iter().any(|name| {
                self.agent_scopes
                    .iter()
                    .rev()
                    .any(|scope| scope.contains(name))
            })
        }
    }

    impl<'ast> syn::visit::Visit<'ast> for Collector {
        fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
            if crate::helpers::cfg_is_test_only(&node.attrs) {
                return;
            }
            self.enter_scope();
            self.visit_block(&node.block);
            self.leave_scope();
        }

        fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
            if crate::helpers::cfg_is_test_only(&node.attrs) {
                return;
            }
            self.enter_scope();
            self.visit_block(&node.block);
            self.leave_scope();
        }

        fn visit_block(&mut self, node: &'ast syn::Block) {
            self.enter_scope();
            syn::visit::visit_block(self, node);
            self.leave_scope();
        }

        fn visit_local(&mut self, node: &'ast syn::Local) {
            if let Some(init) = &node.init
                && self.depends_on_agent(&init.expr)
            {
                self.declare(&node.pat);
            }
            syn::visit::visit_local(self, node);
        }

        fn visit_expr_for_loop(&mut self, node: &'ast syn::ExprForLoop) {
            self.visit_expr(&node.expr);
            self.enter_scope();
            self.declare(&node.pat);
            self.visit_block(&node.body);
            self.leave_scope();
        }

        fn visit_expr_closure(&mut self, node: &'ast syn::ExprClosure) {
            self.enter_scope();
            for input in &node.inputs {
                self.declare(input);
            }
            self.visit_expr(&node.body);
            self.leave_scope();
        }

        fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
            if let syn::Expr::Path(path) = node.func.as_ref()
                && let Some(name) = path
                    .path
                    .segments
                    .last()
                    .map(|segment| segment.ident.to_string())
            {
                for (index, argument) in node.args.iter().enumerate() {
                    if self.depends_on_agent(argument) {
                        self.parameters
                            .entry(name.clone())
                            .or_default()
                            .insert(index);
                    }
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
    }

    let mut collector = Collector::default();
    collector.visit_file(file);
    collector.parameters
}

#[derive(Clone, Debug)]
struct AllocatedBinding {
    type_name: String,
    agent_dependent: bool,
    raw_pointer: bool,
}

/// Flow-sensitive, function-local may-points-to analysis for allocated values.
///
/// The analysis does not attach semantics to project/type/field names.  It
/// follows allocation identities through locals, references, casts and
/// `Box::into_raw`, then recognizes two language-level per-agent escape forms:
/// an agent-keyed storage insertion and a raw pointer written to non-local
/// storage.  The latter additionally requires the allocation value to depend
/// on a function/loop/closure agent variable.
struct PerAgentStorageVisitor<'a> {
    by_name: &'a HashMap<&'a str, Vec<StructKey>>,
    module_path: &'a str,
    agent_parameters: &'a HashMap<String, HashSet<usize>>,
    allocator_types: &'a mut HashSet<StructKey>,
    erased_allocator_types: &'a mut HashSet<StructKey>,
    per_agent_types: &'a mut HashSet<StructKey>,
    scopes: Vec<HashMap<String, AllocatedBinding>>,
    agent_scopes: Vec<HashSet<String>>,
    repetition_depth: usize,
    parallel_depth: usize,
}

impl<'a> PerAgentStorageVisitor<'a> {
    fn new(
        by_name: &'a HashMap<&'a str, Vec<StructKey>>,
        module_path: &'a str,
        agent_parameters: &'a HashMap<String, HashSet<usize>>,
        allocator_types: &'a mut HashSet<StructKey>,
        erased_allocator_types: &'a mut HashSet<StructKey>,
        per_agent_types: &'a mut HashSet<StructKey>,
    ) -> Self {
        Self {
            by_name,
            module_path,
            agent_parameters,
            allocator_types,
            erased_allocator_types,
            per_agent_types,
            scopes: vec![HashMap::new()],
            agent_scopes: vec![HashSet::new()],
            repetition_depth: 0,
            parallel_depth: 0,
        }
    }

    fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.agent_scopes.push(HashSet::new());
    }

    fn leave_scope(&mut self) {
        self.scopes.pop();
        self.agent_scopes.pop();
    }

    fn bind(&mut self, name: String, binding: AllocatedBinding) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, binding);
        }
    }

    fn lookup(&self, name: &str) -> Option<AllocatedBinding> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn declare_agents(&mut self, pattern: &syn::Pat) {
        let mut names = Vec::new();
        collect_pattern_names(pattern, &mut names);
        if let Some(scope) = self.agent_scopes.last_mut() {
            scope.extend(names);
        }
    }

    fn declare_agent_parameters(
        &mut self,
        function_name: &str,
        inputs: &syn::punctuated::Punctuated<syn::FnArg, syn::Token![,]>,
    ) {
        let Some(indexes) = self.agent_parameters.get(function_name).cloned() else {
            return;
        };
        let mut parameter_index = 0usize;
        for input in inputs {
            if let syn::FnArg::Typed(typed) = input {
                if indexes.contains(&parameter_index) {
                    self.declare_agents(&typed.pat);
                }
                parameter_index += 1;
            }
        }
    }

    fn is_agent_name(&self, name: &str) -> bool {
        self.agent_scopes
            .iter()
            .rev()
            .any(|scope| scope.contains(name))
    }

    fn expression_mentions_agent(&self, expression: &syn::Expr) -> bool {
        expression_identifiers(expression)
            .iter()
            .any(|name| self.is_agent_name(name))
    }

    fn binding_from_expr(&self, expression: &syn::Expr) -> Option<AllocatedBinding> {
        match expression {
            syn::Expr::Path(path) => self.lookup(&path.path.segments.last()?.ident.to_string()),
            syn::Expr::Reference(reference) => self.binding_from_expr(&reference.expr),
            syn::Expr::Unary(unary) => self.binding_from_expr(&unary.expr),
            syn::Expr::Paren(paren) => self.binding_from_expr(&paren.expr),
            syn::Expr::Group(group) => self.binding_from_expr(&group.expr),
            syn::Expr::Cast(cast) => self.binding_from_expr(&cast.expr).map(|mut binding| {
                binding.raw_pointer = true;
                binding
            }),
            syn::Expr::Call(call) if raw_box_escape(&call.func) => call
                .args
                .first()
                .and_then(|argument| self.binding_from_expr(argument))
                .map(|mut binding| {
                    binding.raw_pointer = true;
                    binding
                }),
            syn::Expr::Call(call) if allocator_constructor(&call.func) => {
                let argument = call.args.first()?;
                let type_name = allocated_type_name(argument)?;
                Some(AllocatedBinding {
                    type_name,
                    agent_dependent: self.expression_mentions_agent(argument)
                        || self.repetition_depth > 0,
                    raw_pointer: false,
                })
            }
            syn::Expr::MethodCall(method)
                if matches!(
                    method.method.to_string().as_str(),
                    "clone" | "as_ptr" | "as_mut_ptr"
                ) =>
            {
                self.binding_from_expr(&method.receiver).map(|mut binding| {
                    if method.method != "clone" {
                        binding.raw_pointer = true;
                    }
                    binding
                })
            }
            _ => None,
        }
    }

    fn mark_per_agent(&mut self, binding: &AllocatedBinding) {
        add_scoped_type_relation(
            self.allocator_types,
            self.by_name,
            self.module_path,
            &binding.type_name,
        );
        add_scoped_type_relation(
            self.erased_allocator_types,
            self.by_name,
            self.module_path,
            &binding.type_name,
        );
        add_scoped_type_relation(
            self.per_agent_types,
            self.by_name,
            self.module_path,
            &binding.type_name,
        );
    }

    fn non_local_destination(&self, expression: &syn::Expr) -> bool {
        expression_identifiers(expression)
            .first()
            .is_some_and(|root| self.lookup(root).is_none() && !self.is_agent_name(root))
    }

    fn expression_has_parallel_source(expression: &syn::Expr) -> bool {
        match expression {
            syn::Expr::MethodCall(method) => {
                matches!(
                    method.method.to_string().as_str(),
                    "par_iter" | "par_iter_mut" | "into_par_iter"
                ) || Self::expression_has_parallel_source(&method.receiver)
            }
            syn::Expr::Paren(paren) => Self::expression_has_parallel_source(&paren.expr),
            syn::Expr::Reference(reference) => {
                Self::expression_has_parallel_source(&reference.expr)
            }
            _ => false,
        }
    }
}

impl<'ast> syn::visit::Visit<'ast> for PerAgentStorageVisitor<'_> {
    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        if crate::helpers::cfg_is_test_only(&node.attrs) {
            return;
        }
        self.enter_scope();
        self.declare_agent_parameters(&node.sig.ident.to_string(), &node.sig.inputs);
        self.visit_block(&node.block);
        self.leave_scope();
    }

    fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
        if crate::helpers::cfg_is_test_only(&node.attrs) {
            return;
        }
        self.enter_scope();
        self.declare_agent_parameters(&node.sig.ident.to_string(), &node.sig.inputs);
        self.visit_block(&node.block);
        self.leave_scope();
    }

    fn visit_block(&mut self, node: &'ast syn::Block) {
        self.enter_scope();
        syn::visit::visit_block(self, node);
        self.leave_scope();
    }

    fn visit_local(&mut self, node: &'ast syn::Local) {
        if let Some(init) = &node.init
            && (self.expression_mentions_agent(&init.expr) || dynamic_partition_source(&init.expr))
        {
            self.declare_agents(&node.pat);
        }
        if let Some(init) = &node.init
            && let Some(binding) = self.binding_from_expr(&init.expr)
        {
            let mut names = Vec::new();
            collect_pattern_names(&node.pat, &mut names);
            for name in names {
                self.bind(name, binding.clone());
            }
        }
        syn::visit::visit_local(self, node);
    }

    fn visit_expr_for_loop(&mut self, node: &'ast syn::ExprForLoop) {
        self.visit_expr(&node.expr);
        self.enter_scope();
        self.declare_agents(&node.pat);
        self.repetition_depth += 1;
        self.visit_block(&node.body);
        self.repetition_depth = self.repetition_depth.saturating_sub(1);
        self.leave_scope();
    }

    fn visit_expr_closure(&mut self, node: &'ast syn::ExprClosure) {
        self.enter_scope();
        for input in &node.inputs {
            self.declare_agents(input);
        }
        self.repetition_depth += 1;
        self.visit_expr(&node.body);
        self.repetition_depth = self.repetition_depth.saturating_sub(1);
        self.leave_scope();
    }

    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        let tail = node
            .func
            .to_token_stream()
            .to_string()
            .split_whitespace()
            .last()
            .unwrap_or_default()
            .to_string();
        if matches!(tail.as_str(), "write_volatile" | "replace" | "write")
            && node.args.len() >= 2
            && let Some(binding) = node
                .args
                .iter()
                .skip(1)
                .find_map(|argument| self.binding_from_expr(argument))
            && binding.raw_pointer
            && binding.agent_dependent
            && node
                .args
                .first()
                .is_some_and(|destination| self.non_local_destination(destination))
        {
            self.mark_per_agent(&binding);
        }
        let call_path = node.func.to_token_stream().to_string();
        if call_path.contains("rayon :: join")
            || call_path.ends_with("spawn")
            || call_path.ends_with("scope")
        {
            self.visit_expr(&node.func);
            self.parallel_depth += 1;
            for argument in &node.args {
                self.visit_expr(argument);
            }
            self.parallel_depth = self.parallel_depth.saturating_sub(1);
            return;
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        if node.method == "insert"
            && node.args.len() >= 2
            && node
                .args
                .first()
                .is_some_and(|key| self.expression_mentions_agent(key))
            && let Some(binding) = node
                .args
                .iter()
                .skip(1)
                .find_map(|value| self.binding_from_expr(value))
            && (binding.raw_pointer || self.parallel_depth > 0)
        {
            self.mark_per_agent(&binding);
        }
        if node.method == "for_each" && Self::expression_has_parallel_source(&node.receiver) {
            self.visit_expr(&node.receiver);
            self.parallel_depth += 1;
            for argument in &node.args {
                self.visit_expr(argument);
            }
            self.parallel_depth = self.parallel_depth.saturating_sub(1);
            return;
        }
        syn::visit::visit_expr_method_call(self, node);
    }
}

fn dynamic_partition_source(expression: &syn::Expr) -> bool {
    match expression {
        syn::Expr::Call(call) => call.args.is_empty(),
        syn::Expr::Paren(paren) => dynamic_partition_source(&paren.expr),
        syn::Expr::Group(group) => dynamic_partition_source(&group.expr),
        syn::Expr::Cast(cast) => dynamic_partition_source(&cast.expr),
        _ => false,
    }
}

fn collect_pattern_names(pattern: &syn::Pat, output: &mut Vec<String>) {
    match pattern {
        syn::Pat::Ident(ident) => output.push(ident.ident.to_string()),
        syn::Pat::Reference(reference) => collect_pattern_names(&reference.pat, output),
        syn::Pat::Type(typed) => collect_pattern_names(&typed.pat, output),
        syn::Pat::Tuple(tuple) => {
            for element in &tuple.elems {
                collect_pattern_names(element, output);
            }
        }
        syn::Pat::TupleStruct(tuple) => {
            for element in &tuple.elems {
                collect_pattern_names(element, output);
            }
        }
        syn::Pat::Struct(record) => {
            for field in &record.fields {
                collect_pattern_names(&field.pat, output);
            }
        }
        syn::Pat::Slice(slice) => {
            for element in &slice.elems {
                collect_pattern_names(element, output);
            }
        }
        syn::Pat::Paren(paren) => collect_pattern_names(&paren.pat, output),
        _ => {}
    }
}

fn expression_identifiers(expression: &syn::Expr) -> Vec<String> {
    #[derive(Default)]
    struct IdentifierCollector(Vec<String>);
    impl<'ast> syn::visit::Visit<'ast> for IdentifierCollector {
        fn visit_expr_path(&mut self, node: &'ast syn::ExprPath) {
            if let Some(segment) = node.path.segments.first() {
                self.0.push(segment.ident.to_string());
            }
            syn::visit::visit_expr_path(self, node);
        }
    }
    let mut collector = IdentifierCollector::default();
    collector.visit_expr(expression);
    collector.0
}

fn allocator_expression_type(expr: &syn::Expr) -> Option<String> {
    let syn::Expr::Call(call) = expr else {
        return None;
    };
    if !allocator_constructor(&call.func) {
        return None;
    }
    call.args.iter().find_map(allocated_type_name)
}

fn raw_box_escape(expr: &syn::Expr) -> bool {
    let syn::Expr::Path(path) = expr else {
        return false;
    };
    let segments: Vec<_> = path
        .path
        .segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect();
    segments.as_slice() == ["Box", "into_raw"]
}

fn escaped_allocated_type_name(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Call(call) if allocator_constructor(&call.func) => {
            call.args.iter().find_map(allocated_type_name)
        }
        syn::Expr::Call(call) => allocated_type_name(expr).or_else(|| {
            let syn::Expr::Path(path) = call.func.as_ref() else {
                return None;
            };
            let segments: Vec<_> = path.path.segments.iter().collect();
            let method = segments.last()?.ident.to_string();
            if method != "new" {
                return None;
            }
            segments
                .get(segments.len().saturating_sub(2))
                .map(|segment| segment.ident.to_string())
        }),
        syn::Expr::Paren(paren) => escaped_allocated_type_name(&paren.expr),
        syn::Expr::Reference(reference) => escaped_allocated_type_name(&reference.expr),
        _ => None,
    }
}

fn allocator_constructor(expr: &syn::Expr) -> bool {
    let syn::Expr::Path(path) = expr else {
        return false;
    };
    let segments: Vec<_> = path
        .path
        .segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect();
    matches!(
        segments.as_slice(),
        [wrapper, method]
            if matches!(wrapper.as_str(), "Box" | "Arc" | "Owned") && method == "new"
    )
}

fn allocated_type_name(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Struct(expr_struct) => expr_struct
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string()),
        syn::Expr::Call(call) => {
            let syn::Expr::Path(path) = call.func.as_ref() else {
                return None;
            };
            let segments: Vec<_> = path.path.segments.iter().collect();
            let method = segments.last()?.ident.to_string();
            if !matches!(method.as_str(), "default" | "new") {
                return None;
            }
            segments
                .get(segments.len().saturating_sub(2))
                .map(|segment| segment.ident.to_string())
        }
        _ => None,
    }
}

fn contiguous_element_type(ty: &str) -> Option<String> {
    normalize_type_name(&contiguous_element_spelling(ty)?)
}

fn contiguous_elements_are_isolated(
    si: &StructInfo,
    field: &FieldInfo,
    structs: &[StructInfo],
) -> bool {
    let Some(element) = contiguous_element_spelling(&field.ty_str) else {
        return false;
    };
    if is_cache_padded_type(&element)
        && si.cache_line_size <= crate::struct_layout::CACHE_PADDING_MIN_ALIGN
    {
        return true;
    }
    let Some(name) = normalize_type_name(&element) else {
        return false;
    };
    let candidates: Vec<_> = structs
        .iter()
        .filter(|other| {
            other.name == name
                && other.crate_name == si.crate_name
                && other.module_path == si.module_path
        })
        .collect();
    matches!(candidates.as_slice(), [element] if element.repr_align_bytes.is_some_and(|alignment| alignment >= si.cache_line_size))
}

fn contiguous_element_spelling(ty: &str) -> Option<String> {
    let compact: String = ty.chars().filter(|ch| !ch.is_whitespace()).collect();
    let inner = if let Some(rest) = compact.strip_prefix("Vec<") {
        rest.strip_suffix('>')?
    } else if let Some(rest) = compact.strip_prefix("Box<[") {
        rest.strip_suffix("]>")?
    } else if let Some(rest) = compact.strip_prefix("Arc<Vec<") {
        rest.strip_suffix(">>")?
    } else if let Some(rest) = compact.strip_prefix('[') {
        rest.strip_suffix(']')?.split_once(';')?.0
    } else {
        return None;
    };
    Some(inner.to_string())
}

fn assess_container_risk(
    _si: &StructInfo,
    field: &FieldInfo,
    has_evidence: bool,
    evidence_descs: &[String],
    evidence: Option<&ConcurrencyEvidenceSet>,
    api_usage: Option<&ApiUsageEvidenceSet>,
) -> Option<RiskAssessment> {
    let mut risk_factors = vec![
        "布局证据: 连续容器元素按 stride 存放，相邻槽位可能共享缓存行".to_string(),
        format!("类型证据: 容器元素包含热点同步 payload ({})", field.ty_str),
    ];
    let mut descs = evidence_descs.to_vec();
    let field_candidates = std::slice::from_ref(&field.name);
    let summary = candidate_summary(evidence, field_candidates);
    let direct_write = &summary.written_fields;
    let concurrent_write = &summary.concurrent_written_fields;
    let has_parallel = summary.has_strong_parallel;
    let has_shared = summary.has_shared_ownership;
    let api_usage_signal = api_usage.is_some_and(ApiUsageEvidenceSet::has_usage_signal);
    if summary.ownership_partitioned || summary.exclusive_plain_writes_only {
        return None;
    }
    if evidence.is_some_and(|set| consuming_parallel_ownership_only(set, &field.name)) {
        return None;
    }
    // The topology is element-level: type-wide Arc/API exposure is not an
    // element access witness. Require an indexed/container-field access or an
    // explicit non-consuming parallel traversal of this container.
    if !has_container_element_access(evidence, &field.name) {
        return None;
    }
    if !has_evidence && !api_usage_signal {
        return None;
    }

    if !direct_write.is_empty() {
        risk_factors.push("访问证据: 容器字段自身或其元素存在写/同步操作".to_string());
    }
    if has_parallel {
        risk_factors.push("并发证据: 容器所在类型在并发上下文中使用".to_string());
    } else if has_shared {
        risk_factors.push("并发证据: 容器所在类型经 Arc 共享".to_string());
    } else if api_usage_signal {
        risk_factors.push("API 使用启发: 公开 API 暗示外部可能高频访问该分片容器".to_string());
        descs.extend(api_usage.map_or_else(Vec::new, ApiUsageEvidenceSet::descriptions));
    } else {
        risk_factors
            .push("条件风险: 仅依据分片容器结构和语义报告，需结合实际 workload 判断".to_string());
    }

    let category = if has_parallel && (!direct_write.is_empty() || has_evidence) {
        RiskCategory::HotInProject
    } else if api_usage_signal {
        RiskCategory::ApiUsageLatent
    } else {
        RiskCategory::ColdOrConditional
    };
    let mut confidence: f32 = 0.58;
    if has_evidence {
        confidence += 0.08;
    }
    if has_shared {
        confidence += 0.04;
    }
    if has_parallel {
        confidence += 0.08;
    }
    if !direct_write.is_empty() || !concurrent_write.is_empty() {
        confidence += 0.06;
    }
    if api_usage_signal {
        confidence += 0.10;
    }
    if field.ty_str.contains("Mutex") || field.ty_str.contains("RwLock") {
        confidence += 0.03;
        descs.push("分片锁容器: 每个槽位的锁对象自身会被不同线程修改".to_string());
    }

    Some(RiskAssessment {
        category,
        severity: Severity::Medium,
        confidence: confidence.clamp(0.50, 0.86),
        repetition_evidence: summary.max_hotness > 1.0,
        risk_factors,
        evidence_descs: descs,
    })
}

fn consuming_parallel_ownership_only(evidence: &ConcurrencyEvidenceSet, field: &str) -> bool {
    let mut has_parallel = false;
    let mut has_element_access = false;
    for item in &evidence.evidence {
        if item.kind == EvidenceKind::UsedInParallelIter {
            has_parallel = true;
            if !item
                .semantic_contexts
                .iter()
                .any(|context| context == "consuming_self")
            {
                return false;
            }
        }
        if item.field_name.as_deref() == Some(field) && item.access_kind.is_some() {
            has_element_access = true;
        }
    }
    has_parallel && !has_element_access
}

fn has_container_element_access(evidence: Option<&ConcurrencyEvidenceSet>, field: &str) -> bool {
    evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .any(|item| {
            item.field_name.as_deref() == Some(field)
                && item.access_kind.is_some()
                && (!item.access_mode.is_exclusive()
                    || item.in_concurrent_context
                    || item.through_shared_indirection
                    || item.through_raw_pointer)
        })
        || evidence
            .into_iter()
            .flat_map(|set| &set.evidence)
            .any(|item| {
                item.kind == EvidenceKind::UsedInParallelIter
                    && !item
                        .semantic_contexts
                        .iter()
                        .any(|context| context == "consuming_self")
            })
}

fn has_shared_object_access(evidence: &ConcurrencyEvidenceSet) -> bool {
    evidence.evidence.iter().any(|item| {
        item.access_kind.is_some()
            && (!item.access_mode.is_exclusive()
                || item.through_shared_indirection
                || item.through_raw_pointer)
    })
}

fn has_allocator_escape_access(
    evidence: Option<&ConcurrencyEvidenceSet>,
    fields: &[String],
    type_erased_escape: bool,
    per_agent_storage: bool,
) -> bool {
    let candidates: HashSet<&str> = fields.iter().map(String::as_str).collect();
    let candidate_items: Vec<_> = evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .filter(|item| {
            item.field_name
                .as_deref()
                .is_some_and(|field| candidates.contains(field))
        })
        .collect();
    if per_agent_storage {
        return candidate_items.iter().any(|item| {
            matches!(
                item.access_kind,
                Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
            )
        });
    }
    if type_erased_escape {
        return candidate_items.iter().any(|item| {
            item.through_shared_indirection
                || item.through_raw_pointer
                || item.in_concurrent_context
                || item
                    .semantic_contexts
                    .iter()
                    .any(|context| context == "embedded_allocator_escape")
        });
    }

    let explicit_cross_agent_type = evidence.is_some_and(|set| {
        set.has_kind(EvidenceKind::ArcWrapped) && set.has_kind(EvidenceKind::SendSyncCapability)
    });
    explicit_cross_agent_type
        && candidate_items.iter().any(|item| {
            matches!(
                item.access_kind,
                Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
            )
        })
}

fn assess_object_alignment_risk(
    si: &StructInfo,
    fields: &[String],
    has_evidence: bool,
    evidence_descs: &[String],
    evidence: Option<&ConcurrencyEvidenceSet>,
    api_usage: Option<&ApiUsageEvidenceSet>,
    placement: ObjectPlacementContext,
) -> Option<RiskAssessment> {
    let topology_evidence = match (placement.topology, placement.per_agent_storage) {
        (ColocationPattern::AllocatorObjects, true) => {
            "拓扑证据: 流敏感 points-to 关系证明独立分配对象逃逸到按 agent 键控的非局部存储"
        }
        (ColocationPattern::AllocatorObjects, false) => {
            "拓扑证据: 分配与逃逸关系证明独立对象可能占用相邻 allocator slots"
        }
        _ => "拓扑证据: 源码类型关系证明该对象用作连续容器元素",
    };
    let mut risk_factors = vec![
        topology_evidence.to_string(),
        "保护缺失: 结构体本身没有 cache-line 级 repr(align)".to_string(),
    ];
    if si
        .total_estimated_size
        .map(|size| size <= si.cache_line_size)
        .unwrap_or(false)
    {
        risk_factors
            .push("stride 证据: 对象估算大小不超过一个缓存行，相邻对象容易同线".to_string());
    }
    if fields.len() >= 2 {
        risk_factors.push(format!("热点字段: {}", fields.join(", ")));
    }
    let api_usage_signal = api_usage.is_some_and(ApiUsageEvidenceSet::has_usage_signal);
    if !has_evidence && !api_usage_signal {
        return None;
    }
    let mut descs = evidence_descs.to_vec();
    if evidence.is_some_and(ConcurrencyEvidenceSet::has_strong_parallel_signal) {
        risk_factors.push("并发证据: 对象类型在并发上下文中使用".to_string());
    } else if has_evidence {
        risk_factors.push("并发证据: 存在共享/访问证据，但未证明具体并行写入".to_string());
    } else if api_usage_signal {
        risk_factors
            .push("API 使用启发: 公开 API 暗示外部可能高频创建、调度或访问该对象".to_string());
        descs.extend(api_usage.map_or_else(Vec::new, ApiUsageEvidenceSet::descriptions));
    }

    let category =
        if has_evidence && evidence.is_some_and(ConcurrencyEvidenceSet::has_concurrency_signal) {
            RiskCategory::HotInProject
        } else if api_usage_signal {
            RiskCategory::ApiUsageLatent
        } else {
            RiskCategory::ColdOrConditional
        };

    Some(RiskAssessment {
        category,
        severity: Severity::Medium,
        confidence: if has_evidence {
            0.74
        } else if api_usage_signal {
            0.66
        } else {
            0.58
        },
        repetition_evidence: evidence.is_some_and(|set| set.max_hotness() > 1.0),
        risk_factors,
        evidence_descs: descs,
    })
}

/// A single field at the same offset in two non-overlapping instances cannot
/// share a B-byte block when the minimum distance from the end of the first
/// field to the start of the next is at least B. This holds for contiguous
/// elements and for independently allocated instances, regardless of their
/// base alignment or repr(Rust) field order.
fn same_field_object_stride_excludes_colocation(si: &StructInfo, fields: &[String]) -> bool {
    let [field_name] = fields else {
        return false;
    };
    let Some(field) = si.fields.iter().find(|field| &field.name == field_name) else {
        return false;
    };
    let Some(field_size) = exact_simple_field_size(&field.ty_str) else {
        return false;
    };
    let minimum_stride = si.fields.iter().try_fold(0usize, |sum, item| {
        sum.checked_add(minimum_inline_size(&item.ty_str).unwrap_or(0))
    });
    minimum_stride.is_some_and(|stride| {
        stride >= field_size && stride - field_size >= si.cache_line_size.saturating_sub(1)
    })
}

fn exact_simple_field_size(ty: &str) -> Option<usize> {
    match ty.trim() {
        "bool" | "u8" | "i8" => Some(1),
        "u16" | "i16" => Some(2),
        "u32" | "i32" | "f32" => Some(4),
        "u64" | "i64" | "f64" => Some(8),
        "usize" | "isize" => Some(std::mem::size_of::<usize>()),
        "u128" | "i128" => Some(16),
        _ => {
            let parsed = syn::parse_str::<syn::Type>(ty).ok()?;
            let syn::Type::Path(path) = parsed else {
                return None;
            };
            match path.path.segments.last()?.ident.to_string().as_str() {
                "AtomicBool" | "AtomicU8" | "AtomicI8" => Some(1),
                "AtomicU16" | "AtomicI16" => Some(2),
                "AtomicU32" | "AtomicI32" => Some(4),
                "AtomicU64" | "AtomicI64" => Some(8),
                "AtomicUsize" | "AtomicIsize" => Some(std::mem::size_of::<usize>()),
                _ => None,
            }
        }
    }
}

fn minimum_inline_size(ty: &str) -> Option<usize> {
    if let Some(size) = exact_simple_field_size(ty) {
        return Some(size);
    }
    let parsed = syn::parse_str::<syn::Type>(ty).ok()?;
    let syn::Type::Path(path) = parsed else {
        return None;
    };
    let last = path.path.segments.last()?;
    match last.ident.to_string().as_str() {
        // std::Vec is guaranteed to contain a pointer, length, and capacity;
        // std::String contains a Vec<u8>. Their order is irrelevant here.
        "Vec" if matches!(&last.arguments, syn::PathArguments::AngleBracketed(args) if args.args.len() == 1) => {
            Some(3 * std::mem::size_of::<usize>())
        }
        "String" if matches!(last.arguments, syn::PathArguments::None) => {
            Some(3 * std::mem::size_of::<usize>())
        }
        _ => None,
    }
}

fn assess_single_field_risk(
    si: &StructInfo,
    field: &str,
    evidence_descs: &[String],
    evidence: Option<&ConcurrencyEvidenceSet>,
    api_usage: Option<&ApiUsageEvidenceSet>,
) -> RiskAssessment {
    let field_candidates = vec![field.to_string()];
    let summary = candidate_summary(evidence, &field_candidates);
    let written = &summary.written_fields;
    let concurrent_written = &summary.concurrent_written_fields;
    let api_usage_signal = api_usage.is_some_and(ApiUsageEvidenceSet::has_usage_signal);
    let mut risk_factors = vec![
        "布局证据: 单热点字段未独立 padding，可能与邻接字段或相邻对象同线".to_string(),
        "访问证据: 该字段存在静态可见写/RMW，邻接位置构成独立抽象位置".to_string(),
    ];
    let mut descs = evidence_descs.to_vec();
    if !written.is_empty() {
        risk_factors.push("访问证据: 检测到该字段写入".to_string());
    }
    if !concurrent_written.is_empty() {
        risk_factors.push("并发证据: 该字段在并发上下文中写入".to_string());
    } else if api_usage_signal {
        risk_factors.push("API 使用启发: 公开 API 暗示外部可能高频访问该热点字段".to_string());
        descs.extend(api_usage.map_or_else(Vec::new, ApiUsageEvidenceSet::descriptions));
    }

    let category = if !concurrent_written.is_empty() && has_neighbor_payload(si, field) {
        RiskCategory::HotInProject
    } else if api_usage_signal {
        RiskCategory::ApiUsageLatent
    } else {
        RiskCategory::ColdOrConditional
    };

    RiskAssessment {
        category,
        severity: Severity::Medium,
        confidence: if !written.is_empty() {
            0.63
        } else if api_usage_signal {
            0.62
        } else {
            0.56
        },
        repetition_evidence: summary.max_hotness > 1.0,
        risk_factors,
        evidence_descs: descs,
    }
}

/// True when distinct fields are reached through distinct non-exclusive
/// methods.  This is a name-independent witness that the fields are logical
/// access partitions rather than a single compound update.
fn has_independent_shared_methods(
    evidence: Option<&ConcurrencyEvidenceSet>,
    field_names: &[String],
) -> bool {
    let Some(evidence) = evidence else {
        return false;
    };
    let candidate_set: HashSet<&str> = field_names.iter().map(String::as_str).collect();
    let mut per_field_functions: HashMap<String, HashSet<String>> = HashMap::new();

    for item in &evidence.evidence {
        if !matches!(
            item.access_kind,
            Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
        ) {
            continue;
        }
        if !matches!(
            item.kind,
            EvidenceKind::AtomicFieldOps | EvidenceKind::HotSyncFieldOps
        ) {
            continue;
        }
        if item.access_mode.is_exclusive() {
            continue;
        }
        let Some(field_name) = item.field_name.as_deref() else {
            continue;
        };
        if !candidate_set.contains(field_name) {
            continue;
        }
        let Some(function_name) = item.function_name.as_deref() else {
            continue;
        };
        per_field_functions
            .entry(field_name.to_string())
            .or_default()
            .insert(function_name.to_string());
    }

    if per_field_functions.len() < 2 {
        return false;
    }

    let mut distinct_functions = HashSet::new();
    for functions in per_field_functions.values() {
        distinct_functions.extend(functions.iter().cloned());
    }
    distinct_functions.len() >= 2
}

fn fields_share_cache_line(field_names: &[String], groups: &[Vec<String>]) -> bool {
    if groups.is_empty() {
        return false;
    }
    for group in groups {
        let count = field_names.iter().filter(|f| group.contains(f)).count();
        if count >= 2 {
            return true;
        }
    }
    false
}

fn has_strong_share_signal(si: &StructInfo, field_names: &[String]) -> bool {
    if field_names.len() < 2 {
        return false;
    }

    if si.cache_line_groups_precise {
        return fields_share_cache_line(field_names, &si.cache_line_groups);
    }

    if atomic_run_span_size(si, field_names)
        .map(|span| span <= si.cache_line_size)
        .unwrap_or(false)
    {
        return true;
    }

    if si
        .total_estimated_size
        .map(|size| size <= si.cache_line_size)
        .unwrap_or(false)
    {
        return true;
    }

    contiguous_field_span_size(si, field_names)
        .map(|span| span <= si.cache_line_size)
        .unwrap_or(false)
}

fn atomic_run_span_size(si: &StructInfo, field_names: &[String]) -> Option<usize> {
    let candidate_set: HashSet<&str> = field_names.iter().map(String::as_str).collect();
    let mut best: Option<usize> = None;
    let mut current_count = 0usize;
    let mut current_size = 0usize;

    for field in &si.fields {
        if candidate_set.contains(field.name.as_str()) && field.is_atomic && !field.is_cache_padded
        {
            current_count += 1;
            current_size += field.estimated_size?;
            if current_count >= 2 {
                best = Some(best.map_or(current_size, |prev| prev.min(current_size)));
            }
        } else {
            current_count = 0;
            current_size = 0;
        }
    }

    best
}

fn contiguous_field_span_size(si: &StructInfo, field_names: &[String]) -> Option<usize> {
    let candidate_set: HashSet<&str> = field_names.iter().map(String::as_str).collect();
    let mut indexes = Vec::new();
    let mut total = 0usize;

    for (idx, field) in si.fields.iter().enumerate() {
        if candidate_set.contains(field.name.as_str()) {
            indexes.push(idx);
            total += field.estimated_size?;
        }
    }

    if indexes.len() < 2 || indexes.windows(2).any(|window| window[1] != window[0] + 1) {
        return None;
    }

    Some(total)
}

fn is_unisolated_hot_field(field: &FieldInfo) -> bool {
    !field.is_cache_padded && !field.is_manual_padding
}

fn has_neighbor_payload(si: &StructInfo, field_name: &str) -> bool {
    let Some(index) = si.fields.iter().position(|field| field.name == field_name) else {
        return false;
    };

    let prev = index
        .checked_sub(1)
        .and_then(|idx| si.fields.get(idx))
        .map(|field| !field.is_cache_padded && !field.is_manual_padding)
        .unwrap_or(false);
    let next = si
        .fields
        .get(index + 1)
        .map(|field| !field.is_cache_padded && !field.is_manual_padding)
        .unwrap_or(false);

    prev || next
}

fn unisolated_neighbors(si: &StructInfo, field_name: &str) -> Vec<String> {
    let Some(writer_index) = si.fields.iter().position(|field| field.name == field_name) else {
        return Vec::new();
    };
    let writer = &si.fields[writer_index];
    si.fields
        .iter()
        .enumerate()
        .filter(|(_, field)| field.name != field_name)
        .filter(|(peer_index, field)| {
            if !is_unisolated_hot_field(field) {
                return false;
            }
            if si.cache_line_groups_precise {
                return fields_share_cache_line(
                    &[field_name.to_string(), field.name.clone()],
                    &si.cache_line_groups,
                );
            }
            if si.repr_c {
                let begin = writer_index.min(*peer_index) + 1;
                let end = writer_index.max(*peer_index);
                let gap = si.fields[begin..end].iter().fold(0usize, |gap, field| {
                    gap.saturating_add(field.estimated_size.unwrap_or(0))
                });
                if gap >= si.cache_line_size.saturating_sub(1) {
                    return false;
                }
            }
            // Enumerating later peers must not invent co-location across a
            // known large gap. Unknown source layouts retain symbolic may-risk.
            let (Some(writer_offset), Some(peer_offset)) = (writer.offset, field.offset) else {
                return true;
            };
            let (left, left_offset, right_offset) = if writer_offset <= peer_offset {
                (writer, writer_offset, peer_offset)
            } else {
                (*field, peer_offset, writer_offset)
            };
            left.estimated_size.is_none_or(|size| {
                right_offset
                    < left_offset
                        .saturating_add(size)
                        .saturating_add(si.cache_line_size.saturating_sub(1))
            })
        })
        .map(|(_, field)| field.name.clone())
        .collect()
}

fn sorted_names(fields: &HashSet<String>) -> Vec<String> {
    let mut names: Vec<String> = fields.iter().cloned().collect();
    names.sort();
    names
}

fn struct_key(si: &StructInfo) -> StructKey {
    StructKey::from_struct(si)
}

trait FindingLayoutExt {
    fn with_layout_context(self, si: &StructInfo) -> Self;
}

impl FindingLayoutExt for Finding {
    fn with_layout_context(mut self, si: &StructInfo) -> Self {
        self.layout_context = Some(layout_context_for_struct(si));
        self.storage_identity = Some(format!("{}::{}@{}", si.file, si.name, si.line));
        self
    }
}

trait FindingPatternExt {
    fn with_static_pattern(self, pattern: StaticPatternContext) -> Self;
}

impl FindingPatternExt for Finding {
    fn with_static_pattern(mut self, pattern: StaticPatternContext) -> Self {
        self.rule_id = pattern.rule_id;
        self.static_pattern = Some(pattern);
        self
    }
}

fn layout_context_for_struct(si: &StructInfo) -> LayoutContext {
    LayoutContext {
        language: "rust".to_string(),
        struct_name: si.name.clone(),
        canonical_type: if si.module_path.is_empty() {
            si.name.clone()
        } else {
            format!("{}::{}", si.module_path, si.name)
        },
        declaration_line: si.line,
        cache_line_size: si.cache_line_size,
        layout_certainty: layout_certainty(si).to_string(),
        fields: si
            .fields
            .iter()
            .map(|field| layout_field_context(field, si.cache_line_size))
            .collect(),
        cache_line_groups: si.cache_line_groups.clone(),
        cache_line_groups_precise: si.cache_line_groups_precise,
        repr_c: si.repr_c,
        repr_rust: !si.repr_c,
        repr_align_bytes: si.repr_align_bytes,
        repr_packed: si.repr_packed,
        has_cache_padded: si.has_cache_padded,
        manual_padding_fields: si
            .fields
            .iter()
            .filter(|field| field.is_manual_padding)
            .map(|field| field.name.clone())
            .collect(),
        total_estimated_size: si.total_estimated_size,
        layout_source: si.layout_source.as_str().to_string(),
        used_rustc_layout: si.layout_source.used_rustc_layout(),
    }
}

fn layout_certainty(si: &StructInfo) -> &'static str {
    if si.layout_source.used_rustc_layout() {
        "exact"
    } else if si.repr_c && si.cache_line_groups_precise {
        "bounded"
    } else if si.cache_line_groups_precise {
        "estimated"
    } else {
        "symbolic"
    }
}

fn layout_field_context(field: &FieldInfo, cache_line_size: usize) -> LayoutFieldContext {
    let range = field
        .offset
        .zip(field.estimated_size)
        .map(|(offset, size)| LayoutByteRange {
            start: offset,
            end_exclusive: offset.saturating_add(size),
        });
    let cache_line_range = range.as_ref().map(|range| {
        let start = range.start / cache_line_size;
        let end = if range.end_exclusive == range.start {
            start
        } else {
            (range.end_exclusive - 1) / cache_line_size
        };
        LayoutCacheLineRange { start, end }
    });

    LayoutFieldContext {
        name: field.name.clone(),
        ty: field.ty_str.clone(),
        estimated_size: field.estimated_size,
        offset: field.offset,
        range,
        cache_line: cache_line_range.as_ref().map(|range| range.start),
        cache_line_range,
        is_atomic: field.is_atomic,
        is_hot_scalar: field.is_hot_scalar,
        is_hot_sync: field.is_hot_sync,
        is_cache_padded: field.is_cache_padded,
        is_manual_padding: field.is_manual_padding,
        is_indirect: field.is_indirect,
    }
}

#[derive(Clone)]
struct ParallelIndexedWriteMatch {
    declaration_line: Option<usize>,
    line: usize,
    snippet: String,
    logical_location: Option<String>,
}

#[derive(Clone, Debug)]
struct SharedBufferBinding {
    declaration_line: usize,
    logical_location: String,
    through_raw_pointer: bool,
    indexed: bool,
    agent_indexed: bool,
    agent_local: bool,
    element_alignment: Option<usize>,
}

#[derive(Default)]
struct ParallelIndexedWriteVisitor {
    cache_line_size: usize,
    element_alignments: HashMap<String, usize>,
    indexed_accessors: HashMap<String, usize>,
    parallel_depth: usize,
    symbolic_partition_depth: usize,
    scopes: Vec<HashSet<String>>,
    buffer_scopes: Vec<HashMap<String, SharedBufferBinding>>,
    agent_scopes: Vec<HashSet<String>>,
    thread_scope_receivers: Vec<HashSet<String>>,
    imports: HashMap<String, String>,
    matches: Vec<ParallelIndexedWriteMatch>,
}

impl ParallelIndexedWriteVisitor {
    fn enter_scope(&mut self) {
        self.scopes.push(HashSet::new());
        self.buffer_scopes.push(HashMap::new());
        self.agent_scopes.push(HashSet::new());
        self.thread_scope_receivers.push(HashSet::new());
    }

    fn leave_scope(&mut self) {
        self.scopes.pop();
        self.buffer_scopes.pop();
        self.agent_scopes.pop();
        self.thread_scope_receivers.pop();
    }

    fn with_parallel<F>(&mut self, f: F)
    where
        F: FnOnce(&mut Self),
    {
        self.parallel_depth += 1;
        f(self);
        self.parallel_depth = self.parallel_depth.saturating_sub(1);
    }

    fn declare_pat(&mut self, pat: &syn::Pat) {
        match pat {
            syn::Pat::Ident(ident) => {
                if let Some(scope) = self.scopes.last_mut() {
                    scope.insert(ident.ident.to_string());
                }
            }
            syn::Pat::Tuple(tuple) => {
                for elem in &tuple.elems {
                    self.declare_pat(elem);
                }
            }
            syn::Pat::Struct(pat_struct) => {
                for field in &pat_struct.fields {
                    self.declare_pat(&field.pat);
                }
            }
            syn::Pat::TupleStruct(tuple) => {
                for elem in &tuple.elems {
                    self.declare_pat(elem);
                }
            }
            syn::Pat::Reference(reference) => self.declare_pat(&reference.pat),
            syn::Pat::Type(typed) => self.declare_pat(&typed.pat),
            syn::Pat::Paren(paren) => self.declare_pat(&paren.pat),
            syn::Pat::Slice(slice) => {
                for elem in &slice.elems {
                    self.declare_pat(elem);
                }
            }
            _ => {}
        }
    }

    fn bind_buffer_pattern(&mut self, pattern: &syn::Pat, binding: SharedBufferBinding) {
        let mut names = Vec::new();
        collect_pattern_names(pattern, &mut names);
        if let Some(scope) = self.buffer_scopes.last_mut() {
            for name in names {
                scope.insert(name, binding.clone());
            }
        }
    }

    fn lookup_buffer(&self, name: &str) -> Option<SharedBufferBinding> {
        self.buffer_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn mark_agent_pattern(&mut self, pattern: &syn::Pat) {
        let mut names = Vec::new();
        collect_pattern_names(pattern, &mut names);
        if let Some(scope) = self.agent_scopes.last_mut() {
            scope.extend(names);
        }
    }

    fn expression_is_agent_derived(&self, expression: &syn::Expr) -> bool {
        expression_identifiers(expression).iter().any(|name| {
            self.agent_scopes
                .iter()
                .rev()
                .any(|scope| scope.contains(name))
        })
    }

    fn mark_agent_derived_pattern(&mut self, pattern: &syn::Pat) {
        self.mark_agent_pattern(pattern);
    }

    fn is_local_name(&self, name: &str) -> bool {
        self.scopes.iter().rev().any(|scope| scope.contains(name))
    }

    fn expr_has_parallel_source(expr: &syn::Expr) -> bool {
        match expr {
            syn::Expr::MethodCall(method) => {
                let name = method.method.to_string();
                matches!(name.as_str(), "par_iter" | "par_iter_mut" | "into_par_iter")
                    || Self::expr_has_parallel_source(&method.receiver)
            }
            syn::Expr::Call(call) => call
                .func
                .to_token_stream()
                .to_string()
                .contains("rayon :: join"),
            syn::Expr::Paren(paren) => Self::expr_has_parallel_source(&paren.expr),
            syn::Expr::Reference(reference) => Self::expr_has_parallel_source(&reference.expr),
            _ => false,
        }
    }

    fn root_name(expr: &syn::Expr) -> Option<String> {
        match expr {
            syn::Expr::Path(path) => path.path.segments.first().map(|seg| seg.ident.to_string()),
            syn::Expr::Field(field) => Self::root_name(&field.base),
            syn::Expr::Paren(paren) => Self::root_name(&paren.expr),
            syn::Expr::Reference(reference) => Self::root_name(&reference.expr),
            syn::Expr::Unary(unary) => Self::root_name(&unary.expr),
            _ => None,
        }
    }

    fn record_index_write(&mut self, expr: &syn::Expr, line: usize) {
        let syn::Expr::Index(indexed) = expr else {
            return;
        };

        let Some(root_name) = Self::root_name(&indexed.expr) else {
            return;
        };

        if !self.expression_is_agent_derived(&indexed.index) {
            return;
        }
        if self
            .lookup_buffer(&root_name)
            .is_some_and(|binding| binding.agent_local)
        {
            return;
        }
        if self
            .buffer_binding_from_expr(&indexed.expr)
            .is_some_and(|binding| {
                binding
                    .element_alignment
                    .is_some_and(|alignment| alignment >= self.cache_line_size)
            })
        {
            return;
        }
        if root_name != "self"
            && self.is_local_name(&root_name)
            && self.lookup_buffer(&root_name).is_none()
        {
            return;
        }

        self.matches.push(ParallelIndexedWriteMatch {
            line,
            snippet: expr.to_token_stream().to_string(),
            logical_location: Some(indexed.expr.to_token_stream().to_string()),
            declaration_line: None,
        });
    }

    fn buffer_binding_from_expr(&self, expression: &syn::Expr) -> Option<SharedBufferBinding> {
        match expression {
            syn::Expr::Path(path) => {
                self.lookup_buffer(&path.path.segments.last()?.ident.to_string())
            }
            syn::Expr::Reference(reference) => self.buffer_binding_from_expr(&reference.expr),
            syn::Expr::Unary(unary) => self.buffer_binding_from_expr(&unary.expr),
            syn::Expr::Paren(paren) => self.buffer_binding_from_expr(&paren.expr),
            syn::Expr::Group(group) => self.buffer_binding_from_expr(&group.expr),
            syn::Expr::Cast(cast) => {
                self.buffer_binding_from_expr(&cast.expr)
                    .map(|mut binding| {
                        binding.element_alignment = None;
                        binding
                    })
            }
            syn::Expr::Unsafe(expr_unsafe) => expr_unsafe
                .block
                .stmts
                .last()
                .and_then(statement_expression)
                .and_then(|tail| self.buffer_binding_from_expr(tail)),
            syn::Expr::Index(index) => {
                self.buffer_binding_from_expr(&index.expr)
                    .map(|mut binding| {
                        binding.indexed = true;
                        binding.agent_indexed |= self.expression_is_agent_derived(&index.index);
                        binding
                    })
            }
            syn::Expr::MethodCall(method) => {
                let mut binding = self.buffer_binding_from_expr(&method.receiver)?;
                let name = method.method.to_string();
                if let Some(index) = self.indexed_accessors.get(&name) {
                    binding.indexed = true;
                    binding.agent_indexed |= method
                        .args
                        .iter()
                        .nth(*index)
                        .is_some_and(|index| self.expression_is_agent_derived(index));
                }
                if name == "cast" {
                    binding.element_alignment = None;
                }
                if matches!(name.as_str(), "as_ptr" | "as_mut_ptr" | "get") {
                    binding.through_raw_pointer = true;
                }
                if name.contains("unchecked")
                    || matches!(name.as_str(), "get_mut" | "index_mut" | "at_mut")
                {
                    binding.indexed = true;
                }
                if matches!(
                    name.as_str(),
                    "add"
                        | "offset"
                        | "wrapping_add"
                        | "wrapping_offset"
                        | "get"
                        | "get_mut"
                        | "get_unchecked"
                        | "get_unchecked_mut"
                        | "index_mut"
                        | "at_mut"
                ) {
                    binding.agent_indexed |= method
                        .args
                        .first()
                        .is_some_and(|index| self.expression_is_agent_derived(index));
                }
                Some(binding)
            }
            syn::Expr::Call(call) => {
                let function = call.func.to_token_stream().to_string();
                let mut binding = call
                    .args
                    .first()
                    .and_then(|argument| self.buffer_binding_from_expr(argument))?;
                if function.contains("from_raw_parts") || function.ends_with("from_raw_parts_mut") {
                    binding.through_raw_pointer = true;
                }
                Some(binding)
            }
            _ => None,
        }
    }

    fn base_buffer_binding(
        &self,
        expression: &syn::Expr,
        logical_location: String,
    ) -> Option<SharedBufferBinding> {
        let tokens = expression.to_token_stream().to_string();
        let dense_allocation = matches!(expression, syn::Expr::Macro(expr_macro) if expr_macro.mac.path.segments.last().is_some_and(|segment| segment.ident == "vec"))
            || matches!(expression, syn::Expr::Call(call) if matches!(&*call.func, syn::Expr::Path(path) if path.path.segments.iter().any(|segment| segment.ident == "Vec") && path.path.segments.last().is_some_and(|segment| matches!(segment.ident.to_string().as_str(), "new" | "with_capacity"))))
            || tokens.contains("Vec :: with_capacity")
            || tokens.contains("Vec :: new")
            || tokens.contains("vec !")
            || tokens.contains("Box :: new");
        dense_allocation.then(|| SharedBufferBinding {
            declaration_line: expression.span().start().line,
            logical_location,
            through_raw_pointer: false,
            indexed: false,
            agent_indexed: false,
            agent_local: self.parallel_depth > 0,
            element_alignment: self.allocation_element_alignment(expression),
        })
    }

    fn record_shared_buffer_mutation(&mut self, expression: &syn::Expr, line: usize) {
        if self.parallel_depth == 0 || self.symbolic_partition_depth == 0 {
            return;
        }
        let Some(binding) = self.buffer_binding_from_expr(expression) else {
            return;
        };
        if binding.agent_local {
            return;
        }
        if !binding.through_raw_pointer || !binding.indexed || !binding.agent_indexed {
            return;
        }
        if binding
            .element_alignment
            .is_some_and(|alignment| alignment >= self.cache_line_size)
        {
            return;
        }
        self.matches.push(ParallelIndexedWriteMatch {
            line,
            snippet: format!(
                "{} [points-to alias; raw slice; symbolic agent partition]",
                expression.to_token_stream()
            ),
            logical_location: Some(binding.logical_location),
            declaration_line: Some(binding.declaration_line),
        });
    }

    fn collect_imports(&mut self, ast: &syn::File) {
        fn collect(tree: &syn::UseTree, prefix: &str, imports: &mut HashMap<String, String>) {
            match tree {
                syn::UseTree::Path(path) => {
                    collect(&path.tree, &format!("{prefix}{}::", path.ident), imports)
                }
                syn::UseTree::Name(name) => {
                    imports.insert(name.ident.to_string(), format!("{prefix}{}", name.ident));
                }
                syn::UseTree::Rename(name) => {
                    imports.insert(name.rename.to_string(), format!("{prefix}{}", name.ident));
                }
                syn::UseTree::Group(group) => {
                    for item in &group.items {
                        collect(item, prefix, imports);
                    }
                }
                syn::UseTree::Glob(_) => {}
            }
        }
        for item in &ast.items {
            if let syn::Item::Use(item) = item {
                collect(&item.tree, "", &mut self.imports);
            }
        }
    }

    fn collect_element_alignments(&mut self, ast: &syn::File) {
        struct Collector<'a>(&'a mut HashMap<String, usize>);
        impl<'ast> Visit<'ast> for Collector<'_> {
            fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
                let alignment =
                    crate::struct_layout::analyze_struct_layout(item, "", "", None, "", 1)
                        .repr_align_bytes
                        .unwrap_or(1);
                self.0
                    .entry(item.ident.to_string())
                    .and_modify(|existing| *existing = (*existing).min(alignment))
                    .or_insert(alignment);
            }
        }
        Collector(&mut self.element_alignments).visit_file(ast);
    }

    fn vector_element_alignment(&self, path: &syn::Path) -> Option<usize> {
        let segment = path
            .segments
            .iter()
            .find(|segment| segment.ident == "Vec")?;
        let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments else {
            return None;
        };
        let syn::GenericArgument::Type(ty) = arguments.args.first()? else {
            return None;
        };
        self.element_alignments
            .get(&normalize_type_name(&ty.to_token_stream().to_string())?)
            .copied()
    }

    fn allocation_element_alignment(&self, expression: &syn::Expr) -> Option<usize> {
        match expression {
            syn::Expr::Call(call) => {
                let syn::Expr::Path(path) = &*call.func else {
                    return None;
                };
                self.vector_element_alignment(&path.path)
            }
            _ => None,
        }
    }

    fn call_path(&self, expr: &syn::Expr) -> Option<String> {
        let syn::Expr::Path(path) = expr else {
            return None;
        };
        let mut segments = path
            .path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string());
        let first = segments.next()?;
        let first = self.imports.get(&first).cloned().unwrap_or(first);
        Some(
            std::iter::once(first)
                .chain(segments)
                .collect::<Vec<_>>()
                .join("::"),
        )
    }

    fn visit_parallel_callback(&mut self, expr: &syn::Expr) {
        if matches!(expr, syn::Expr::Closure(_)) {
            self.with_parallel(|visitor| visitor.visit_expr(expr));
        } else {
            self.visit_expr(expr);
        }
    }
}

impl<'ast> syn::visit::Visit<'ast> for ParallelIndexedWriteVisitor {
    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        let execution = (self.parallel_depth, self.symbolic_partition_depth);
        self.parallel_depth = 0;
        self.symbolic_partition_depth = 0;
        self.visit_block(&node.block);
        (self.parallel_depth, self.symbolic_partition_depth) = execution;
    }

    fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
        let execution = (self.parallel_depth, self.symbolic_partition_depth);
        self.parallel_depth = 0;
        self.symbolic_partition_depth = 0;
        self.visit_block(&node.block);
        (self.parallel_depth, self.symbolic_partition_depth) = execution;
    }

    fn visit_block(&mut self, node: &'ast syn::Block) {
        self.enter_scope();
        syn::visit::visit_block(self, node);
        self.leave_scope();
    }

    fn visit_local(&mut self, node: &'ast syn::Local) {
        let derived_buffer = node
            .init
            .as_ref()
            .and_then(|init| self.buffer_binding_from_expr(&init.expr));
        let mut names = Vec::new();
        collect_pattern_names(&node.pat, &mut names);
        let base_buffer = node.init.as_ref().and_then(|init| {
            names
                .first()
                .and_then(|name| self.base_buffer_binding(&init.expr, name.clone()))
        });
        let agent_derived = node
            .init
            .as_ref()
            .is_some_and(|init| self.expression_is_agent_derived(&init.expr));
        self.declare_pat(&node.pat);
        if let Some(mut binding) = derived_buffer.or(base_buffer) {
            if let syn::Pat::Type(typed) = &node.pat
                && let syn::Type::Path(path) = &*typed.ty
            {
                binding.element_alignment = self.vector_element_alignment(&path.path);
            }
            self.bind_buffer_pattern(&node.pat, binding);
        }
        if agent_derived {
            self.mark_agent_derived_pattern(&node.pat);
        }
        syn::visit::visit_local(self, node);
    }

    fn visit_expr_closure(&mut self, node: &'ast syn::ExprClosure) {
        self.enter_scope();
        for input in &node.inputs {
            self.declare_pat(input);
            if self.parallel_depth > 0 {
                self.mark_agent_pattern(input);
            }
        }
        syn::visit::visit_expr_closure(self, node);
        self.leave_scope();
    }

    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        let path = self.call_path(&node.func);
        if matches!(
            path.as_deref(),
            Some("std::thread::scope" | "crossbeam::thread::scope")
        ) {
            self.visit_expr(&node.func);
            for arg in &node.args {
                if let syn::Expr::Closure(closure) = arg {
                    self.enter_scope();
                    let mut names = Vec::new();
                    for input in &closure.inputs {
                        collect_pattern_names(input, &mut names);
                    }
                    self.thread_scope_receivers
                        .last_mut()
                        .unwrap()
                        .extend(names);
                    self.visit_expr(&closure.body);
                    self.leave_scope();
                } else {
                    self.visit_expr(arg);
                }
            }
            return;
        }
        if matches!(
            path.as_deref(),
            Some(
                "std::thread::spawn"
                    | "tokio::spawn"
                    | "tokio::task::spawn"
                    | "async_std::task::spawn"
                    | "rayon::spawn"
                    | "rayon::join"
            )
        ) {
            self.visit_expr(&node.func);
            for arg in &node.args {
                self.visit_parallel_callback(arg);
            }
            return;
        }

        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        let method = node.method.to_string();
        if method == "spawn"
            && Self::root_name(&node.receiver).is_some_and(|name| {
                self.thread_scope_receivers
                    .iter()
                    .rev()
                    .any(|scope| scope.contains(&name))
            })
        {
            self.visit_expr(&node.receiver);
            for arg in &node.args {
                self.visit_parallel_callback(arg);
            }
            return;
        }

        if matches!(
            method.as_str(),
            "for_each" | "for_each_with" | "for_each_init" | "map" | "inspect"
        ) && Self::expr_has_parallel_source(&node.receiver)
        {
            self.visit_expr(&node.receiver);
            for arg in &node.args {
                self.with_parallel(|visitor| visitor.visit_expr(arg));
            }
            return;
        }

        if self.parallel_depth > 0
            && matches!(
                method.as_str(),
                "push"
                    | "insert"
                    | "set"
                    | "store"
                    | "swap"
                    | "fetch_add"
                    | "fetch_sub"
                    | "replace"
                    | "write"
                    | "borrow_mut"
            )
        {
            self.record_shared_buffer_mutation(&node.receiver, node.span().start().line);
        }

        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_expr_if(&mut self, node: &'ast syn::ExprIf) {
        self.visit_expr(&node.cond);
        let partition = self.parallel_depth > 0 && self.expression_is_agent_derived(&node.cond);
        if partition {
            self.symbolic_partition_depth += 1;
        }
        self.visit_block(&node.then_branch);
        if partition {
            self.symbolic_partition_depth = self.symbolic_partition_depth.saturating_sub(1);
        }
        if let Some((_, else_branch)) = &node.else_branch {
            self.visit_expr(else_branch);
        }
    }

    fn visit_expr_for_loop(&mut self, node: &'ast syn::ExprForLoop) {
        self.visit_expr(&node.expr);
        self.enter_scope();
        self.declare_pat(&node.pat);
        let single_iteration = match &*node.expr {
            syn::Expr::Range(range) => {
                let value = |expr: &syn::Expr| match expr {
                    syn::Expr::Lit(syn::ExprLit {
                        lit: syn::Lit::Int(value),
                        ..
                    }) => value.base10_parse::<usize>().ok(),
                    _ => None,
                };
                match (
                    range.start.as_deref().and_then(value),
                    range.end.as_deref().and_then(value),
                ) {
                    (Some(start), Some(end)) => {
                        end.saturating_sub(start)
                            .saturating_add(usize::from(matches!(
                                range.limits,
                                syn::RangeLimits::Closed(_)
                            )))
                            <= 1
                    }
                    _ => false,
                }
            }
            _ => false,
        };
        if !single_iteration {
            self.mark_agent_pattern(&node.pat);
        }
        self.visit_block(&node.body);
        self.leave_scope();
    }

    fn visit_expr_assign(&mut self, node: &'ast syn::ExprAssign) {
        if self.parallel_depth > 0 {
            self.record_index_write(&node.left, node.left.span().start().line);
            self.record_shared_buffer_mutation(&node.left, node.left.span().start().line);
        }
        syn::visit::visit_expr_assign(self, node);
    }
}

fn statement_expression(statement: &syn::Stmt) -> Option<&syn::Expr> {
    match statement {
        syn::Stmt::Expr(expression, _) => Some(expression),
        _ => None,
    }
}

/// Attach the already resolved receiver layout without changing the access witness.
pub(crate) fn bind_indexed_record_finding(finding: &mut Finding, si: &StructInfo, field: &str) {
    if !si.fields.iter().any(|member| member.name == field) {
        return;
    }
    finding.struct_name = Some(si.name.clone());
    finding.field_list = vec![field.to_string()];
    finding.layout_context = Some(layout_context_for_struct(si));
    finding.storage_identity = Some(format!("{}::{}@{}", si.file, si.name, si.line));
}

#[cfg(test)]
mod semantic_relation_tests {
    use super::*;

    #[test]
    fn per_agent_storage_follows_box_raw_alias_into_keyed_map() {
        let file = syn::parse_file(
            r#"
struct Slot { state: u64 }
fn install(agent: usize) {
    let boxed = Box::new(Slot { state: agent as u64 });
    let raw = Box::into_raw(boxed);
    unsafe { REGISTRY.insert(agent, &(*raw)); }
}
fn install_all() {
    for agent in 0..8 { install(agent); }
}
"#,
        )
        .unwrap();
        let key = StructKey::new("demo", "storage", "Slot");
        let mut by_name = HashMap::new();
        by_name.insert("Slot", vec![key.clone()]);
        let mut allocator = HashSet::new();
        let mut erased = HashSet::new();
        let mut per_agent = HashSet::new();
        let agent_parameters = collect_repeated_call_parameters(&file);
        let mut visitor = PerAgentStorageVisitor::new(
            &by_name,
            "storage",
            &agent_parameters,
            &mut allocator,
            &mut erased,
            &mut per_agent,
        );
        visitor.visit_file(&file);
        assert!(allocator.contains(&key));
        assert!(erased.contains(&key));
        assert!(per_agent.contains(&key));
    }

    #[test]
    fn ordinary_keyed_arc_cache_is_not_per_agent_storage() {
        let file = syn::parse_file(
            r#"
struct Slot { state: u64 }
fn cache(key: String, seed: u64) {
    REGISTRY.insert(key, std::sync::Arc::new(Slot { state: seed }));
}
"#,
        )
        .unwrap();
        let key = StructKey::new("demo", "storage", "Slot");
        let mut by_name = HashMap::new();
        by_name.insert("Slot", vec![key.clone()]);
        let agent_parameters = collect_repeated_call_parameters(&file);
        let mut allocator = HashSet::new();
        let mut erased = HashSet::new();
        let mut per_agent = HashSet::new();
        PerAgentStorageVisitor::new(
            &by_name,
            "storage",
            &agent_parameters,
            &mut allocator,
            &mut erased,
            &mut per_agent,
        )
        .visit_file(&file);
        assert!(!per_agent.contains(&key));
    }

    #[test]
    fn typed_vec_allocated_inside_spawn_is_agent_local() {
        let file = syn::parse_file(
            r#"
fn launch() {
    std::thread::spawn(move || {
        let mut current_depths: Vec<u8> = vec![1; 64];
        let pos_idx = 3usize;
        current_depths[pos_idx] = current_depths[pos_idx].saturating_add(1);
    });
}
"#,
        )
        .unwrap();
        let mut visitor = ParallelIndexedWriteVisitor::default();
        visitor.visit_file(&file);
        assert!(
            visitor.matches.is_empty(),
            "typed locals must shadow outer/shared buffer candidates: {:?}",
            visitor
                .matches
                .iter()
                .map(|item| item.snippet.as_str())
                .collect::<Vec<_>>()
        );
    }
}
