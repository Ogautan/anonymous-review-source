use std::collections::{HashMap, HashSet};

use crate::helpers::stable_finding_hash;
use crate::types::{
    AccessEvidenceContext, AnalysisOptions, CandidateKind, Finding, LayoutByteRange,
    LayoutCacheLineRange, LayoutContext, LayoutFieldContext, RiskCategory, Severity, UsageLocation,
};

use super::evidence::{
    container_field_element_name, container_has_atomic_elements, is_container_field_name,
};
use super::layout::{clean_type_name, fields_may_share_cache_line, is_cpp_atomic_type};
use super::types::{
    AtomicAliasArrayCandidate, CppAccessKind, CppEvidenceItem, CppEvidenceKind, CppEvidenceSet,
    CppFieldInfo, CppStructInfo, IndexedWriteCandidate, StaticHotStateCandidate,
};

pub fn apply_cpp_rules(
    structs: &[CppStructInfo],
    evidence_by_record: &[CppEvidenceSet],
    indexed_writes: &[IndexedWriteCandidate],
    atomic_alias_arrays: &[AtomicAliasArrayCandidate],
    static_hot_state: &[StaticHotStateCandidate],
    options: &AnalysisOptions,
) -> Vec<Finding> {
    let mut findings = Vec::new();
    for (record_idx, record) in structs.iter().enumerate() {
        let evidence = evidence_by_record.get(record_idx);

        if options.candidate_enabled(CandidateKind::FieldGroup)
            && record.atomic_fields.len() >= 2
            && fields_may_share_cache_line(record, &record.atomic_fields)
            && let Some(assessment) = assess_record_field_risk(
                record,
                &record.atomic_fields,
                evidence,
                false,
                "多个未隔离 atomic 字段可能处于同一缓存行",
            )
        {
            findings.push(with_risk_factors(make_cpp_finding(
                assessment.category,
                CandidateKind::FieldGroup,
                "C++ 类型中多个 atomic 字段可能共享同一缓存行",
                assessment.severity,
                &record.file,
                record.line,
                &record.project_name,
                format!("{} {} {{ {} }}", record_kind(record), record.name, record.atomic_fields.join(", ")),
                "为热点 atomic 字段增加满足本次配置粒度的 alignas/padded wrapper 隔离，或拆分结构体。",
                assessment.confidence,
                Some(&record.name),
                &assessment.field_names,
                &assessment.evidence_descs,
                evidence,
            )
            .with_cpp_layout_context(record), assessment.risk_factors));
        }

        if options.candidate_enabled(CandidateKind::FieldGroup)
            && record.hot_scalar_fields.len() >= 2
            && fields_may_share_cache_line(record, &record.hot_scalar_fields)
            && evidence.is_some_and(|set| {
                !set.written_fields_matching(&record.hot_scalar_fields)
                    .is_empty()
            })
            && let Some(assessment) = assess_record_field_risk(
                record,
                &record.hot_scalar_fields,
                evidence,
                false,
                "多个计数/索引/状态标量字段紧邻，可能被不同线程高频写入",
            )
        {
            findings.push(with_risk_factors(make_cpp_finding(
                assessment.category,
                CandidateKind::FieldGroup,
                "C++ 类型中多个热点标量字段紧邻",
                assessment.severity,
                &record.file,
                record.line,
                &record.project_name,
                format!("{} {} {{ {} }}", record_kind(record), record.name, record.hot_scalar_fields.join(", ")),
                "如果这些字段由不同线程写入，请按线程分片、拆分结构体或对热点字段做 cache-line 填充。",
                assessment.confidence.min(0.78),
                Some(&record.name),
                &assessment.field_names,
                &assessment.evidence_descs,
                evidence,
            )
            .with_cpp_layout_context(record), assessment.risk_factors));
        }

        if options.candidate_enabled(CandidateKind::ContainerElements) {
            findings.extend(apply_container_rules(record, structs, evidence));
        }

        if options.candidate_enabled(CandidateKind::WriterNeighbor) {
            findings.extend(apply_single_field_rules(record, evidence));
        }

        if options.candidate_enabled(CandidateKind::ObjectInstances) {
            findings.extend(apply_object_alignment_rules(record, evidence));
        }

        if options.candidate_enabled(CandidateKind::AtomicArray) {
            findings.extend(apply_atomic_alias_array_rules(record, evidence));
        }

        if options.candidate_enabled(CandidateKind::MixedFields) {
            findings.extend(apply_mixed_layout_rules(record, structs, evidence));
        }

        if options.candidate_enabled(CandidateKind::SeparateAllocations) {
            findings.extend(apply_cross_allocation_rules(record, evidence));
        }
    }

    if options.candidate_enabled(CandidateKind::IndexedWrites)
        || options.candidate_enabled(CandidateKind::ObjectInstances)
    {
        for candidate in indexed_writes {
            let rule = if candidate.record_peer.is_some() {
                CandidateKind::ObjectInstances
            } else {
                CandidateKind::IndexedWrites
            };
            if !options.candidate_enabled(rule) {
                continue;
            }
            let mut fields = candidate
                .field_name
                .iter()
                .chain(candidate.alias_name.iter())
                .chain(candidate.record_peer.iter().map(|peer| &peer.field))
                .cloned()
                .collect::<Vec<String>>();
            let kernel_fields = fields
                .iter()
                .filter_map(|field| field.strip_prefix("k_"))
                .filter(|field| {
                    structs
                        .iter()
                        .any(|record| record.fields.iter().any(|item| item.name == *field))
                })
                .map(ToOwned::to_owned)
                .collect::<Vec<_>>();
            fields.extend(kernel_fields);
            fields.sort();
            fields.dedup();
            let mut finding = make_cpp_finding(
                RiskCategory::ColdOrConditional,
                rule,
                if candidate.record_peer.is_some() {
                    "相邻 worker 记录中的内联数组边界可能共享缓存行"
                } else {
                    "严格 thread-indexed dense write 可能导致相邻元素伪共享"
                },
                Severity::Medium,
                &candidate.file,
                candidate.line,
                "",
                candidate.snippet.clone(),
                "改为每线程局部缓冲并 reduce，或确保不同线程写入的相邻元素使用 cache-line 对齐包装。",
                0.46,
                candidate.record_name.as_deref(),
                &fields,
                &candidate.evidence,
                None,
            );
            finding.storage_identity = candidate.storage_identity.clone();
            finding.symbol = candidate
                .function_name
                .clone()
                .or_else(|| finding.symbol.clone());
            finding.access_evidence.push(AccessEvidenceContext {
                evidence_kind: if !candidate.access_in_concurrent_context {
                    "api_index_partition"
                } else if candidate.has_direct_partition_evidence {
                    "direct_worker_partition"
                } else {
                    "parallel_indexed_write"
                }
                .to_string(),
                access_kind: Some(
                    match candidate.access_kind {
                        CppAccessKind::Read => "read",
                        CppAccessKind::Write => "write",
                        CppAccessKind::ReadModifyWrite => "read_modify_write",
                    }
                    .to_string(),
                ),
                field_name: candidate.field_name.clone(),
                hotness_score: 1.0,
                in_concurrent_context: candidate.access_in_concurrent_context,
                access_mode: "partitioned_index".to_string(),
                function_name: candidate.function_name.clone(),
                propagation_depth: 0,
                call_path: Vec::new(),
                semantic_contexts: std::iter::once("cpp_index_partition".to_string())
                    .chain(
                        candidate
                            .record_storage
                            .as_ref()
                            .map(|storage| format!("cpp_worker_record_storage:{storage}")),
                    )
                    .chain(
                        candidate
                            .record_peer
                            .as_ref()
                            .map(|peer| format!("cpp_worker_record_peer:{}", peer.field)),
                    )
                    .chain(
                        (!candidate.access_in_concurrent_context)
                            .then(|| "cpp_api_index_partition".to_string()),
                    )
                    .chain(
                        (candidate.has_direct_partition_evidence
                            && !candidate.access_in_concurrent_context)
                            .then(|| "cpp_direct_partition".to_string()),
                    )
                    .chain(
                        candidate
                            .evidence
                            .iter()
                            .any(|reason| reason.contains("[literal-slot-store]"))
                            .then(|| "cpp_literal_slot_store".to_owned()),
                    )
                    .chain(
                        candidate
                            .evidence
                            .iter()
                            .any(|reason| reason.contains("[plain-store-summary]"))
                            .then(|| "cpp_plain_store_summary".to_owned()),
                    )
                    .chain(
                        candidate
                            .evidence
                            .iter()
                            .any(|reason| reason.contains("[terminal-thread-store]"))
                            .then(|| "cpp_terminal_thread_store".to_owned()),
                    )
                    .chain(
                        candidate
                            .guard_ids
                            .iter()
                            .map(|guard| format!("cpp_guarded_by:{guard}")),
                    )
                    .collect(),
                through_shared_indirection: false,
                through_raw_pointer: false,
                file: candidate.file.clone(),
                line: candidate.line,
                description: candidate
                    .evidence
                    .first()
                    .cloned()
                    .unwrap_or_else(|| "C++ indexed worker write".to_string()),
            });
            if let Some(peer) = &candidate.record_peer {
                let mut access = finding.access_evidence.last().unwrap().clone();
                access.field_name = Some(peer.field.clone());
                access.line = peer.line;
                access.access_kind = Some(
                    match peer.kind {
                        CppAccessKind::Read => "read",
                        CppAccessKind::Write => "write",
                        CppAccessKind::ReadModifyWrite => "read_modify_write",
                    }
                    .to_owned(),
                );
                access.semantic_contexts.retain(|c| {
                    !c.starts_with("cpp_worker_record_peer:") && !c.starts_with("cpp_guarded_by:")
                });
                access
                    .semantic_contexts
                    .extend(peer.guard_ids.iter().map(|g| format!("cpp_guarded_by:{g}")));
                finding.access_evidence.push(access);
            }
            if let Some(record) = candidate.record_name.as_deref().and_then(|record_name| {
                structs.iter().find(|record| {
                    record.file == candidate.file
                        && record.name == record_name
                        && candidate.record_line.is_none_or(|line| record.line == line)
                })
            }) {
                finding = finding.with_cpp_layout_context(record);
            }
            findings.push(finding);
        }
    }

    if options.candidate_enabled(CandidateKind::StaticData) {
        for candidate in static_hot_state {
            if !candidate.is_array_like || candidate.is_generic_array {
                continue;
            }
            let fields = candidate
                .field_name
                .iter()
                .cloned()
                .collect::<Vec<String>>();
            let mut finding = make_cpp_finding(
                RiskCategory::ColdOrConditional,
                CandidateKind::StaticData,
                "C++ static/global 热点数组或 singleton 相邻风险",
                Severity::High,
                &candidate.file,
                candidate.line,
                "",
                candidate.snippet.clone(),
                "避免多线程高频写入全局热点状态；改用 thread_local、分片结构或 cache-line 对齐的聚合对象。",
                0.52,
                None,
                &fields,
                &candidate.evidence,
                None,
            );
            if let (Some(access_kind), Some(access_file), Some(access_line)) = (
                candidate.access_kind.as_ref(),
                candidate.access_file.as_ref(),
                candidate.access_line,
            ) {
                finding.access_evidence.push(AccessEvidenceContext {
                    evidence_kind: if candidate.has_partitioned_index_evidence {
                        "static_thread_indexed_write"
                    } else {
                        "static_array_write"
                    }
                    .to_string(),
                    access_kind: Some(
                        match access_kind {
                            CppAccessKind::Read => "read",
                            CppAccessKind::Write => "write",
                            CppAccessKind::ReadModifyWrite => "read_modify_write",
                        }
                        .to_string(),
                    ),
                    field_name: candidate.field_name.clone(),
                    hotness_score: 1.0,
                    in_concurrent_context: candidate.access_in_concurrent_context,
                    access_mode: if candidate.has_partitioned_index_evidence {
                        "static_partitioned_index"
                    } else {
                        "direct_index"
                    }
                    .to_string(),
                    function_name: None,
                    propagation_depth: 0,
                    call_path: Vec::new(),
                    semantic_contexts: std::iter::once("cpp_static_storage".to_string())
                        .chain(
                            (candidate.has_partitioned_index_evidence
                                && !candidate.access_in_concurrent_context)
                                .then(|| "cpp_conditional_partition_api".to_string()),
                        )
                        .chain(
                            candidate
                                .guard_ids
                                .iter()
                                .map(|guard| format!("cpp_guarded_by:{guard}")),
                        )
                        .collect(),
                    through_shared_indirection: false,
                    through_raw_pointer: false,
                    file: access_file.clone(),
                    line: access_line,
                    description: candidate
                        .evidence
                        .last()
                        .cloned()
                        .unwrap_or_else(|| "C++ static indexed write".to_string()),
                });
            }
            findings.push(finding);
        }
        findings.extend(apply_static_sibling_array_rules(static_hot_state));
    }

    if options.candidate_enabled(CandidateKind::AtomicArray) {
        for candidate in atomic_alias_arrays {
            let fields = vec![candidate.storage_name.clone(), candidate.alias.clone()];
            let mut finding = make_cpp_finding(
                RiskCategory::ApiUsageLatent,
                CandidateKind::AtomicArray,
                "C++ atomic alias 数组元素可能共享缓存行",
                Severity::Medium,
                &candidate.file,
                candidate.line,
                "",
                candidate.snippet.clone(),
                "将 atomic alias 替换为满足本次配置粒度的 alignas wrapper，或使用 padded array/vector 存储。",
                0.68,
                None,
                &fields,
                &candidate.evidence,
                None,
            );
            if let (Some(access_kind), Some(access_file), Some(access_line)) = (
                candidate.access_kind.as_ref(),
                candidate.access_file.as_ref(),
                candidate.access_line,
            ) {
                finding.access_evidence.push(AccessEvidenceContext {
                    evidence_kind: if candidate.access_is_mutable_api {
                        "atomic_alias_mutable_index_api"
                    } else {
                        "atomic_alias_partitioned_write"
                    }
                    .to_string(),
                    access_kind: Some(
                        match access_kind {
                            CppAccessKind::Read => "read",
                            CppAccessKind::Write => "write",
                            CppAccessKind::ReadModifyWrite => "read_modify_write",
                        }
                        .to_string(),
                    ),
                    field_name: Some(candidate.storage_name.clone()),
                    hotness_score: 1.0,
                    in_concurrent_context: candidate.access_in_concurrent_context,
                    access_mode: "partitioned_index".to_string(),
                    function_name: None,
                    propagation_depth: 0,
                    call_path: Vec::new(),
                    semantic_contexts: std::iter::once("cpp_atomic_alias_storage".to_string())
                        .chain(
                            candidate
                                .access_is_mutable_api
                                .then(|| "cpp_external_mutable_index_api".to_string()),
                        )
                        .chain(
                            candidate
                                .guard_ids
                                .iter()
                                .map(|guard| format!("cpp_guarded_by:{guard}")),
                        )
                        .collect(),
                    through_shared_indirection: false,
                    through_raw_pointer: false,
                    file: access_file.clone(),
                    line: access_line,
                    description: candidate
                        .evidence
                        .last()
                        .cloned()
                        .unwrap_or_else(|| "C++ atomic alias indexed write".to_string()),
                });
            }
            findings.push(finding);
        }
    }

    if options.candidate_enabled(CandidateKind::SiblingArrays)
        && !options.ablated(crate::types::AblationComponent::MayParallel)
    {
        findings.extend(apply_parallel_sibling_array_rules(
            structs,
            evidence_by_record,
            options.cpp_include_speculative,
        ));
    }

    super::pattern::retain_theory_candidates(&mut findings, structs, evidence_by_record);
    findings
}

/// Group mutable file-scope arrays that are independently indexed by the same
/// proven worker/runtime partition. This covers C-style parallel state such as
/// `stats[thread]`, `queue[thread]` and a payload buffer passed through a
/// macro. Generic arrays are never reported alone; a group needs at least two
/// independently accessed arrays and a runtime write witness.
fn apply_static_sibling_array_rules(candidates: &[StaticHotStateCandidate]) -> Vec<Finding> {
    let mut groups: HashMap<(String, String), Vec<&StaticHotStateCandidate>> = HashMap::new();
    for candidate in candidates {
        let (Some(field), Some(index)) = (
            candidate.field_name.as_deref(),
            candidate.access_index.as_deref(),
        ) else {
            continue;
        };
        if !candidate.is_array_like
            || !candidate.is_file_scope
            || field.is_empty()
            || !candidate.has_partitioned_index_evidence
            || candidate.access_file.is_none()
            || candidate.access_kind.is_none()
        {
            continue;
        }
        groups
            .entry((candidate.file.clone(), index.to_owned()))
            .or_default()
            .push(candidate);
    }

    let mut findings = Vec::new();
    for ((file, index), mut group) in groups {
        group.sort_by_key(|candidate| {
            (
                candidate.line,
                candidate.field_name.as_deref().unwrap_or_default(),
            )
        });
        group.dedup_by(|left, right| left.field_name == right.field_name);
        if group.len() < 2
            || !group.iter().any(|candidate| {
                matches!(
                    candidate.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                )
            })
        {
            continue;
        }
        let fields = group
            .iter()
            .filter_map(|candidate| candidate.field_name.clone())
            .collect::<Vec<_>>();
        let line = group
            .iter()
            .map(|candidate| candidate.line)
            .min()
            .unwrap_or(1);
        let snippet = format!(
            "static sibling arrays [{}] partitioned by {index}",
            fields.join(", ")
        );
        let evidence = group
            .iter()
            .flat_map(|candidate| candidate.evidence.iter().cloned())
            .chain(std::iter::once(format!(
                "分组证据: file-scope arrays [{}] share the proven indexed partition '{}'; at least one selected array is written",
                fields.join(", "),
                index
            )))
            .collect::<Vec<_>>();
        let mut finding = make_cpp_finding(
            RiskCategory::ColdOrConditional,
            CandidateKind::StaticData,
            "C++ static/global sibling arrays 可能产生分区伪共享",
            Severity::High,
            &file,
            line,
            "",
            snippet,
            "将共享索引的多个全局数组合并为 cache-line 对齐的分片结构，或对每个分片元素做 padding。",
            0.56,
            None,
            &fields,
            &evidence,
            None,
        );
        for candidate in group {
            let (Some(access_file), Some(access_line), Some(access_kind), Some(field)) = (
                candidate.access_file.as_ref(),
                candidate.access_line,
                candidate.access_kind.as_ref(),
                candidate.field_name.as_ref(),
            ) else {
                continue;
            };
            let kind = match access_kind {
                CppAccessKind::Read => "static_thread_indexed_access",
                CppAccessKind::Write | CppAccessKind::ReadModifyWrite => {
                    "static_thread_indexed_write"
                }
            };
            finding.access_evidence.push(AccessEvidenceContext {
                evidence_kind: kind.to_string(),
                access_kind: Some(
                    match access_kind {
                        CppAccessKind::Read => "read",
                        CppAccessKind::Write => "write",
                        CppAccessKind::ReadModifyWrite => "read_modify_write",
                    }
                    .to_string(),
                ),
                field_name: Some(field.clone()),
                hotness_score: 1.0,
                in_concurrent_context: candidate.access_in_concurrent_context,
                access_mode: "static_partitioned_index".to_string(),
                function_name: candidate.access_function.clone(),
                propagation_depth: 0,
                call_path: Vec::new(),
                semantic_contexts: vec![
                    "cpp_static_storage".to_string(),
                    "cpp_static_sibling_array".to_string(),
                    "cpp_api_index_partition".to_string(),
                ],
                through_shared_indirection: false,
                through_raw_pointer: false,
                file: access_file.clone(),
                line: access_line,
                description: candidate
                    .evidence
                    .last()
                    .cloned()
                    .unwrap_or_else(|| format!("static array '{}' indexed by '{}'", field, index)),
            });
        }
        findings.push(finding);
    }
    findings
}

fn apply_container_rules(
    record: &CppStructInfo,
    structs: &[CppStructInfo],
    evidence: Option<&CppEvidenceSet>,
) -> Vec<Finding> {
    let mut findings = Vec::new();
    for field in &record.fields {
        if field.is_cache_padded || !is_container_field_name(&field.name, &field.ty_str) {
            continue;
        }
        let element = container_field_element_name(&field.ty_str, field.element_type.as_deref());
        let element_isolated = element.as_ref().is_some_and(|name| {
            let owners = scoped_element_records(record, name, structs);
            !owners.is_empty() && owners.iter().all(|owner| owner.is_cache_aligned)
        });
        if element_isolated {
            continue;
        }
        let element_hot = element
            .as_ref()
            .is_some_and(|name| element_type_is_hot(record, name, structs))
            || (element.as_ref().is_some_and(|name| {
                let owners = scoped_element_records(record, name, structs);
                !owners.is_empty()
                    && owners.iter().all(|owner| {
                        owner
                            .total_estimated_size
                            .is_some_and(|size| size > 0 && size < owner.cache_line_size)
                    })
            }) && evidence.is_some_and(|facts| {
                facts.items.iter().any(|item| {
                    item.field_name.as_deref() == Some(field.name.as_str())
                        && item.kind == CppEvidenceKind::ContiguousElementAccess
                        && item.in_concurrent_context
                        && !item.initialization_phase
                        && !item.through_thread_local
                        && !item.through_nonescaping_local
                        && matches!(
                            item.access_kind,
                            Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                        )
                })
            }))
            || container_has_atomic_elements(field)
            || field.is_hot_sync
            || field.is_atomic;
        if !element_hot {
            continue;
        }

        let Some(assessment) = assess_container_risk(record, field, evidence, element.as_deref())
        else {
            continue;
        };
        findings.push(with_risk_factors(make_cpp_finding(
            assessment.category,
            CandidateKind::ContainerElements,
            "C++ 连续分片容器元素可能共享缓存行",
            assessment.severity,
            &record.file,
            record.line,
            &record.project_name,
            format!("{}.{}: {}", record.name, field.name, field.ty_str),
            "将分片/桶/槽位元素改为满足本次配置粒度的 alignas 包装类型，或使用 padded allocator/wrapper 防止相邻元素同线。",
            assessment.confidence,
            Some(&record.name),
            &assessment.field_names,
            &assessment.evidence_descs,
            evidence,
        )
        .with_cpp_layout_context(record), assessment.risk_factors));
    }

    findings
}

/// Resolve a container element against C++ lexical scope before considering a
/// project-wide short-name fallback. This prevents an unrelated `Counter` or
/// `State` declaration in another namespace from donating hotness to the
/// owner, while still supporting an unambiguous out-of-line declaration.
fn scoped_element_records<'a>(
    owner: &CppStructInfo,
    element: &str,
    structs: &'a [CppStructInfo],
) -> Vec<&'a CppStructInfo> {
    let candidates = structs
        .iter()
        .filter(|candidate| candidate.name == element)
        .collect::<Vec<_>>();
    if candidates.len() <= 1 {
        return candidates;
    }

    let nested_name = format!("{}::{element}", owner.qualified_name);
    let nested = candidates
        .iter()
        .copied()
        .filter(|candidate| candidate.qualified_name == nested_name)
        .collect::<Vec<_>>();
    if !nested.is_empty() {
        return nested;
    }

    if let Some((namespace, _)) = owner.qualified_name.rsplit_once("::") {
        let sibling_name = format!("{namespace}::{element}");
        let siblings = candidates
            .iter()
            .copied()
            .filter(|candidate| candidate.qualified_name == sibling_name)
            .collect::<Vec<_>>();
        if !siblings.is_empty() {
            return siblings;
        }
    }

    let same_file = candidates
        .iter()
        .copied()
        .filter(|candidate| candidate.file == owner.file)
        .collect::<Vec<_>>();
    if !same_file.is_empty() {
        return same_file;
    }
    candidates
}

fn element_type_is_hot(owner: &CppStructInfo, element: &str, structs: &[CppStructInfo]) -> bool {
    let candidates = scoped_element_records(owner, element, structs);
    !candidates.is_empty()
        && candidates.iter().all(|candidate| {
            !candidate.is_cache_aligned
                && candidate
                    .fields
                    .iter()
                    .any(|field| (field.is_atomic || field.is_hot_sync) && !field.is_cache_padded)
        })
}

fn apply_single_field_rules(
    record: &CppStructInfo,
    evidence: Option<&CppEvidenceSet>,
) -> Vec<Finding> {
    let Some(evidence) = evidence else {
        return Vec::new();
    };
    let candidates: Vec<String> = hot_fields(record)
        .into_iter()
        .filter(|field| has_neighbor_payload(record, field))
        .collect();
    let hot_written = evidence.hot_written_fields_matching(&candidates, 5.0);
    let written = evidence.written_fields_matching(&candidates);
    let mut fields: Vec<String> = hot_written.into_iter().chain(written).collect();
    fields.sort();
    fields.dedup();
    fields.retain(|field| has_neighbor_payload(record, field));
    if fields.is_empty() {
        return Vec::new();
    }

    // writer_neighbor still needs a concrete second access. Selecting a hot field and
    // inventing its nearest declaration as the peer made address-taking and
    // unused payload bytes look like an independently accessed location.
    let accesses = evidence
        .items
        .iter()
        .filter(|item| {
            item.access_kind.is_some()
                && !item.initialization_phase
                && !item.through_thread_local
                && !item.through_nonescaping_local
        })
        .filter_map(|item| item.field_name.as_deref())
        .collect::<HashSet<_>>();
    // Keep each witnessed pair until the shared predicate has assessed it.
    // The first layout-compatible pair may be protected or lack independent
    // roles; it must not hide a later valid pair in the same record.
    let mut findings = Vec::new();
    let mut seen = HashSet::new();
    for field in &fields {
        for peer in &record.fields {
            if peer.name == *field
                || !accesses.contains(peer.name.as_str())
                || peer.is_manual_padding
                || peer.is_cache_padded
                || !fields_may_share_cache_line(record, &[field.clone(), peer.name.clone()])
            {
                continue;
            }
            let mut pair = vec![field.clone(), peer.name.clone()];
            pair.sort();
            if !seen.insert(pair.clone()) {
                continue;
            }
            let Some(assessment) = assess_record_field_risk(
                record,
                &pair,
                Some(evidence),
                false,
                "热点字段与实际访问的邻接字段可能共享缓存行",
            ) else {
                continue;
            };
            findings.push(with_risk_factors(
        make_cpp_finding(
            assessment.category,
            CandidateKind::WriterNeighbor,
            "C++ 单热点字段可能与邻接字段共享缓存行",
            assessment.severity,
            &record.file,
            record.line,
            &record.project_name,
            format!(
                "{} {} {{ {} }}",
                record_kind(record),
                record.name,
                assessment.field_names.join(", ")
            ),
            "对该热点字段使用满足本次配置粒度的 alignas wrapper，或调整布局使其独占有效干扰块。",
            assessment.confidence.max(0.56),
            Some(&record.name),
            &assessment.field_names,
            &assessment.evidence_descs,
            Some(evidence),
        )
        .with_cpp_layout_context(record),
        assessment.risk_factors,
            ));
        }
    }
    findings
}

fn apply_object_alignment_rules(
    record: &CppStructInfo,
    evidence: Option<&CppEvidenceSet>,
) -> Vec<Finding> {
    if record.is_cache_aligned {
        return Vec::new();
    }

    let evidence = evidence.unwrap_or(&EMPTY_EVIDENCE);
    let record_name = record.name.to_lowercase();
    let mut fields = hot_fields(record);
    if evidence.has_contiguous_object_storage() {
        // Object-stride risk is also established by an actual post-init
        // mutation, even when the application calls the scalar something
        // domain-specific (for example `nodes`) rather than `count`/`state`.
        // This is more precise than continually expanding a hot-name lexicon.
        fields.extend(evidence.items.iter().filter_map(|item| {
            (!item.initialization_phase
                && (matches!(
                    item.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                ) || (item.kind == CppEvidenceKind::InlineMemberAccess
                    && item.access_kind == Some(CppAccessKind::Read)))
                && item
                    .field_name
                    .as_ref()
                    .is_some_and(|name| record.fields.iter().any(|field| field.name == *name)))
            .then(|| item.field_name.clone())
            .flatten()
        }));
        fields.sort();
        fields.dedup();
    }
    if fields.is_empty() && (record_name.contains("lock") || record_name.contains("mutex")) {
        fields.extend(evidence.items.iter().filter_map(|item| {
            matches!(
                item.access_kind,
                Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
            )
            .then(|| item.field_name.clone())
            .flatten()
        }));
        fields.sort();
        fields.dedup();
    }
    let single_lock_stride = fields.len() == 1
        && (record_name.contains("lock") || record_name.contains("mutex"))
        && !evidence.written_fields_matching(&fields).is_empty();
    let object_stride_risk = record
        .total_estimated_size
        .map(|size| {
            size <= record.cache_line_size.saturating_mul(2)
                || (evidence.has_contiguous_object_storage() && size % record.cache_line_size != 0)
        })
        .unwrap_or_else(|| evidence.has_contiguous_object_storage())
        && (single_lock_stride
            || (evidence.has_contiguous_object_storage() && !fields.is_empty())
            || (fields.len() >= 2
                && (record_name.contains("thread")
                    || record_name.contains("queue")
                    || record_name.contains("state")
                    || record_name.contains("tracker")
                    || record.fields.iter().any(|field| field.is_indirect))
                // Type naming/shape alone is insufficient to establish an
                // object-stride hazard.  When no concrete contiguous storage
                // was observed, retain this exploratory path only if an
                // external API usage witness exists.
                && evidence.has_api_signal()));
    if !object_stride_risk {
        return Vec::new();
    }
    // A private contiguous array with no API, ownership, or parallel witness
    // is normally a serial work/test buffer. Atomic syntax and loop hotness
    // alone do not establish independently active neighbouring objects.
    // Keep explicitly lock-typed records eligible because their lock is a
    // structural execution-domain witness.
    let has_typed_lock_member = record.fields.iter().any(|field| {
        field.is_hot_sync && {
            let ty = field.ty_str.to_ascii_lowercase();
            ty.contains("mutex") || ty.contains("lock")
        }
    });
    let serial_atomic_data_pair = fields.len() == 2
        && fields
            .iter()
            .filter(|name| {
                record
                    .fields
                    .iter()
                    .find(|field| &field.name == *name)
                    .is_some_and(|field| field.is_atomic)
            })
            .count()
            == 1
        && fields
            .iter()
            .filter(|name| {
                record
                    .fields
                    .iter()
                    .find(|field| &field.name == *name)
                    .is_some_and(|field| !field.is_atomic && !field.is_hot_sync)
            })
            .count()
            == 1;
    if evidence.has_contiguous_object_storage()
        && !record.visibility.is_exposed()
        && !evidence.has_api_signal()
        && !evidence.has_shared_ownership_signal()
        && !evidence.has_strong_parallel_signal()
        && serial_atomic_data_pair
        && !record_name.contains("lock")
        && !record_name.contains("mutex")
        && !has_typed_lock_member
    {
        return Vec::new();
    }
    // A symbolic object-stride candidate without a concrete storage witness
    // still needs an execution-domain or synchronization witness.  A pair of
    // ordinary pointer/scalar writes discovered only in serial helper code is
    // insufficient to establish independently active neighbouring objects;
    // retaining it would turn API reachability into a false parallelism proxy.
    let has_atomic_or_lock_evidence = evidence.items.iter().any(|item| {
        matches!(
            item.kind,
            CppEvidenceKind::AtomicFieldOps | CppEvidenceKind::LockProtected
        )
    });
    let has_plain_field_access = evidence
        .items
        .iter()
        .any(|item| item.kind == CppEvidenceKind::HotScalarWrite);
    if !evidence.has_contiguous_object_storage()
        && !evidence.has_strong_parallel_signal()
        && !has_atomic_or_lock_evidence
        && has_plain_field_access
    {
        return Vec::new();
    }
    // A small two-field control record with one atomic counter and one
    // embedded synchronization object still needs a concrete object-storage
    // witness before an object-stride warning is actionable.  Without one,
    // the atomic counter and its guard are only a same-object layout fact;
    // inferring adjacent live instances would manufacture a parallel peer.
    let atomic_control_pair = fields.len() == 2
        && record.atomic_fields.len() == 1
        && record
            .fields
            .iter()
            .any(|field| field.is_hot_sync && !field.is_atomic);
    if atomic_control_pair
        && !evidence.has_contiguous_object_storage()
        && !evidence.has_allocator_object_storage()
        && !evidence.has_strong_parallel_signal()
    {
        return Vec::new();
    }
    if !evidence.has_evidence() && !evidence.has_api_signal() && !record.visibility.is_exposed() {
        return Vec::new();
    }
    let Some(assessment) = assess_record_field_risk_with_topology(
        record,
        &fields,
        Some(evidence),
        true,
        true,
        "对象可能作为数组/slab/pool 元素连续分配，相邻对象热点字段会同线",
    ) else {
        return Vec::new();
    };

    vec![with_risk_factors(
        make_cpp_finding(
            assessment.category,
            CandidateKind::ObjectInstances,
            "C++ 热点对象可能需要整体 cache-line 对齐",
            assessment.severity,
            &record.file,
            record.line,
            &record.project_name,
            format!(
                "{} {} {{ {} }}",
                record_kind(record),
                record.name,
                fields.join(", ")
            ),
            "对整个对象使用满足本次配置粒度的 alignas 或 padded allocator，避免连续对象 stride 伪共享。",
            assessment.confidence.max(0.58),
            Some(&record.name),
            &assessment.field_names,
            &assessment.evidence_descs,
            Some(evidence),
        )
        .with_cpp_layout_context(record),
        assessment.risk_factors,
    )]
}

fn apply_atomic_alias_array_rules(
    record: &CppStructInfo,
    evidence: Option<&CppEvidenceSet>,
) -> Vec<Finding> {
    if record.is_cache_aligned {
        return Vec::new();
    }
    let mut findings = Vec::new();
    for field in &record.fields {
        let element = field.element_type.as_deref().unwrap_or(&field.ty_str);
        let alias_like_atomic = field.is_array
            && !field.is_cache_padded
            && (is_cpp_atomic_type(element)
                || clean_atomic_alias_name(element)
                || field.name.to_lowercase().contains("counter"));
        if !alias_like_atomic {
            continue;
        }
        let evidence = evidence.unwrap_or(&EMPTY_EVIDENCE);
        let category = if evidence.has_strong_parallel_signal() {
            RiskCategory::HotInProject
        } else if evidence.has_api_signal() || record.visibility.is_exposed() {
            RiskCategory::ApiUsageLatent
        } else {
            RiskCategory::ColdOrConditional
        };
        let risk_factors = vec![
            "布局证据: atomic alias/wrapper 数组按对象 stride 连续存放".to_string(),
            format!("数组字段: {} ({})", field.name, field.ty_str),
        ];
        findings.push(with_risk_factors(
            make_cpp_finding(
                category,
                CandidateKind::AtomicArray,
                "C++ atomic alias/wrapper 数组元素可能共享缓存行",
                Severity::Medium,
                &record.file,
                field.line,
                &record.project_name,
                format!("{}.{}: {}", record.name, field.name, field.ty_str),
                "将 alias/wrapper 元素改为满足本次配置粒度的 alignas 类型，或使用 padded array/vector 存储。",
                0.62,
                Some(&record.name),
                std::slice::from_ref(&field.name),
                &evidence.descriptions(),
                Some(evidence),
            )
            .with_cpp_layout_context(record),
            risk_factors,
        ));
    }
    findings
}

fn apply_parallel_sibling_array_rules(
    structs: &[CppStructInfo],
    evidence_by_record: &[CppEvidenceSet],
    include_speculative: bool,
) -> Vec<Finding> {
    let mut findings = Vec::new();
    for (record_index, record) in structs.iter().enumerate() {
        // Aligning the owner separates adjacent owners, not adjacent elements
        // within its arrays. Element padding is checked on each field below.
        let evidence = evidence_by_record.get(record_index);
        let sibling_arrays: Vec<&CppFieldInfo> = record
            .fields
            .iter()
            .filter(|field| {
                let dense_scalar = container_field_element_name(
                    &field.ty_str,
                    field.element_type.as_deref(),
                )
                .and_then(|element| super::layout::scalar_type_size(&element))
                .is_some_and(|size| size < record.cache_line_size);
                let lower_name = field.name.to_ascii_lowercase();
                let partition_name = ["thread", "worker", "task", "slot"]
                    .iter()
                    .any(|keyword| lower_name.contains(keyword));
                let hot_counter_element = ["stat", "counter"]
                    .iter()
                    .any(|keyword| lower_name.contains(keyword))
                    && container_field_element_name(&field.ty_str, field.element_type.as_deref())
                        .is_some_and(|element| element_type_is_hot(record, &element, structs));
                let container_like = field.is_array
                    || field.ty_str.contains("std::vector")
                    || field.ty_str.contains("vector<")
                    || field.ty_str.contains("std::array")
                    || field.ty_str.contains("absl::FixedArray")
                    || field.ty_str.contains("folly::small_vector");
                container_like
                    && !field.is_cache_padded
                    && (dense_scalar
                        || field.is_hot_scalar
                        || field.is_atomic
                        || partition_name
                        || hot_counter_element)
                    // This linear rule need not discard a large owner record.
                    // Each reported array must have its own payload write;
                    // another array's access cannot donate that evidence.
                    && evidence.is_some_and(|facts| facts.items.iter().any(|item| {
                        item.field_name.as_deref() == Some(field.name.as_str())
                            && item.kind == CppEvidenceKind::ContiguousElementAccess
                            && (include_speculative || item.in_concurrent_context
                                || ((field.is_atomic || hot_counter_element || container_has_atomic_elements(field))
                                    && item.access_kind == Some(CppAccessKind::ReadModifyWrite)))
                            && !item.initialization_phase
                            && !item.through_thread_local
                            && !item.through_nonescaping_local
                            && matches!(item.access_kind, Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite))
                    }))
            })
            .collect();
        if sibling_arrays.len() < 2 {
            continue;
        }
        let names: Vec<String> = sibling_arrays
            .iter()
            .map(|field| field.name.clone())
            .collect();
        if !evidence.is_some_and(|evidence| {
            !evidence.accessed_fields_matching(&names).is_empty()
                && !evidence.written_fields_matching(&names).is_empty()
        }) {
            continue;
        }
        findings.push(with_risk_factors(
            make_cpp_finding(
                RiskCategory::ColdOrConditional,
                CandidateKind::SiblingArrays,
                "C++ per-thread sibling arrays 可能产生平行数组伪共享",
                Severity::Medium,
                &record.file,
                record.line,
                &record.project_name,
                format!("{} {} {{ {} }}", record_kind(record), record.name, names.join(", ")),
                "将多个 per-thread 平行数组合并为 cache-line 对齐的 struct array，或按线程对每个数组元素做 padding。",
                0.58,
                Some(&record.name),
                &names,
                &evidence.map(CppEvidenceSet::descriptions).unwrap_or_default(),
                evidence,
            )
            .with_cpp_layout_context(record),
            vec![
                "布局证据: 多个热点数组字段平行存放，线程按相同 index 写入时可能命中相邻 cache line".to_string(),
            ],
        ));
    }
    findings
}

fn apply_mixed_layout_rules(
    record: &CppStructInfo,
    structs: &[CppStructInfo],
    evidence: Option<&CppEvidenceSet>,
) -> Vec<Finding> {
    let has_queue_layout = record.fields.iter().any(|field| {
        let ty = field.ty_str.to_ascii_lowercase();
        ty.contains("list_head") || ty.contains("queue_head")
    });
    let mixed_fields: Vec<String> = record
        .fields
        .iter()
        .filter(|field| {
            let name = field.name.to_ascii_lowercase();
            let ty = field.ty_str.to_ascii_lowercase();
            !field.is_cache_padded
                && !field.is_manual_padding
                && (field.is_atomic
                    || field.is_hot_sync
                    || field.is_indirect
                    || name.contains("ref")
                    || name.contains("waker")
                    || name.contains("list")
                    || ty.contains("list_head")
                    || ty.contains("queue_head")
                    || (has_queue_layout
                        && (name.starts_with("num_")
                            || name.ends_with("_count")
                            || name.ends_with("_cnt"))))
        })
        .map(|field| field.name.clone())
        .collect();
    if mixed_fields.len() < 2 || !fields_may_share_cache_line(record, &mixed_fields) {
        return Vec::new();
    }
    let evidence = evidence.unwrap_or(&EMPTY_EVIDENCE);
    let Some(assessment) = assess_record_field_risk(
        record,
        &mixed_fields,
        Some(evidence),
        false,
        "异构热点字段、指针/refcount/waker/list handle 混排且缺少 padding",
    ) else {
        return Vec::new();
    };
    let has_exact_concurrent_conflict =
        has_independent_concurrent_field_roles(evidence, &assessment.field_names);
    if record.has_cache_padding && !has_exact_concurrent_conflict {
        return Vec::new();
    }
    let mut report_fields = assessment.field_names.clone();
    for field in record
        .fields
        .iter()
        .filter(|field| assessment.field_names.contains(&field.name) && !field.is_indirect)
    {
        let embedded_name = clean_type_name(&field.ty_str);
        // Explicit qualification must win over an identically named local
        // record. This supplements a report, so unresolved qualified names
        // must not fall back to an unrelated short-name candidate.
        let spelled_type = field
            .ty_str
            .trim()
            .trim_start_matches("const ")
            .trim_start_matches("struct ")
            .trim_start_matches("class ");
        let candidates = if spelled_type.contains("::") {
            structs
                .iter()
                .filter(|candidate| {
                    candidate.qualified_name.trim_start_matches("::")
                        == spelled_type.trim_start_matches("::")
                })
                .collect::<Vec<_>>()
        } else {
            scoped_element_records(record, &embedded_name, structs)
        };
        if candidates.len() == 1
            && let Some(embedded) = candidates.first()
            && !embedded.is_cache_aligned
            && !embedded.has_cache_padding
            && let Some(trailing_hot) = embedded
                .fields
                .iter()
                .rev()
                .find(|inner| inner.is_atomic || inner.is_hot_sync || inner.is_hot_scalar)
        {
            report_fields.push(trailing_hot.name.clone());
        }
    }
    report_fields.sort();
    report_fields.dedup();
    let mut finding = make_cpp_finding(
        assessment.category,
        CandidateKind::MixedFields,
        "C++ mixed hot/cold layout 可能需要 padding repair",
        assessment.severity,
        &record.file,
        record.line,
        &record.project_name,
        format!(
            "{} {} {{ {} }}",
            record_kind(record),
            record.name,
            mixed_fields.join(", ")
        ),
        "在异构热点字段之间插入 cache-line padding，或将热点字段拆分到已对齐的子结构。",
        assessment.confidence.max(0.56),
        Some(&record.name),
        &report_fields,
        &assessment.evidence_descs,
        Some(evidence),
    )
    .with_cpp_layout_context(record);
    // Keep declared synchronization members in serialized coverage for mixed
    // layout repair. This is a presentation supplement only: the finding hash
    // remains based on the scored risk fields, so historical identities remain
    // stable.
    finding.field_list.extend(
        record
            .fields
            .iter()
            .filter(|field| field.is_hot_sync)
            .map(|field| field.name.clone()),
    );
    finding.field_list.sort();
    finding.field_list.dedup();
    vec![with_risk_factors(finding, assessment.risk_factors)]
}

fn has_independent_concurrent_field_roles(evidence: &CppEvidenceSet, fields: &[String]) -> bool {
    let fields = fields.iter().map(String::as_str).collect::<HashSet<_>>();
    let accesses = evidence
        .items
        .iter()
        .filter(|item| item.in_concurrent_context && item.access_kind.is_some())
        .filter(|item| {
            item.field_name
                .as_deref()
                .is_some_and(|field| fields.contains(field))
        })
        .collect::<Vec<_>>();
    accesses.iter().enumerate().any(|(index, left)| {
        accesses.iter().skip(index + 1).any(|right| {
            left.function_name.is_some()
                && right.function_name.is_some()
                && left.function_name != right.function_name
                && left.field_name != right.field_name
                && (matches!(
                    left.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                ) || matches!(
                    right.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                ))
        })
    })
}

fn apply_cross_allocation_rules(
    record: &CppStructInfo,
    evidence: Option<&CppEvidenceSet>,
) -> Vec<Finding> {
    if record.is_cache_aligned {
        return Vec::new();
    }
    let mut fields: Vec<_> = record
        .fields
        .iter()
        .filter(|field| !field.is_cache_padded && !field.is_manual_padding)
        .map(|field| field.name.clone())
        .collect();
    let evidence = evidence.unwrap_or(&EMPTY_EVIDENCE);
    let unrounded_aligned_allocation = evidence.items.iter().find(|item| {
        item.kind == CppEvidenceKind::AllocatorObjectStorage
            && item.description.contains("[unrounded aligned_alloc size]")
    });
    if unrounded_aligned_allocation.is_some() {
        fields.extend(
            record
                .fields
                .iter()
                .filter(|field| {
                    evidence
                        .items
                        .iter()
                        .any(|item| item.field_name.as_deref() == Some(&field.name))
                })
                .map(|field| field.name.clone()),
        );
        fields.sort();
        fields.dedup();
    }
    let accessed = evidence.accessed_fields_matching(&fields);
    let written = evidence.written_fields_matching(&fields);
    if accessed.is_empty() || written.is_empty() {
        return Vec::new();
    }
    let concurrent_accessed = evidence.concurrent_accessed_fields_matching(&fields);
    let concurrent_written = evidence.concurrent_written_fields_matching(&fields);
    let category = if !concurrent_accessed.is_empty() && !concurrent_written.is_empty() {
        RiskCategory::HotInProject
    } else if evidence.has_api_signal() || record.visibility.is_exposed() {
        RiskCategory::ApiUsageLatent
    } else {
        RiskCategory::ColdOrConditional
    };
    let (root_file, root_line) = unrounded_aligned_allocation
        .map(|item| (item.file.as_str(), item.line))
        .unwrap_or((&record.file, record.line));
    let mut finding = make_cpp_finding(
        category,
        CandidateKind::SeparateAllocations,
        "C++ allocator adjacency 可能导致跨对象伪共享",
        Severity::Medium,
        root_file,
        root_line,
        &record.project_name,
        format!("{} {}", record_kind(record), record.name),
        "对 allocator-managed 相邻对象或数组使用 cache-line 对齐分配，并隔离 per-thread 热字段。",
        0.52,
        Some(&record.name),
        &fields,
        &evidence.descriptions(),
        Some(evidence),
    )
    .with_cpp_layout_context(record);
    if let Some(function_name) =
        unrounded_aligned_allocation.and_then(|item| item.function_name.clone())
    {
        finding.symbol = Some(function_name);
    }
    vec![with_risk_factors(
        finding,
        vec![
            "存储证据: 独立分配对象具有共享可达的访问位置".to_string(),
            "限制: 该规则需要运行时分配拓扑复核".to_string(),
        ],
    )]
}

#[derive(Clone)]
struct CppRiskAssessment {
    category: RiskCategory,
    severity: Severity,
    confidence: f32,
    field_names: Vec<String>,
    risk_factors: Vec<String>,
    evidence_descs: Vec<String>,
}

fn assess_record_field_risk(
    record: &CppStructInfo,
    field_names: &[String],
    evidence: Option<&CppEvidenceSet>,
    allow_single_field: bool,
    layout_reason: &str,
) -> Option<CppRiskAssessment> {
    assess_record_field_risk_with_topology(
        record,
        field_names,
        evidence,
        allow_single_field,
        false,
        layout_reason,
    )
}

fn assess_record_field_risk_with_topology(
    record: &CppStructInfo,
    field_names: &[String],
    evidence: Option<&CppEvidenceSet>,
    allow_single_field: bool,
    adjacent_objects: bool,
    layout_reason: &str,
) -> Option<CppRiskAssessment> {
    if field_names.is_empty() {
        return None;
    }

    let evidence = evidence.unwrap_or(&EMPTY_EVIDENCE);
    let accessed = evidence.accessed_fields_matching(field_names);
    let written = evidence.written_fields_matching(field_names);
    let concurrent_accessed = evidence.concurrent_accessed_fields_matching(field_names);
    let concurrent_written = evidence.concurrent_written_fields_matching(field_names);
    let hot_written = evidence.hot_written_fields_matching(field_names, 5.0);
    let read_only = !evidence.read_fields_matching(field_names).is_empty()
        && written.is_empty()
        && concurrent_written.is_empty()
        && hot_written.is_empty();
    let has_strong_parallel = evidence.has_strong_parallel_signal();
    let api_signal = evidence.has_api_signal() || record.visibility.is_exposed();
    if read_only {
        return None;
    }
    if accessed.is_empty() || written.is_empty() {
        return None;
    }
    let relevant_fields = strongest_colocated_component(
        record,
        &accessed,
        &written,
        allow_single_field,
        adjacent_objects,
    );
    if relevant_fields.is_empty()
        || (!allow_single_field && relevant_fields.len() < 2)
        || (!adjacent_objects && !has_layout_risk(record, &relevant_fields, allow_single_field))
    {
        return None;
    }

    let mut risk_factors = vec![format!("布局证据: {layout_reason}")];
    if record.has_base_classes {
        risk_factors.push("C++ 布局注意: 存在继承，字段 offset 采用保守估算".to_string());
    }
    if record.has_no_unique_address {
        risk_factors.push("C++ 布局注意: [[no_unique_address]] 可能改变空字段布局".to_string());
    }
    if !written.is_empty() {
        risk_factors.push(format!(
            "访问证据: 检测到热点字段写入 ({})",
            sorted(&written).join(", ")
        ));
    }
    if !concurrent_written.is_empty() {
        risk_factors.push(format!(
            "并发证据: 并发上下文中写入 ({})",
            sorted(&concurrent_written).join(", ")
        ));
    } else if has_strong_parallel {
        risk_factors
            .push("并发证据: 类型在 std::thread/OpenMP/TBB/std::async 等上下文中使用".to_string());
    } else if evidence.has_shared_ownership_signal() {
        risk_factors.push("并发证据: 类型经 std::shared_ptr 或引用共享".to_string());
    }
    if evidence.max_hotness() >= 5.0 {
        risk_factors.push(format!(
            "热度证据: 循环/重复访问最高热度 {:.1}",
            evidence.max_hotness()
        ));
    }
    if evidence.has_api_signal() {
        risk_factors
            .push("API 使用启发: public 方法/签名/命名暗示外部可能高频并发访问".to_string());
    }

    let concurrent_conflict = if allow_single_field {
        !concurrent_written.is_empty()
    } else {
        concurrent_accessed.len() >= 2 && !concurrent_written.is_empty()
    };
    let multi_field_write = written.len() >= 2 || hot_written.len() >= 2;
    let category = if concurrent_conflict {
        RiskCategory::HotInProject
    } else if api_signal {
        RiskCategory::ApiUsageLatent
    } else {
        RiskCategory::ColdOrConditional
    };

    let mut confidence: f32 = 0.48;
    if record.cache_line_groups_precise {
        confidence += 0.06;
    }
    if !written.is_empty() {
        confidence += 0.10;
    }
    if written.len() >= 2 {
        confidence += 0.08;
    }
    if has_strong_parallel {
        confidence += 0.12;
    }
    if concurrent_written.len() >= 2 {
        confidence += 0.12;
    }
    if evidence.max_hotness() >= 5.0 {
        confidence += 0.08;
    }
    if evidence.has_api_signal() {
        confidence += evidence.max_api_score().min(0.16);
    }
    if category == RiskCategory::HotInProject {
        confidence = confidence.max(0.80);
    }
    if category == RiskCategory::ApiUsageLatent {
        confidence = confidence.clamp(0.62, 0.82);
    }

    Some(CppRiskAssessment {
        category,
        severity: if evidence.max_hotness() >= 5.0 || concurrent_conflict || multi_field_write {
            Severity::High
        } else {
            Severity::Medium
        },
        confidence: confidence.clamp(0.30, 0.95),
        field_names: relevant_fields,
        risk_factors,
        evidence_descs: evidence.descriptions(),
    })
}

fn strongest_colocated_component(
    record: &CppStructInfo,
    accessed: &HashSet<String>,
    written: &HashSet<String>,
    allow_single_field: bool,
    adjacent_objects: bool,
) -> Vec<String> {
    let fields = sorted(accessed);
    let mut visited = HashSet::new();
    let mut components = Vec::<Vec<String>>::new();
    for seed in &fields {
        if !visited.insert(seed.clone()) {
            continue;
        }
        let mut component = vec![seed.clone()];
        let mut cursor = 0usize;
        while cursor < component.len() {
            let current = component[cursor].clone();
            for candidate in &fields {
                let may_share = if adjacent_objects {
                    fields_may_share_across_objects(record, &current, candidate)
                } else {
                    fields_may_share_cache_line(record, &[current.clone(), candidate.clone()])
                };
                if visited.contains(candidate) || !may_share {
                    continue;
                }
                visited.insert(candidate.clone());
                component.push(candidate.clone());
            }
            cursor += 1;
        }
        component.sort();
        if (allow_single_field || component.len() >= 2)
            && (!adjacent_objects
                || (component.iter().any(|field| written.contains(field))
                    && (component.len() >= 2
                        || fields_may_share_across_objects(record, &component[0], &component[0]))))
        {
            components.push(component);
        }
    }
    components
        .into_iter()
        .max_by_key(|component| {
            (
                component
                    .iter()
                    .filter(|field| written.contains(*field))
                    .count(),
                component.len(),
            )
        })
        .unwrap_or_default()
}

/// An array object's last accessed bytes may share a block with the next
/// object's first accessed bytes even when those fields are far apart within
/// one object. Conversely a known interior field cannot borrow that boundary.
fn fields_may_share_across_objects(record: &CppStructInfo, a: &str, b: &str) -> bool {
    let Some(a) = record.fields.iter().find(|field| field.name == a) else {
        return false;
    };
    let Some(b) = record.fields.iter().find(|field| field.name == b) else {
        return false;
    };
    if a.is_cache_padded || a.is_manual_padding || b.is_cache_padded || b.is_manual_padding {
        return false;
    }
    super::layout::fields_may_share_across_objects(record, a, b)
}

fn assess_container_risk(
    record: &CppStructInfo,
    field: &CppFieldInfo,
    evidence: Option<&CppEvidenceSet>,
    element_name: Option<&str>,
) -> Option<CppRiskAssessment> {
    if record.is_cache_aligned {
        return None;
    }
    let evidence = evidence.unwrap_or(&EMPTY_EVIDENCE);
    let api_signal = evidence.has_api_signal() || record.visibility.is_exposed();
    if !evidence.has_evidence() && !api_signal {
        return None;
    }

    let mut risk_factors = vec![
        "布局证据: 连续容器元素按 stride 存放，相邻槽位可能共享缓存行".to_string(),
        format!("容器字段: {} ({})", field.name, field.ty_str),
    ];
    if let Some(element) = element_name {
        risk_factors.push(format!(
            "元素类型证据: '{}' 包含未隔离热点 payload",
            element
        ));
    }
    if evidence.has_strong_parallel_signal() {
        risk_factors.push("并发证据: 容器所在类型在并行上下文中使用".to_string());
    } else if api_signal {
        risk_factors.push("API 使用启发: 分片容器通过 public 类型/API 暴露".to_string());
    }

    let category = if evidence.has_strong_parallel_signal() {
        RiskCategory::HotInProject
    } else if api_signal {
        RiskCategory::ApiUsageLatent
    } else {
        RiskCategory::ColdOrConditional
    };

    let mut confidence: f32 = 0.58;
    if evidence.has_evidence() {
        confidence += 0.08;
    }
    if evidence.has_strong_parallel_signal() {
        confidence += 0.10;
    }
    if api_signal {
        confidence += 0.08;
    }

    Some(CppRiskAssessment {
        category,
        severity: Severity::Medium,
        confidence: confidence.clamp(0.50, 0.88),
        field_names: vec![field.name.clone()],
        risk_factors,
        evidence_descs: evidence.descriptions(),
    })
}

static EMPTY_EVIDENCE: CppEvidenceSet = CppEvidenceSet {
    method_roles: Vec::new(),
    items: Vec::new(),
    api_items: Vec::new(),
    truncated_items: 0,
    truncated_api_items: 0,
    omitted_access_roles: Vec::new(),
    omitted_access_roles_overflow: false,
};

fn has_layout_risk(
    record: &CppStructInfo,
    field_names: &[String],
    allow_single_field: bool,
) -> bool {
    if field_names.len() == 1 {
        return allow_single_field
            && record
                .total_estimated_size
                .map(|size| size <= record.cache_line_size.saturating_mul(2))
                .unwrap_or(true);
    }
    fields_may_share_cache_line(record, field_names)
}

fn has_neighbor_payload(record: &CppStructInfo, field_name: &str) -> bool {
    let Some(index) = record
        .fields
        .iter()
        .position(|field| field.name == field_name)
    else {
        return false;
    };

    let prev = index
        .checked_sub(1)
        .and_then(|idx| record.fields.get(idx))
        .map(|field| !field.is_cache_padded && !field.is_manual_padding)
        .unwrap_or(false);
    let next = record
        .fields
        .get(index + 1)
        .map(|field| !field.is_cache_padded && !field.is_manual_padding)
        .unwrap_or(false);

    prev || next
}

fn clean_atomic_alias_name(ty: &str) -> bool {
    let clean = ty
        .trim()
        .trim_start_matches("const ")
        .trim_start_matches("struct ")
        .trim_start_matches("class ");
    clean.ends_with("Counter")
        || clean.ends_with("Counters")
        || clean.ends_with("Atomic")
        || clean.contains("Atomic")
        || clean.contains("Counter")
}

fn hot_fields(record: &CppStructInfo) -> Vec<String> {
    let mut fields = Vec::new();
    fields.extend(record.atomic_fields.clone());
    fields.extend(record.hot_sync_fields.clone());
    fields.extend(record.hot_scalar_fields.clone());
    fields.sort();
    fields.dedup();
    fields
}

fn record_kind(record: &CppStructInfo) -> &'static str {
    match record.kind {
        super::types::CppRecordKind::Struct => "struct",
        super::types::CppRecordKind::Class => "class",
    }
}

#[allow(clippy::too_many_arguments)]
fn make_cpp_finding(
    category: RiskCategory,
    rule: CandidateKind,
    title: &'static str,
    severity: Severity,
    file: &str,
    line: usize,
    project_name: &str,
    snippet: String,
    suggestion: &'static str,
    confidence: f32,
    struct_name: Option<&str>,
    field_list: &[String],
    evidence_descs: &[String],
    evidence_set: Option<&CppEvidenceSet>,
) -> Finding {
    const MAX_SERIALIZED_EVIDENCE: usize = 12;
    // One call can mutate several distinct storage objects. Location and
    // source text alone would give those reports the same identity, letting
    // unordered summary traversal decide which object survives deduplication.
    let mut identity_fields = field_list.to_vec();
    identity_fields.sort();
    identity_fields.dedup();
    let identity = format!("{snippet}\n{struct_name:?}\n{identity_fields:?}");
    let finding_hash = stable_finding_hash(rule.identity_salt(), file, line, &identity);
    let relevant_item = |item: &&CppEvidenceItem| {
        item.field_name
            .as_ref()
            .is_none_or(|field| field_list.is_empty() || field_list.contains(field))
    };
    let mut usage_locations: Vec<UsageLocation> = evidence_set
        .map(|set| {
            set.items
                .iter()
                .filter(relevant_item)
                .map(|item| UsageLocation {
                    file: item.file.clone(),
                    line: item.line,
                    description: item.description.clone(),
                })
                .chain(set.api_items.iter().map(|item| UsageLocation {
                    file: item.file.clone(),
                    line: item.line,
                    description: item.description.clone(),
                }))
                .take(MAX_SERIALIZED_EVIDENCE)
                .collect()
        })
        .unwrap_or_default();
    if usage_locations.is_empty() {
        usage_locations.extend(evidence_descs.iter().map(|desc| UsageLocation {
            file: file.to_string(),
            line,
            description: desc.clone(),
        }));
    }
    let mut seen_locations = HashSet::new();
    usage_locations.retain(|location| {
        seen_locations.insert((
            location.file.clone(),
            location.line,
            location.description.clone(),
        ))
    });
    let access_evidence: Vec<AccessEvidenceContext> = evidence_set
        .map(|set| {
            set.items
                .iter()
                .filter(relevant_item)
                .take(MAX_SERIALIZED_EVIDENCE)
                .map(access_evidence_context)
                .collect()
        })
        .unwrap_or_default();

    let mut reported_fields = field_list.to_vec();
    if matches!(
        rule,
        CandidateKind::ContainerElements
            | CandidateKind::AtomicArray
            | CandidateKind::SiblingArrays
    ) {
        for access in &access_evidence {
            if access.access_kind.is_none()
                || access.semantic_contexts.iter().any(|context| {
                    matches!(
                        context.as_str(),
                        "cpp_thread_local_receiver"
                            | "cpp_nonescaping_local_receiver"
                            | "cpp_initialization_phase"
                    )
                })
            {
                continue;
            }
            reported_fields.extend(access.semantic_contexts.iter().filter_map(|context| {
                context
                    .strip_prefix("cpp_element_member_path:")
                    .map(str::to_string)
            }));
        }
        reported_fields.sort();
        reported_fields.dedup();
    }
    Finding {
        category,
        rule_id: crate::pattern_model::default_colocation_pattern(rule).rule_id(),
        candidate_kind: rule,
        related_candidate_kinds: Vec::new(),
        finding_group_id: String::new(),
        finding_occurrence_count: 1,
        title,
        severity,
        file: file.to_string(),
        line,
        crate_name: if project_name.is_empty() {
            None
        } else {
            Some(project_name.to_string())
        },
        snippet,
        suggestion,
        confidence,
        struct_name: struct_name.map(ToOwned::to_owned),
        symbol: finding_symbol(struct_name, field_list),
        field_list: reported_fields,
        static_pattern: None,
        layout_context: None,
        access_evidence,
        risk_factors: Vec::new(),
        concurrency_evidence: evidence_descs.to_vec(),
        usage_locations,
        finding_hash,
        storage_identity: None,
    }
}

pub(super) fn access_evidence_context(item: &CppEvidenceItem) -> AccessEvidenceContext {
    AccessEvidenceContext {
        evidence_kind: match item.kind {
            CppEvidenceKind::AtomicFieldOps => "atomic_field_operation",
            CppEvidenceKind::HotScalarWrite => "plain_field_write",
            CppEvidenceKind::ThreadSpawn => "thread_spawn",
            CppEvidenceKind::OpenMp => "openmp_parallelism",
            CppEvidenceKind::ParallelLibrary => "parallel_library",
            CppEvidenceKind::SharedOwnership => "shared_ownership",
            CppEvidenceKind::ConcurrentFieldAccess => "concurrent_field_access",
            CppEvidenceKind::CompilerSemanticAccess => "compiler_semantic_access",
            CppEvidenceKind::InlineMemberAccess => "inline_member_access",
            CppEvidenceKind::ContiguousElementAccess => "contiguous_element_access",
            CppEvidenceKind::LockProtected => "lock_protected",
            CppEvidenceKind::LoopHotness => "loop_hotness",
            CppEvidenceKind::ContiguousObjectStorage => "contiguous_object_storage",
            CppEvidenceKind::AllocatorObjectStorage => "allocator_object_storage",
        }
        .to_string(),
        access_kind: item.access_kind.as_ref().map(|kind| {
            match kind {
                CppAccessKind::Read => "read",
                CppAccessKind::Write => "write",
                CppAccessKind::ReadModifyWrite => "read_modify_write",
            }
            .to_string()
        }),
        field_name: item.field_name.clone(),
        hotness_score: item.hotness_score,
        in_concurrent_context: item.in_concurrent_context,
        access_mode: if item.kind == CppEvidenceKind::ContiguousElementAccess {
            "contiguous_element"
        } else if item.through_shared_indirection {
            "shared"
        } else {
            "unknown"
        }
        .to_string(),
        function_name: item.function_name.clone(),
        propagation_depth: usize::from(!item.concurrent_call_path.is_empty()),
        call_path: if item.concurrent_call_path.is_empty() {
            item.function_name.iter().cloned().collect()
        } else {
            item.concurrent_call_path.clone()
        },
        semantic_contexts: item
            .guard_ids
            .iter()
            .map(|guard| format!("cpp_guarded_by:{guard}"))
            .chain(
                item.through_thread_local
                    .then(|| "cpp_thread_local_receiver".to_string()),
            )
            .chain(
                item.through_nonescaping_local
                    .then(|| "cpp_nonescaping_local_receiver".to_string()),
            )
            .chain(
                item.through_automatic_receiver
                    .then(|| "cpp_automatic_receiver_unproven_sharing".to_string()),
            )
            .chain(
                item.initialization_phase
                    .then(|| "cpp_initialization_phase".to_string()),
            )
            .chain(
                item.in_record_constructor
                    .then(|| "cpp_record_construction_context".to_string()),
            )
            .chain(
                (item.kind == CppEvidenceKind::ContiguousElementAccess)
                    .then(|| "cpp_contiguous_element".to_string()),
            )
            .chain((!item.element_member_path.is_empty()).then(|| {
                format!(
                    "cpp_element_member_path:{}[].{}",
                    item.field_name.as_deref().unwrap_or(""),
                    item.element_member_path.join(".")
                )
            }))
            .collect(),
        through_shared_indirection: item.through_shared_indirection,
        through_raw_pointer: item.through_raw_pointer,
        file: item.file.clone(),
        line: item.line,
        description: item.description.clone(),
    }
}

trait CppFindingLayoutExt {
    fn with_cpp_layout_context(self, record: &CppStructInfo) -> Self;
}

impl CppFindingLayoutExt for Finding {
    fn with_cpp_layout_context(mut self, record: &CppStructInfo) -> Self {
        self.layout_context = Some(layout_context_for_record(record));
        self.storage_identity = Some(format!(
            "{}::{}@{}",
            record.file, record.qualified_name, record.line
        ));
        self
    }
}

fn layout_context_for_record(record: &CppStructInfo) -> LayoutContext {
    LayoutContext {
        language: "cpp".to_string(),
        struct_name: record.name.clone(),
        canonical_type: record.qualified_name.clone(),
        declaration_line: record.line,
        cache_line_size: record.cache_line_size,
        layout_certainty: if record.compiler_layout_exact {
            "exact"
        } else if record.cache_line_groups_precise {
            "estimated"
        } else {
            "symbolic"
        }
        .to_string(),
        fields: record
            .fields
            .iter()
            .map(|field| layout_field_context(field, record.cache_line_size))
            .collect(),
        cache_line_groups: record.cache_line_groups.clone(),
        cache_line_groups_precise: record.cache_line_groups_precise,
        repr_c: false,
        repr_rust: false,
        repr_align_bytes: record.align_bytes,
        repr_packed: record.is_packed,
        has_cache_padded: record.has_cache_padding,
        manual_padding_fields: record
            .fields
            .iter()
            .filter(|field| field.is_manual_padding)
            .map(|field| field.name.clone())
            .collect(),
        total_estimated_size: record.total_estimated_size,
        layout_source: if record.compiler_layout_exact {
            "cpp_compiler_exact"
        } else {
            crate::types::LayoutSource::CppEstimate.as_str()
        }
        .to_string(),
        used_rustc_layout: false,
    }
}

fn layout_field_context(field: &CppFieldInfo, cache_line_size: usize) -> LayoutFieldContext {
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

fn finding_symbol(struct_name: Option<&str>, field_list: &[String]) -> Option<String> {
    match (struct_name, field_list) {
        (Some(struct_name), [field]) => Some(format!("{struct_name}.{field}")),
        (Some(struct_name), _) => Some(struct_name.to_string()),
        (None, [field]) => Some(field.clone()),
        _ => None,
    }
}

fn with_risk_factors(mut finding: Finding, risk_factors: Vec<String>) -> Finding {
    finding.risk_factors = risk_factors;
    finding
}

fn sorted(fields: &HashSet<String>) -> Vec<String> {
    let mut values: Vec<String> = fields.iter().cloned().collect();
    values.sort();
    values
}

#[cfg(test)]
mod precision_tests {
    use super::*;
    use crate::cpp_detection::layout::collect_cpp_structs;
    use crate::cpp_detection::parser::parse_cpp_files;
    use crate::cpp_detection::types::CppFile;

    #[test]
    fn manual_padding_splits_colocation_components() {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.c".to_string(),
            source: r#"
                struct Candidate {
                    void *left;
                    unsigned long padding[16];
                    atomic_t right;
                };
            "#
            .to_string(),
        }]);
        let records = collect_cpp_structs(&files, "test", 64);
        let record = records
            .iter()
            .find(|record| record.name == "Candidate")
            .expect("candidate record");
        let accessed = HashSet::from(["left".to_string(), "right".to_string()]);
        let written = accessed.clone();
        assert!(
            strongest_colocated_component(record, &accessed, &written, false, false).is_empty(),
            "a cache-line-sized manual padding field must separate the two candidate fields"
        );
    }
}
