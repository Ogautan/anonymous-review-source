//! Evidence requirements for the default, reviewable C++ report. The broader
//! may-risk calculus remains available via --cpp-include-speculative; failing
//! this policy does not establish safety or absence of false sharing.

use crate::types::{CandidateKind, Finding};

use super::pattern::matching_record_index;
use super::types::{CppAccessKind, CppEvidenceKind, CppEvidenceSet, CppStructInfo};

struct ReviewReason {
    text: String,
    witnesses: Vec<super::types::CppEvidenceItem>,
}

pub(super) fn retain_reportable(
    findings: &mut Vec<Finding>,
    records: &[CppStructInfo],
    evidence: &[CppEvidenceSet],
) -> usize {
    let before = findings.len();
    findings.retain_mut(|finding| {
        let index = matching_record_index(finding, records);
        let record = index.map(|index| &records[index]);
        let facts = index.and_then(|index| evidence.get(index));
        // Clustering unions fields from several candidate rules. An unrelated
        // valid pair must not make every field in that union reviewable.
        if finding.static_pattern.as_ref().is_some_and(|pattern| {
            pattern.colocation_pattern == crate::types::ColocationPattern::SameObjectFields
        }) && let (Some(record), Some(facts)) = (record, facts)
        {
            let accesses = facts
                .items
                .iter()
                .filter(|item| {
                    item.access_kind.is_some()
                        && !item.initialization_phase
                        && !item.through_thread_local
                        && !item.through_nonescaping_local
                        && item
                            .field_name
                            .as_ref()
                            .is_some_and(|field| finding.field_list.contains(field))
                })
                .collect::<Vec<_>>();
            let mut supported = std::collections::HashSet::new();
            let candidate_fields = record
                .fields
                .iter()
                .filter(|field| finding.field_list.contains(&field.name))
                .collect::<Vec<_>>();
            for (index, left) in candidate_fields.iter().enumerate() {
                for right in candidate_fields.iter().skip(index + 1) {
                    let pair = accesses
                        .iter()
                        .copied()
                        .filter(|item| {
                            item.field_name
                                .as_deref()
                                .is_some_and(|name| name == left.name || name == right.name)
                        })
                        .collect::<Vec<_>>();
                    if same_object_pair_reason_with_roles(
                        record,
                        &pair,
                        &facts.method_roles,
                        Some(facts),
                    )
                    .is_some()
                    {
                        supported.insert(left.name.clone());
                        supported.insert(right.name.clone());
                    }
                }
            }
            // Keep a concrete lock member that guards a supported data field
            // in the serialized layout surface. It is not itself a second
            // writable role, but omitting it hides the padding/repair boundary
            // that the finding asks the reviewer to inspect.
            if !supported.is_empty() {
                for guard in candidate_fields.iter().filter(|field| {
                    field.is_hot_sync
                        && facts
                            .items
                            .iter()
                            .any(|item| item.guard_ids.iter().any(|guard| guard == &field.name))
                }) {
                    supported.insert(guard.name.clone());
                }
            }
            finding.field_list.retain(|field| supported.contains(field));
            if let Some(pattern) = &mut finding.static_pattern {
                pattern.witness_locations = finding
                    .field_list
                    .iter()
                    .map(|field| format!("{}.{}", record.name, field))
                    .collect();
            }
        }
        let Some(reason) = reportable_reason(finding, record, facts, records) else {
            return false;
        };
        for witness in &reason.witnesses {
            let rendered = super::rules::access_evidence_context(witness);
            if !finding.access_evidence.iter().any(|item| {
                item.file == rendered.file
                    && item.line == rendered.line
                    && item.field_name == rendered.field_name
                    && item.access_kind == rendered.access_kind
                    && item.function_name == rendered.function_name
            }) {
                finding.access_evidence.push(rendered);
            }
        }
        // The normal renderer keeps a small prefix of accesses. Preserve one
        // actual supporting concurrent witness even when it occurs after that
        // prefix, so the default reason is auditable in the JSON itself.
        if let Some(witness) = facts
            .into_iter()
            .flat_map(|facts| &facts.items)
            .find(|item| {
                item.in_concurrent_context
                    && item.access_kind.is_some()
                    && !item.initialization_phase
                    && !item.through_thread_local
                    && !item.through_nonescaping_local
                    && item
                        .field_name
                        .as_ref()
                        .is_some_and(|field| finding.field_list.contains(field))
            })
            && !finding.access_evidence.iter().any(|item| {
                item.file == witness.file
                    && item.line == witness.line
                    && item.field_name == witness.field_name
                    && item.in_concurrent_context
            })
        {
            finding
                .access_evidence
                .push(super::rules::access_evidence_context(witness));
        }
        if let Some(facts) = facts {
            for rendered in &mut finding.access_evidence {
                for role in &facts.method_roles {
                    if rendered.file == role.file
                        && rendered.line == role.line
                        && rendered.function_name.as_deref() == Some(role.function.as_str())
                        && rendered.field_name.as_deref() == Some(role.field.as_str())
                    {
                        let contexts = if role.entries.is_empty() {
                            vec!["cpp_no_resolved_runtime_entry".to_owned()]
                        } else {
                            role.entries
                                .iter()
                                .map(|entry| format!("cpp_runtime_entry:{entry}"))
                                .collect()
                        };
                        for context in contexts {
                            if !rendered.semantic_contexts.contains(&context) {
                                rendered.semantic_contexts.push(context);
                            }
                        }
                    }
                }
            }
        }
        let rendered_reason = format!("C++ 报告依据: {}", reason.text);
        if !finding.risk_factors.contains(&rendered_reason) {
            finding.risk_factors.push(rendered_reason);
        }
        true
    });
    before - findings.len()
}

fn reportable_reason(
    finding: &Finding,
    record: Option<&CppStructInfo>,
    facts: Option<&CppEvidenceSet>,
    records: &[CppStructInfo],
) -> Option<ReviewReason> {
    let accesses = facts
        .into_iter()
        .flat_map(|facts| &facts.items)
        .filter(|item| {
            item.access_kind.is_some()
                && !item.initialization_phase
                && !item.through_thread_local
                && !item.through_nonescaping_local
                && item
                    .field_name
                    .as_ref()
                    .is_some_and(|field| finding.field_list.contains(field))
        })
        .collect::<Vec<_>>();
    let concurrent = accesses.iter().any(|item| item.in_concurrent_context)
        || finding.access_evidence.iter().any(|item| {
            item.in_concurrent_context
                && item.access_kind.is_some()
                && !item.semantic_contexts.iter().any(|context| {
                    matches!(
                        context.as_str(),
                        "cpp_initialization_phase"
                            | "cpp_thread_local_receiver"
                            | "cpp_nonescaping_local_receiver"
                    )
                })
        });
    let synchronized = record.is_some_and(|record| {
        record
            .fields
            .iter()
            .any(|field| field.is_atomic || field.is_hot_sync)
    }) || accesses
        .iter()
        .any(|item| item.kind == CppEvidenceKind::AtomicFieldOps);
    let mutates_in = |names: &[&str]| {
        accesses.iter().any(|item| {
            matches!(
                item.access_kind,
                Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
            ) && item
                .function_name
                .as_deref()
                .is_some_and(|name| names.contains(&name.rsplit("::").next().unwrap_or(name)))
        })
    };
    // A reusable synchronization primitive is an explicit external API risk,
    // unlike an arbitrary object that merely contains an atomic member.
    let synchronization_protocol = synchronized
        && mutates_in(&[
            "lock",
            "try_lock",
            "tryLock",
            "lockShared",
            "enter",
            "acquire",
        ])
        && mutates_in(&["unlock", "unlockShared", "leave", "release"]);
    match finding.candidate_kind {
        CandidateKind::FieldGroup | CandidateKind::WriterNeighbor | CandidateKind::MixedFields => {
            // Specialize the theory's independent-access predicate using
            // actual callable access sets. Public visibility or atomic field
            // types establish capabilities, not distinct access roles. Keep
            // such unresolved API hypotheses in the speculative view.
            return same_object_pair_reason_with_roles(record?, &accesses, &facts?.method_roles, facts);
        }
        CandidateKind::ObjectInstances => {
            // A hot reader of adjacent objects is not an invalidating writer.
            // Constructor/fresh initialization writes and pointee payload
            // mutations must not supply a write to these object slots.
            let runtime_slot_write = accesses.iter().any(|item| {
                item.kind != CppEvidenceKind::ContiguousElementAccess
                    && matches!(
                        item.access_kind,
                        Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                    )
            });
            let slots = accesses
                .iter()
                .copied()
                .filter(|item| item.kind != CppEvidenceKind::ContiguousElementAccess)
                .collect::<Vec<_>>();
            let bound_worker_boundary = finding.access_evidence.iter().any(|item|
                item.evidence_kind == "direct_worker_partition" && item.in_concurrent_context
                    && item.semantic_contexts.iter().any(|c| c.starts_with("cpp_worker_record_peer:")))
                && finding.access_evidence.iter().filter(|item| item.in_concurrent_context
                    && matches!(item.access_kind.as_deref(), Some("write" | "read_modify_write")))
                    .count() >= 2;
            if bound_worker_boundary {
                Some("已绑定不同 pthread worker 的连续记录，内联数组边界有具体写入对与字节间距证据")
            } else if !cross_object_layout_may_interfere(record?, &finding.field_list)
                || !runtime_slot_write || !has_recurrent_writer(&slots) {
                None
            } else if synchronization_protocol {
                Some("存在实际修改同步状态的获取/释放 API，保留外部相邻实例使用风险")
            } else if synchronized
                && facts.is_some_and(CppEvidenceSet::has_contiguous_object_storage)
                && slots.iter().any(|item| {
                    matches!(item.access_kind, Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite))
                        && (item.kind == CppEvidenceKind::AtomicFieldOps
                            || record.is_some_and(|record| record.fields.iter().any(|field| {
                                item.field_name.as_deref() == Some(field.name.as_str())
                                    && (field.is_atomic || field.is_hot_sync)
                            })))
                })
            {
                Some("候选同步字段有实际写入，且对象具有具体连续实例存储及未隔离 stride 风险")
            } else if facts.is_some_and(CppEvidenceSet::has_contiguous_object_storage)
                && slots.iter().any(|item| {
                    item.in_concurrent_context
                        && matches!(item.access_kind,
                            Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite))
                })
            {
                // A parallel reader of the wrapper cannot lend its execution
                // domain to unrelated serial header updates. Atomic/protocol
                // API risks have their own paths above; an unresolved ordinary
                // writer remains in the speculative view, not a safety proof.
                Some("存在连续对象存储，且候选字段有实际并发访问")
            } else {
                None
            }
        }
        CandidateKind::SeparateAllocations => {
            if !cross_object_layout_may_interfere(record?, &finding.field_list) {
                None
            } else if facts.is_some_and(|facts| {
                facts.items.iter().any(|item| {
                    item.kind == CppEvidenceKind::AllocatorObjectStorage
                        && item.description.contains("[unrounded aligned_alloc size]")
                })
            }) {
                Some("已识别未按 cache-line 取整的对齐分配及实际访问")
            } else if concurrent
                && has_recurrent_writer(&accesses)
                && facts.is_some_and(CppEvidenceSet::has_allocator_object_storage)
            {
                Some("分配对象的候选字段存在实际并发访问，且写者自身具有重复写依据")
            } else {
                None
            }
        }
        CandidateKind::IndexedWrites => {
            // Literal-only initialization is not a repeated state transition.
            // Dynamic data and bound aliases remain unresolved API risks; do
            // not confuse plain store syntax with proof of initialization.
            let has_selected_writer = finding
                .access_evidence
                .iter()
                .any(|item| {
                    !item.semantic_contexts.iter().any(|c| c == "cpp_terminal_thread_store")
                    // Read-only indexed traversal cannot invalidate another
                    // thread's cache line. Require a write or read-modify-
                    // write witness before treating the access as a sharing
                    // candidate.
                    && matches!(
                        item.access_kind.as_deref(),
                        Some("write" | "read_modify_write")
                    )
                    // A dynamic-looking subscript is common in ordinary
                    // single-threaded loops. Preserve the API/partition
                    // escape hatch, but require actual concurrent evidence
                    // for regular stores and read-modify-write updates.
                    && (item.in_concurrent_context
                        || (item.evidence_kind == "api_index_partition"
                            && item.function_name.is_some()
                            && item.semantic_contexts.iter().any(|c| c == "cpp_direct_partition")
                            && !item.semantic_contexts.iter().any(|c| c == "cpp_literal_slot_store"))
                        || item.evidence_kind == "static_thread_indexed_write")
                    // Being inside a parallel body does not identify two
                    // independently selected elements: a serial inner loop
                    // can update worker-private scratch or the same shared
                    // locations in every worker. Require the selected writer
                    // itself to carry an index partition witness. Unresolved
                    // region-only hypotheses remain in speculative output.
                    && (item.semantic_contexts.iter().any(|context| {
                        matches!(context.as_str(), "cpp_direct_partition" | "cpp_api_index_partition" | "cpp_runtime_thread_identity")
                    }) || matches!(item.evidence_kind.as_str(), "static_thread_indexed_write" | "direct_worker_partition"))
                });
            has_selected_writer.then_some(
                "选中的连续元素写访问本身具有运行时、并行循环或条件 API 分区来源；仅处于并行区域不足以建立元素访问对",
            )
        }
        CandidateKind::SiblingArrays => {
            // Updating an ordinary inline array is also the normal sequential
            // hash/codec pattern. Unlike a worker-indexed slot, it has no
            // partition witness. Require concurrency on these fields, or
            // synchronization semantics belonging to these selected fields.
            let selected_sync = accesses
                .iter()
                .any(|item| item.kind == CppEvidenceKind::AtomicFieldOps)
                || record.is_some_and(|record| {
                    record.fields.iter().any(|field| {
                        finding.field_list.contains(&field.name)
                            && (field.is_atomic || field.is_hot_sync
                                || super::evidence::container_has_atomic_elements(field)
                                || super::evidence::container_field_element_name(&field.ty_str, field.element_type.as_deref())
                                    .is_some_and(|element| {
                                        let owners = records.iter().filter(|record| record.name == element).collect::<Vec<_>>();
                                        matches!(owners.as_slice(), [owner] if owner.fields.iter().any(|field| field.is_atomic))
                                    }))
                    })
                });
            (has_recurrent_writer(&accesses) && (concurrent || selected_sync)).then_some(
                "连续字段具有状态更新，并且候选字段本身有并发或同步语义；非仅顺序数组处理",
            )
        }
        CandidateKind::StaticData => finding.access_evidence.iter().any(|item| {
            matches!(item.access_kind.as_deref(), Some("write" | "read_modify_write"))
                && (item.in_concurrent_context || item.evidence_kind == "static_thread_indexed_write")
        }).then_some("全局连续存储具有实际并发写或明确索引分区/可变分区API证据；静态存储和普通顺序写本身不足以建立线程干扰"),
        CandidateKind::ContainerElements => {
            let runtime_payload_write = accesses.iter().any(|item| {
                item.kind == CppEvidenceKind::ContiguousElementAccess
                    && matches!(item.access_kind, Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite))
            });
            // Reads of a container payload do not create invalidations.  A
            // reportable candidate therefore needs a repeated runtime write
            // (or read-modify-write) to the selected elements; declaration,
            // publication, and read-only traversal remain speculative.
            let payload_accesses = accesses.iter().copied().filter(|item| {
                item.kind == CppEvidenceKind::ContiguousElementAccess
            }).collect::<Vec<_>>();
            (runtime_payload_write && has_recurrent_writer(&payload_accesses))
                .then_some("已识别连续元素访问；候选元素具有重复运行期写入，发布前填充不能替代冲突证据")
        }
        CandidateKind::AtomicArray => {
            // An atomic alias array declaration only describes a possible
            // layout hazard.  Keep it reportable when the selected array is
            // actually mutated at runtime and the mutation has either a
            // concurrent witness or an explicit indexed/API partition path.
            // This avoids turning every pool of atomic objects into a finding
            // when it is never touched (or is only initialized).
            let runtime_write = accesses.iter().any(|item| {
                matches!(
                    item.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                ) && !item.initialization_phase
            });
            let partitioned = finding.access_evidence.iter().any(|item| {
                matches!(
                    item.evidence_kind.as_str(),
                    "api_index_partition" | "static_thread_indexed_write"
                )
            });
            (runtime_write
                && (concurrent || partitioned)
                && has_recurrent_writer(&accesses))
                .then_some("atomic alias/wrapper 数组具有实际运行期写入及并发或索引分片证据")
        }
    }
    .map(|text| ReviewReason {
        text: text.to_owned(),
        witnesses: Vec::new(),
    })
}

/// Reject only a selected cross-object relation separated by a usable layout.
/// Unknown stride is not isolation: template payloads and opaque synchronization
/// members retain their may-risk, subject to the other reportability checks.
fn cross_object_layout_may_interfere(record: &CppStructInfo, names: &[String]) -> bool {
    let selected = record
        .fields
        .iter()
        .filter(|f| names.contains(&f.name))
        .collect::<Vec<_>>();
    selected.iter().any(|left| {
        selected
            .iter()
            .any(|right| super::layout::fields_may_share_across_objects(record, left, right))
    })
}

/// The same pair must witness both layout interference and separable access
/// roles. A writer on one cache line cannot borrow a read/read pair on another
/// line to establish a false-sharing conflict.
#[cfg(test)]
fn same_object_pair_reason(
    record: &CppStructInfo,
    accesses: &[&super::types::CppEvidenceItem],
) -> Option<ReviewReason> {
    same_object_pair_reason_with_roles(record, accesses, &[], None)
}

fn same_object_pair_reason_with_roles(
    record: &CppStructInfo,
    accesses: &[&super::types::CppEvidenceItem],
    roles: &[super::types::CppMethodRole],
    facts: Option<&CppEvidenceSet>,
) -> Option<ReviewReason> {
    // A vector payload is a separate storage domain. Writes through its
    // elements cannot witness a write to the adjacent object header fields.
    let accesses = accesses
        .iter()
        .copied()
        .filter(|item| item.kind != CppEvidenceKind::ContiguousElementAccess)
        .filter(|item| !item.through_automatic_receiver)
        .filter(|item| {
            item.in_concurrent_context
                || method_role(item, roles).is_none_or(|role| !role.entries.is_empty())
        })
        .collect::<Vec<_>>();
    let fields = record
        .fields
        .iter()
        .filter(|field| {
            accesses
                .iter()
                .any(|item| item.field_name.as_deref() == Some(field.name.as_str()))
        })
        .collect::<Vec<_>>();
    for (i, left) in fields.iter().enumerate() {
        for right in fields.iter().skip(i + 1) {
            if left.name == right.name
                || left
                    .bitfield_group
                    .is_some_and(|group| right.bitfield_group == Some(group))
            {
                // Alternative declarations with the same name cannot supply
                // two independently identified fields for the access witness.
                continue;
            }
            let names = [left.name.clone(), right.name.clone()];
            // Approximate offsets use a fallback size for unknown members.
            // Those placeholders can enumerate speculative pairs but cannot
            // certify the byte distance of a default reviewable finding.
            // Unknown members before the pair do not invalidate its relative
            // layout: the base cache-line phase is already existential.
            let start = record
                .fields
                .iter()
                .position(|field| std::ptr::eq(field, *left))?;
            let end = record
                .fields
                .iter()
                .position(|field| std::ptr::eq(field, *right))?;
            if !record.cache_line_groups_precise
                && record.fields[start..=end]
                    .iter()
                    .any(|field| field.estimated_size.is_none())
            {
                continue;
            }
            if !super::layout::fields_may_share_cache_line(record, &names) {
                continue;
            }
            let pair = accesses
                .iter()
                .copied()
                .filter(|item| {
                    item.field_name
                        .as_ref()
                        .is_some_and(|field| names.contains(field))
                })
                .collect::<Vec<_>>();
            // Omitted memberships only veto separability. They never supply
            // accesses, concurrency, guards, or recurrence witnesses.
            if facts.is_some_and(|facts| facts.omitted_access_roles_overflow) {
                continue;
            }
            let omitted = facts
                .into_iter()
                .flat_map(|facts| &facts.omitted_access_roles)
                .filter(|role| names.contains(&role.field))
                .cloned()
                .collect::<Vec<_>>();
            if !super::pattern::has_distinct_cpp_access_roles(&pair) {
                continue;
            }
            if left
                .guarded_by
                .as_ref()
                .is_some_and(|guard| right.guarded_by.as_ref() == Some(guard))
                || accesses_share_guard(&pair)
            {
                continue;
            }
            // External concurrency plus an atomic type does not turn a
            // one-shot setter and unrelated readers into a recurrent conflict.
            // Look for a state transition in the mutating role itself. A real
            // concurrent writer remains eligible even for blind stores.
            if !has_recurrent_writer(&pair) {
                continue;
            }
            let witnesses = role_witnesses_with_roles(
                &pair,
                // A parallel read cannot lend its execution domain to a
                // serial orchestration write. A concrete synchronization
                // stream still supports the legitimate write/read case in
                // which the foreground writer overlaps a remote atomic read.
                |conflict, _role_evidence| {
                    conflict.iter().any(|item| {
                        item.in_concurrent_context
                            && matches!(
                                item.access_kind,
                                Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                            )
                    }) || ((left.is_atomic
                        || left.is_hot_sync
                        || right.is_atomic
                        || right.is_hot_sync)
                        && conflict.iter().any(|item| item.in_concurrent_context))
                },
                roles,
                &omitted,
            );
            if !witnesses.is_empty() {
                return Some(ReviewReason {
                    text: format!(
                        "字段对 {} / {} 具有同线可能性、实际并发访问及可分离读写角色",
                        left.name, right.name
                    ),
                    witnesses,
                });
            }
            // Without an explicit parallel context, accesses observed only
            // inside one callable are ordinary sequential state transitions.
            // An atomic type alone cannot establish two thread roles. Require
            // the external-API fallback to cross callable/file boundaries so
            // that a setter and its own reader do not become a false pair.
            let distinct_call_sites = pair.iter().any(|left| {
                pair.iter().any(|right| {
                    left.function_name.is_some()
                        && right.function_name.is_some()
                        && (left.function_name != right.function_name || left.file != right.file)
                })
            });
            if !distinct_call_sites {
                continue;
            }
            if left.is_atomic
                || left.is_hot_sync
                || right.is_atomic
                || right.is_hot_sync
                || pair
                    .iter()
                    .any(|item| item.kind == CppEvidenceKind::AtomicFieldOps)
            {
                // Require recurrence in the synchronization stream itself,
                // including repeated remote reads: writes to a neighboring
                // field can invalidate a reader's cache line as well.
                let recurring_sync_stream = |items: &[&super::types::CppEvidenceItem]| {
                    items.iter().any(|item| {
                        let sync = item.field_name.as_deref().is_some_and(|name| {
                            [*left, *right].iter().any(|field| {
                                field.name == name && (field.is_atomic || field.is_hot_sync)
                            })
                        }) || item.kind == CppEvidenceKind::AtomicFieldOps;
                        let repeating_write = matches!(
                            item.access_kind,
                            Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                        ) && (has_recurrent_writer(&[*item])
                            || item.hotness_score >= 5.0);
                        let independent_read_stream = item.access_kind == Some(CppAccessKind::Read)
                            && item.hotness_score >= 5.0
                            && items.iter().any(|writer| {
                                writer.field_name != item.field_name
                                    && (writer.file != item.file
                                        || writer.function_name != item.function_name)
                                    && has_recurrent_writer(&[*writer])
                            });
                        sync && (repeating_write || independent_read_stream)
                    })
                };
                let witnesses = role_witnesses_with_roles(
                    &pair,
                    |_conflict, role_evidence| recurring_sync_stream(role_evidence),
                    roles,
                    &omitted,
                );
                if witnesses.is_empty() {
                    continue;
                }
                return Some(ReviewReason {
                    text: format!(
                        "字段对 {} / {} 具有同线可能性、atomic/同步状态及可分离读写角色（外部并发假设）",
                        left.name, right.name
                    ),
                    witnesses,
                });
            }
        }
    }
    None
}

fn has_recurrent_writer(accesses: &[&super::types::CppEvidenceItem]) -> bool {
    accesses.iter().any(|writer| {
        // Moving from an existing object is not fresh-object initialization,
        // but a single constructor RMW also does not establish recurrence.
        // Keep its access evidence; require independent repetition/concurrency
        // before using it as the default report's invalidating writer. Other
        // records updated by a constructor (e.g. a shared RAII counter) are
        // deliberately not classified as this record's construction phase.
        let construction_only = writer.in_record_constructor && writer.hotness_score <= 1.0;
        matches!(
            writer.access_kind,
            Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
        ) && (writer.in_concurrent_context
            || (writer.access_kind == Some(CppAccessKind::ReadModifyWrite) && !construction_only))
    })
}

fn accesses_share_guard(accesses: &[&super::types::CppEvidenceItem]) -> bool {
    accesses.first().is_some_and(|first| {
        first
            .guard_ids
            .iter()
            .any(|guard| accesses.iter().all(|item| item.guard_ids.contains(guard)))
    })
}

/// Retain the source witnesses of two actual access roles, not the renderer's
/// unrelated prefix of API and type-usage descriptions.
#[cfg(test)]
fn role_witnesses(
    accesses: &[&super::types::CppEvidenceItem],
) -> Vec<super::types::CppEvidenceItem> {
    role_witnesses_matching(accesses, |_, _| true, &[])
}

fn method_role<'a>(
    access: &super::types::CppEvidenceItem,
    roles: &'a [super::types::CppMethodRole],
) -> Option<&'a super::types::CppMethodRole> {
    let mut matching = roles.iter().filter(|role| {
        role.file == access.file
            && role.line == access.line
            && access.function_name.as_deref() == Some(role.function.as_str())
            && access.field_name.as_deref() == Some(role.field.as_str())
    });
    let first = matching.next()?;
    matching.next().is_none().then_some(first)
}

fn role_witnesses_with_roles(
    accesses: &[&super::types::CppEvidenceItem],
    eligible: impl Fn(&[&super::types::CppEvidenceItem], &[&super::types::CppEvidenceItem]) -> bool,
    roles: &[super::types::CppMethodRole],
    omitted: &[super::types::CppOmittedAccessRole],
) -> Vec<super::types::CppEvidenceItem> {
    if roles.is_empty() {
        return role_witnesses_matching(accesses, eligible, omitted);
    }
    let mut projected = Vec::new();
    for &access in accesses {
        let entries = method_role(access, roles).map(|role| &role.entries);
        if let Some(entries) = entries {
            if entries.is_empty() && access.in_concurrent_context {
                projected.push((access.clone(), access));
            }
            for entry in entries {
                let mut copy = access.clone();
                // These copies only check role separability; returned source
                // witnesses retain the actual callee and source locations.
                copy.file = "cpp_runtime_entry".into();
                copy.function_name = Some(entry.clone());
                projected.push((copy, access));
            }
        } else {
            projected.push((access.clone(), access));
        }
    }
    let items = projected.iter().map(|(item, _)| item).collect::<Vec<_>>();
    let mut projected_omissions = Vec::new();
    for role in omitted {
        if role.runtime_entries.is_empty() {
            projected_omissions.push(role.clone());
        } else {
            for entry in &role.runtime_entries {
                let mut copy = role.clone();
                copy.file = "cpp_runtime_entry".into();
                copy.function = entry.clone();
                projected_omissions.push(copy);
            }
        }
    }
    let selected = role_witnesses_matching(&items, eligible, &projected_omissions);
    let mut sources = Vec::new();
    for (item, source) in &projected {
        if selected.iter().any(|w| {
            w.file == item.file
                && w.function_name == item.function_name
                && w.line == item.line
                && w.field_name == item.field_name
                && w.access_kind == item.access_kind
        }) && !sources.iter().any(|s: &super::types::CppEvidenceItem| {
            s.file == source.file
                && s.line == source.line
                && s.field_name == source.field_name
                && s.access_kind == source.access_kind
                && s.function_name == source.function_name
        }) {
            sources.push((*source).clone());
        }
    }
    sources
}

fn role_witnesses_matching(
    accesses: &[&super::types::CppEvidenceItem],
    eligible: impl Fn(&[&super::types::CppEvidenceItem], &[&super::types::CppEvidenceItem]) -> bool,
    omitted: &[super::types::CppOmittedAccessRole],
) -> Vec<super::types::CppEvidenceItem> {
    let mut functions = Vec::new();
    for access in accesses {
        if let Some(function) = &access.function_name {
            let key = (&access.file, function);
            if !functions.contains(&key) {
                functions.push(key);
            }
        }
    }
    for (i, left) in functions.iter().enumerate() {
        for right in functions.iter().skip(i + 1) {
            let pair = accesses
                .iter()
                .copied()
                .filter(|a| {
                    a.function_name
                        .as_ref()
                        .is_some_and(|f| [*left, *right].contains(&(&a.file, f)))
                })
                .collect::<Vec<_>>();
            if !super::pattern::has_distinct_cpp_access_roles(&pair)
                || !super::pattern::has_distinct_cpp_access_roles_with_omissions(&pair, omitted)
                || accesses_share_guard(&pair)
                || !has_recurrent_writer(&pair)
            {
                continue;
            }
            // The callable access sets establish separability, but their
            // union is not a conflict witness. Protection and observed
            // parallelism belong to the actual accesses. Recurrence is an
            // existing report-priority criterion, not a theory predicate: a
            // writer role may update a cached value alongside an atomic RMW.
            // Such support must belong to that writer and compatible guards.
            for a in &pair {
                for b in &pair {
                    if a.field_name.is_none()
                        || b.field_name.is_none()
                        || a.field_name == b.field_name
                        || (a.file == b.file && a.function_name == b.function_name)
                        || a.access_kind.is_none()
                        || b.access_kind.is_none()
                    {
                        continue;
                    }
                    let conflict = [*a, *b];
                    let role_evidence = pair
                        .iter()
                        .copied()
                        .filter(|item| {
                            conflict.iter().any(|endpoint| {
                                endpoint.file == item.file
                                    && endpoint.function_name == item.function_name
                                    && endpoint
                                        .guard_ids
                                        .iter()
                                        .all(|guard| item.guard_ids.contains(guard))
                                    && item
                                        .guard_ids
                                        .iter()
                                        .all(|guard| endpoint.guard_ids.contains(guard))
                            })
                        })
                        .collect::<Vec<_>>();
                    let recurrent_writer_role = conflict.iter().any(|writer| {
                        matches!(
                            writer.access_kind,
                            Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                        ) && role_evidence.iter().any(|support| {
                            writer.file == support.file
                                && writer.function_name == support.function_name
                                && has_recurrent_writer(&[*support])
                        })
                    });
                    if !accesses_share_guard(&conflict)
                        && recurrent_writer_role
                        && eligible(&conflict, &role_evidence)
                    {
                        let mut witnesses = vec![(*a).clone(), (*b).clone()];
                        for support in role_evidence {
                            if (has_recurrent_writer(&[support]) || support.hotness_score >= 5.0)
                                && !witnesses.iter().any(|w| {
                                    w.file == support.file
                                        && w.function_name == support.function_name
                                        && w.line == support.line
                                        && w.field_name == support.field_name
                                        && w.access_kind == support.access_kind
                                        && w.hotness_score == support.hotness_score
                                })
                            {
                                witnesses.push(support.clone());
                            }
                        }
                        return witnesses;
                    }
                }
            }
        }
    }
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpp_detection::{evidence, layout, parser, types::CppFile};

    #[test]
    fn cross_object_reviewability_uses_selected_intervals_and_known_stride() {
        for block in [32, 64, 128] {
            let files = parser::parse_cpp_files(vec![CppFile {
                path: "slots.hpp".into(),
                source: "struct Slot { int first; char gap[256]; int last; }; struct Unknown { Opaque value; int count; };".into(),
            }]);
            let records = layout::collect_cpp_structs(&files, "fixture", block);
            let slot = records.iter().find(|r| r.name == "Slot").unwrap();
            assert!(!cross_object_layout_may_interfere(slot, &["last".into()]));
            // Large objects can still share at their touching boundaries.
            assert!(cross_object_layout_may_interfere(
                slot,
                &["first".into(), "last".into()]
            ));
            let unknown = records.iter().find(|r| r.name == "Unknown").unwrap();
            assert!(cross_object_layout_may_interfere(
                unknown,
                &["count".into()]
            ));
        }
    }

    #[test]
    fn cross_object_byte_intervals_respect_legal_base_alignment() {
        for block in [32, 64, 128] {
            for (prefix, expected) in [(block - 8, false), (block - 16, true)] {
                let files = parser::parse_cpp_files(vec![CppFile {
                    path: "aligned.hpp".into(),
                    source: format!(
                        "struct Slot {{ char prefix[{prefix}]; uint64_t first; uint64_t last; }};"
                    ),
                }]);
                let records = layout::collect_cpp_structs(&files, "fixture", block);
                assert_eq!(
                    cross_object_layout_may_interfere(
                        &records[0],
                        &["first".into(), "last".into()]
                    ),
                    expected,
                    "B={block}, prefix={prefix}"
                );
                let mut unknown = records[0].clone();
                unknown.total_estimated_size = None;
                assert!(cross_object_layout_may_interfere(
                    &unknown,
                    &["first".into(), "last".into()]
                ));
            }
        }
    }

    #[test]
    fn cached_value_store_keeps_the_recurrence_of_its_compatible_writer_role() {
        let files = parser::parse_cpp_files(vec![CppFile {
            path: "queue.hpp".into(),
            source: "struct State { std::atomic<int> tail; int cached; };\nvoid produce(State *s) { int old = s->tail.load(); s->cached = remote(); s->tail.store(old + 1); }\nint consume(State *s) { return s->tail.load(); }\n".into(),
        }]);
        let records = layout::collect_cpp_structs(&files, "fixture", 64);
        let facts = evidence::collect_cpp_evidence(&files, &records);
        let accesses = facts[0]
            .items
            .iter()
            .filter(|a| a.access_kind.is_some())
            .collect::<Vec<_>>();
        let reason = same_object_pair_reason(&records[0], &accesses)
            .expect("cached producer writes remain a may-risk");
        assert!(
            reason
                .witnesses
                .iter()
                .any(|a| a.field_name.as_deref() == Some("cached")
                    && a.access_kind == Some(CppAccessKind::Write))
        );
        assert!(
            reason
                .witnesses
                .iter()
                .any(|a| a.function_name.as_deref() == Some("consume"))
        );
        assert!(
            reason
                .witnesses
                .iter()
                .any(|a| a.field_name.as_deref() == Some("tail")
                    && a.access_kind == Some(CppAccessKind::ReadModifyWrite))
        );
    }

    #[test]
    fn protected_rmw_cannot_lend_recurrence_to_a_different_unprotected_store() {
        for (concurrent_store, expected) in [(false, false), (true, true)] {
            let files = parser::parse_cpp_files(vec![CppFile {
                path: "pair.hpp".into(),
                source: "struct State { std::atomic<int> counter; int value; };\nvoid update(State *s) { s->counter.fetch_add(1); s->counter.store(1); }\nvoid inspect(State *s) { consume(s->value); }\n".into(),
            }]);
            let records = layout::collect_cpp_structs(&files, "fixture", 64);
            let mut facts = evidence::collect_cpp_evidence(&files, &records);
            for item in &mut facts[0].items {
                if item.access_kind == Some(CppAccessKind::ReadModifyWrite)
                    || item.field_name.as_deref() == Some("value")
                {
                    item.guard_ids = vec!["gate".into()];
                }
                if item.access_kind == Some(CppAccessKind::Write) {
                    item.in_concurrent_context = concurrent_store;
                }
            }
            let accesses = facts[0]
                .items
                .iter()
                .filter(|a| a.access_kind.is_some())
                .collect::<Vec<_>>();
            let reason = same_object_pair_reason(&records[0], &accesses);
            assert_eq!(reason.is_some(), expected);
            if let Some(reason) = reason {
                assert_eq!(reason.witnesses.len(), 2);
                assert!(reason.witnesses.iter().any(|a| {
                    a.access_kind == Some(CppAccessKind::Write) && a.in_concurrent_context
                }));
            }
        }
    }

    #[test]
    fn concurrent_same_location_read_cannot_lend_parallelism_to_another_pair() {
        for atomic in [false, true] {
            let files = parser::parse_cpp_files(vec![CppFile {
                path: "pair.hpp".into(),
                source: format!(
                    "struct State {{ {} counter; int value; }};\nvoid update(State *s) {{ ++s->counter; }}\nvoid inspect(State *s) {{ consume(s->counter); consume(s->value); }}\n",
                    if atomic { "std::atomic<int>" } else { "int" }
                ),
            }]);
            let records = layout::collect_cpp_structs(&files, "fixture", 64);
            let mut facts = evidence::collect_cpp_evidence(&files, &records);
            for item in &mut facts[0].items {
                item.in_concurrent_context = item.function_name.as_deref() == Some("inspect")
                    && item.field_name.as_deref() == Some("counter");
            }
            let accesses = facts[0]
                .items
                .iter()
                .filter(|a| a.access_kind.is_some())
                .collect::<Vec<_>>();
            let reason = same_object_pair_reason(&records[0], &accesses);
            assert_eq!(reason.is_some(), atomic);
            if let Some(reason) = reason {
                // A valid external API hypothesis is still available. An
                // unrelated concrete thread access neither proves nor vetoes it.
                assert!(reason.text.contains("外部并发假设"));
            }
        }
    }

    #[test]
    fn unguarded_same_location_reads_do_not_break_distinct_location_protection() {
        for size in [32, 64, 128] {
            for (peer_guard, peer_write, expected) in [
                ("gate", false, false),
                ("other_gate", false, true),
                ("", false, true),
                ("gate", true, true),
            ] {
                let files = parser::parse_cpp_files(vec![CppFile {
                    path: "protected.hpp".into(),
                    source: "struct State { std::atomic<int> counter; int value; };\nvoid update(State *s) { s->counter.fetch_add(1); }\nvoid inspect(State *s) { consume(s->counter.load()); consume(s->value); }\n".into(),
                }]);
                let records = layout::collect_cpp_structs(&files, "fixture", size);
                let mut facts = evidence::collect_cpp_evidence(&files, &records);
                for access in &mut facts[0].items {
                    if access.function_name.as_deref() == Some("update") {
                        access.guard_ids = vec!["gate".into()];
                    } else if access.field_name.as_deref() == Some("value") {
                        access.guard_ids = if peer_guard.is_empty() {
                            Vec::new()
                        } else {
                            vec![peer_guard.into()]
                        };
                        if peer_write && access.access_kind.is_some() {
                            access.access_kind = Some(CppAccessKind::ReadModifyWrite);
                        }
                    }
                }
                // An unguarded read in another role remains a real conflict
                // when the peer is written, even if other accesses are locked.
                if peer_write {
                    let mut read = facts[0]
                        .items
                        .iter()
                        .find(|a| {
                            a.field_name.as_deref() == Some("counter")
                                && a.access_kind == Some(CppAccessKind::Read)
                        })
                        .unwrap()
                        .clone();
                    read.function_name = Some("observe".into());
                    read.hotness_score = 6.0;
                    facts[0].items.push(read);
                }
                let accesses = facts[0]
                    .items
                    .iter()
                    .filter(|a| a.access_kind.is_some())
                    .collect::<Vec<_>>();
                assert_eq!(
                    same_object_pair_reason(&records[0], &accesses).is_some(),
                    expected,
                    "size={size} guard={peer_guard} peer_write={peer_write}"
                );
            }
        }
    }

    #[test]
    fn external_pair_parallelism_needs_recurrence_on_the_sync_field() {
        for (notification, expected) in [
            ("flag.store(1);", false),
            ("flag.fetch_add(1);", true),
            ("auto old = flag.load(); flag.store(old + 1);", true),
            ("auto old = flag.load(); old = 1; flag.store(old);", false),
            ("for (int i=0; i<1000; ++i) flag.store(i);", true),
            ("for (int i=0; i<1000; ++i) consume(flag.load());", true),
            ("consume(flag.load());", false),
        ] {
            let files = parser::parse_cpp_files(vec![CppFile {
                path: "pair.cpp".into(),
                source: format!(
                    r#"
                struct State {{ std::atomic<int> flag; char * cursor;
                    void inspect() {{ consume(flag.load()); }}
                    void notify() {{ {notification} }}
                    void work() {{ for (int i=0; i<1000; ++i) ++cursor; }}
                }};
            "#
                ),
            }]);
            let records = layout::collect_cpp_structs(&files, "fixture", 64);
            let mut facts = evidence::collect_cpp_evidence(&files, &records);
            let accesses = facts[0]
                .items
                .iter()
                .filter(|a| a.access_kind.is_some())
                .collect::<Vec<_>>();
            let reason = same_object_pair_reason(&records[0], &accesses);
            assert_eq!(reason.is_some(), expected, "{notification}");
            if let Some(reason) = reason {
                assert!(
                    reason
                        .witnesses
                        .iter()
                        .any(|item| item.function_name.as_deref() == Some("notify")
                            && (matches!(
                                item.access_kind,
                                Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                            ) || (item.access_kind == Some(CppAccessKind::Read)
                                && item.hotness_score >= 5.0))),
                    "the reported roles must contain the recurring synchronization stream"
                );
            }
            for item in &mut facts[0].items {
                if item.field_name.as_deref() == Some("flag") {
                    item.in_concurrent_context = true;
                }
            }
            let concurrent_accesses = facts[0]
                .items
                .iter()
                .filter(|a| a.access_kind.is_some())
                .collect::<Vec<_>>();
            assert!(
                same_object_pair_reason(&records[0], &concurrent_accesses).is_some(),
                "actual concurrency must remain eligible: {notification}"
            );
        }
    }

    #[test]
    fn recurrent_writer_requires_value_dependency_not_a_prior_flag_check() {
        for (body, expected) in [
            ("if (state) return; state = true;", false),
            ("if (state.load()) return; state.store(true);", false),
            ("state.exchange(true);", true),
            ("state = !state;", true),
            ("state = state + 1;", true),
            ("state = other.state;", false),
            ("state = sizeof(state);", false),
            ("state = (state = 1);", false),
            (
                "auto previous = state.load(); state.store(previous + 1);",
                true,
            ),
            (
                "auto previous = state.load(); --previous; state.store(previous);",
                true,
            ),
            (
                "auto previous = state.load(); auto &element = values[previous & 15]; state.store(previous + 1);",
                true,
            ),
            (
                "auto previous = state.load(); previous = 1; state.store(previous);",
                false,
            ),
            (
                "auto previous = state.load(); modify(previous); state.store(previous);",
                false,
            ),
            (
                "auto previous = other.state.load(); state.store(previous + 1);",
                false,
            ),
            (
                "auto previous = state.load(); auto &alias = previous; alias = 1; state.store(previous);",
                false,
            ),
        ] {
            let files = parser::parse_cpp_files(vec![CppFile {
                path: "state.cpp".into(),
                source: format!(
                    "struct State {{ std::atomic<int> state; int peer; void step(State &other) {{ {body} }} int read() {{ return peer; }} }};"
                ),
            }]);
            let records = layout::collect_cpp_structs(&files, "fixture", 64);
            let facts = evidence::collect_cpp_evidence(&files, &records);
            let accesses = facts[0]
                .items
                .iter()
                .filter(|a| a.access_kind.is_some() && !a.initialization_phase)
                .collect::<Vec<_>>();
            assert_eq!(
                has_recurrent_writer(&accesses),
                expected,
                "{body}: {accesses:?}"
            );
        }
    }

    #[test]
    fn unknown_intervening_size_is_not_positive_layout_evidence() {
        for (members, expected) in [
            (
                "std::atomic<int> writer; Unknown middle; int reader;",
                false,
            ),
            ("Unknown prefix; std::atomic<int> writer; int reader;", true),
            ("std::atomic<int> writer; int reader; Unknown suffix;", true),
            (
                "std::atomic<int> writer; char padding[128]; int reader;",
                false,
            ),
        ] {
            let files = parser::parse_cpp_files(vec![CppFile {
                path: "layout.cpp".into(),
                source: format!(
                    "struct State {{ {members} void update() {{ writer++; }} int observe() {{ return reader; }} }};"
                ),
            }]);
            let records = layout::collect_cpp_structs(&files, "fixture", 64);
            let facts = evidence::collect_cpp_evidence(&files, &records);
            let accesses = facts[0]
                .items
                .iter()
                .filter(|a| a.access_kind.is_some())
                .collect::<Vec<_>>();
            assert_eq!(
                same_object_pair_reason(&records[0], &accesses).is_some(),
                expected,
                "{members}: {:?}; {accesses:?}",
                records[0].fields
            );
        }
    }

    #[test]
    fn repeated_field_names_do_not_reverse_layout_interval() {
        let files = parser::parse_cpp_files(vec![CppFile {
            path: "alternatives.cpp".into(),
            source: "struct State { int reader; Unknown gap; std::atomic<int> writer; void update() { writer++; } int observe() { return reader; } };".into(),
        }]);
        let mut records = layout::collect_cpp_structs(&files, "fixture", 64);
        let facts = evidence::collect_cpp_evidence(&files, &records);
        // Preprocessor alternatives/recovery may retain two declarations with
        // the same spelling. The latter must use its actual position, not the
        // first name match before the writer.
        let repeated = records[0].fields[0].clone();
        records[0].fields.push(repeated);
        let accesses = facts[0]
            .items
            .iter()
            .filter(|a| a.access_kind.is_some())
            .collect::<Vec<_>>();
        let _ = same_object_pair_reason(&records[0], &accesses);
    }

    #[test]
    fn qualified_parameter_binds_its_record_not_a_same_named_owner() {
        for own in ["", "int own;"] {
            let files = parser::parse_cpp_files(vec![CppFile {
                path: "qualified.cpp".into(),
                source: format!(
                    "namespace A {{ struct State {{ std::atomic<int> writer; void *peer; }}; }}\nnamespace B {{ struct State {{ {own} State(A::State& shared) {{ shared.writer.fetch_add(1); }} }}; }}\nvoid unknown(Missing::State& shared) {{ shared.writer.fetch_add(1); }}"
                ),
            }]);
            let records = layout::collect_cpp_structs(&files, "fixture", 64);
            let facts = evidence::collect_cpp_evidence(&files, &records);
            let index = records
                .iter()
                .position(|r| r.qualified_name == "A::State")
                .unwrap();
            let accesses = facts[index]
                .items
                .iter()
                .filter(|a| a.access_kind == Some(CppAccessKind::ReadModifyWrite))
                .collect::<Vec<_>>();
            assert!(!accesses.is_empty(), "{own}");
            assert!(
                accesses
                    .iter()
                    .all(|a| !a.in_record_constructor
                        && a.function_name.as_deref() != Some("unknown"))
            );
            assert!(has_recurrent_writer(&accesses));
        }
    }

    #[test]
    fn constructor_created_callback_is_not_construction_execution() {
        let files = parser::parse_cpp_files(vec![CppFile {
            path: "callback.cpp".into(),
            source: "struct State { std::atomic<int> writer; void *peer; State(State& src) { register_callback([&src] { src.writer.fetch_add(1); }); } };".into(),
        }]);
        let records = layout::collect_cpp_structs(&files, "fixture", 64);
        let facts = evidence::collect_cpp_evidence(&files, &records);
        let accesses = facts[0]
            .items
            .iter()
            .filter(|a| a.access_kind == Some(CppAccessKind::ReadModifyWrite))
            .collect::<Vec<_>>();
        assert!(!accesses.is_empty());
        assert!(accesses.iter().all(|a| !a.in_record_constructor));
        assert!(has_recurrent_writer(&accesses));
    }

    #[test]
    fn field_repetition_uses_expression_scope_not_line_or_callback_creation() {
        let files = parser::parse_cpp_files(vec![CppFile {
            path: "loops.cpp".into(),
            source: "struct State { int before, init, body, callback, nested, after; void work() { before++; for (int i = init++; i < 10; ++i) { body++; defer([this] { callback++; while (ready()) { nested++; } }); } after++; } };".into(),
        }]);
        let records = layout::collect_cpp_structs(&files, "fixture", 64);
        let facts = evidence::collect_cpp_evidence(&files, &records);
        for (field, hot) in [
            ("before", false),
            ("init", false),
            ("body", true),
            ("callback", false),
            ("nested", true),
            ("after", false),
        ] {
            let writes = facts[0]
                .items
                .iter()
                .filter(|a| {
                    a.field_name.as_deref() == Some(field)
                        && a.access_kind == Some(CppAccessKind::ReadModifyWrite)
                })
                .collect::<Vec<_>>();
            assert!(!writes.is_empty(), "{field}");
            assert!(
                writes.iter().all(|a| (a.hotness_score > 1.0) == hot),
                "{field}: {writes:?}"
            );
        }
    }

    #[test]
    fn same_named_constructor_in_another_scope_is_not_this_records_lifecycle() {
        let files = parser::parse_cpp_files(vec![CppFile {
            path: "owners.cpp".into(),
            source: "namespace A { struct State { std::atomic<int> writer; void *peer; }; }\nnamespace B { struct State { State(A::State& shared) { shared.writer.fetch_add(1); } }; }".into(),
        }]);
        let records = layout::collect_cpp_structs(&files, "fixture", 64);
        let facts = evidence::collect_cpp_evidence(&files, &records);
        let index = records
            .iter()
            .position(|r| r.qualified_name == "A::State")
            .unwrap();
        let accesses = facts[index]
            .items
            .iter()
            .filter(|a| a.access_kind == Some(CppAccessKind::ReadModifyWrite))
            .collect::<Vec<_>>();
        assert!(!accesses.is_empty());
        assert!(accesses.iter().all(|a| !a.in_record_constructor));
        assert!(has_recurrent_writer(&accesses));
    }

    #[test]
    fn construction_policy_preserves_concurrency_and_other_record_updates() {
        let files = parser::parse_cpp_files(vec![CppFile {
            path: "lifetime.cpp".into(),
            source: "struct State { std::atomic<int> writer; void *peer; State(State&& src) : writer(src.writer.exchange(0)), peer(nullptr) {} }; struct Token { Token(State& s) { s.writer.fetch_add(1); } };".into(),
        }]);
        let records = layout::collect_cpp_structs(&files, "fixture", 64);
        let facts = evidence::collect_cpp_evidence(&files, &records);
        let index = records.iter().position(|r| r.name == "State").unwrap();
        let source = facts[index]
            .items
            .iter()
            .find(|a| {
                a.function_name.as_deref() == Some("State")
                    && a.access_kind == Some(CppAccessKind::ReadModifyWrite)
                    && !a.initialization_phase
            })
            .unwrap();
        assert!(!has_recurrent_writer(&[source]));
        let mut concurrent = source.clone();
        concurrent.in_concurrent_context = true;
        assert!(has_recurrent_writer(&[&concurrent]));
        let token = facts[index]
            .items
            .iter()
            .find(|a| {
                a.function_name.as_deref() == Some("Token")
                    && a.access_kind == Some(CppAccessKind::ReadModifyWrite)
            })
            .unwrap();
        assert!(has_recurrent_writer(&[token]));
    }

    #[test]
    fn serialized_roles_must_include_the_recurrent_writer() {
        let files = parser::parse_cpp_files(vec![CppFile {
            path: "roles.cpp".into(),
            source: r#"
            struct State { std::atomic<int> writer; int reader; };
            void set_once(State * s) { s->writer = 1; }
            void observe(State * s) { consume(s->reader); }
            void update(State * s) { s->writer.fetch_add(1); }
        "#
            .into(),
        }]);
        let records = layout::collect_cpp_structs(&files, "fixture", 64);
        let facts = evidence::collect_cpp_evidence(&files, &records);
        let accesses = facts[0]
            .items
            .iter()
            .filter(|a| a.access_kind.is_some())
            .collect::<Vec<_>>();
        let witnesses = role_witnesses(&accesses);
        assert!(
            witnesses
                .iter()
                .any(|a| a.function_name.as_deref() == Some("update")),
            "a blind setter must not borrow repetition from an omitted method"
        );
        let without_update = accesses
            .into_iter()
            .filter(|a| a.function_name.as_deref() != Some("update"))
            .collect::<Vec<_>>();
        assert!(role_witnesses(&without_update).is_empty());
    }

    #[test]
    fn pair_guard_exclusion_is_not_diluted_by_an_unrelated_unguarded_field() {
        for (peer_guard, expected) in [("mutex", false), ("other_mutex", true), ("", true)] {
            let files = parser::parse_cpp_files(vec![CppFile { path: "fixture.hpp".into(), source:
                "struct State {\nstd::atomic<size_t> writer;\nuint64_t reader;\nuint64_t unrelated;\n};\nvoid update(State* s) { s->writer.fetch_add(1); }\nvoid read(State* s) { consume(s->reader); }\nvoid other(State* s) { consume(s->unrelated); }\n".into() }]);
            let mut records = layout::collect_cpp_structs(&files, "fixture", 64);
            records[0].cache_line_groups_precise = true;
            records[0].cache_line_groups = vec![
                vec!["writer".into(), "reader".into()],
                vec!["unrelated".into()],
            ];
            let mut facts = evidence::collect_cpp_evidence(&files, &records);
            for item in &mut facts[0].items {
                match item.field_name.as_deref() {
                    Some("writer") => item.guard_ids = vec!["mutex".into()],
                    Some("reader") if !peer_guard.is_empty() => {
                        item.guard_ids = vec![peer_guard.into()]
                    }
                    _ => {}
                }
            }
            let accesses = facts[0]
                .items
                .iter()
                .filter(|a| a.access_kind.is_some())
                .collect::<Vec<_>>();
            let reason = same_object_pair_reason(&records[0], &accesses);
            assert_eq!(reason.is_some(), expected, "{peer_guard}");
            if let Some(reason) = reason {
                assert!(
                    reason
                        .witnesses
                        .iter()
                        .any(|a| a.field_name.as_deref() == Some("writer"))
                );
                assert!(
                    reason
                        .witnesses
                        .iter()
                        .any(|a| a.field_name.as_deref() == Some("reader"))
                );
                assert!(!accesses_share_guard(
                    &reason.witnesses.iter().collect::<Vec<_>>()
                ));
            }
        }
    }

    #[test]
    fn payload_writes_cannot_supply_an_object_header_pair_witness() {
        let files = parser::parse_cpp_files(vec![CppFile { path: "fixture.hpp".into(), source:
            "struct State {\nstd::atomic<size_t> counter;\nuint64_t peer;\n};\nvoid update(State* s) { s->counter.fetch_add(1); }\nvoid read(State* s) { consume(s->peer); }\n".into() }]);
        let records = layout::collect_cpp_structs(&files, "fixture", 64);
        let mut facts = evidence::collect_cpp_evidence(&files, &records);
        assert!(
            same_object_pair_reason(
                &records[0],
                &facts[0]
                    .items
                    .iter()
                    .filter(|a| a.access_kind.is_some())
                    .collect::<Vec<_>>()
            )
            .is_some()
        );
        for item in &mut facts[0].items {
            if item.field_name.as_deref() == Some("counter") {
                item.kind = CppEvidenceKind::ContiguousElementAccess;
            }
        }
        assert!(
            same_object_pair_reason(
                &records[0],
                &facts[0]
                    .items
                    .iter()
                    .filter(|a| a.access_kind.is_some())
                    .collect::<Vec<_>>()
            )
            .is_none()
        );
    }

    #[test]
    fn write_and_colocation_must_belong_to_the_same_pair() {
        for (separate_line, expected) in [(true, false), (false, true)] {
            let source = "struct State {\nstd::atomic<size_t> isolated;\nuint64_t left;\nuint64_t right;\n};\nvoid update(State* s) { s->isolated.fetch_add(1); }\nvoid read_left(State* s) { consume(s->left); }\nvoid read_right(State* s) { consume(s->right); }\n".to_owned();
            let files = parser::parse_cpp_files(vec![CppFile {
                path: "fixture.hpp".into(),
                source,
            }]);
            let mut records = layout::collect_cpp_structs(&files, "fixture", 64);
            // Supply exact layout facts to test the predicate independently
            // of the source frontend's ABI/alignment approximation.
            records[0].cache_line_groups_precise = true;
            records[0].cache_line_groups = if separate_line {
                vec![vec!["isolated".into()], vec!["left".into(), "right".into()]]
            } else {
                vec![vec!["isolated".into(), "left".into(), "right".into()]]
            };
            let facts = evidence::collect_cpp_evidence(&files, &records);
            assert_eq!(records.len(), 1);
            let accesses = facts[0]
                .items
                .iter()
                .filter(|item| item.access_kind.is_some())
                .collect::<Vec<_>>();
            assert_eq!(
                same_object_pair_reason(&records[0], &accesses).is_some(),
                expected,
                "separate_line={separate_line}"
            );
        }
    }
}
