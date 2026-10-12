//! C++ adapter for the language-neutral false-sharing pattern calculus.
//!
//! The adapter turns C++-specific facts (ABI-dependent record layout,
//! contiguous arrays, unrestricted aliasing, shared ownership, OpenMP and
//! thread APIs) into the same predicate used by the Rust frontend.

use std::collections::{HashMap, HashSet};

use crate::pattern_model::{
    StaticPatternInput, core_predicate_holds, default_colocation_pattern, evaluate_static_pattern,
};
use crate::types::{
    AccessPattern, CandidateKind, ColocationEvidence, ColocationPattern, Finding,
    ParallelismEvidence,
};

use super::layout::fields_may_share_cache_line;
use super::types::{
    CppAccessKind, CppEvidenceKind, CppEvidenceSet, CppFieldInfo, CppStructInfo,
    has_contiguous_elements,
};

/// Attach a theory-level witness to every C++ candidate and discard candidates
/// that do not satisfy the shared core predicate.
pub fn retain_theory_candidates(
    findings: &mut Vec<Finding>,
    records: &[CppStructInfo],
    evidence_by_record: &[CppEvidenceSet],
) {
    findings.retain_mut(|finding| {
        let record_index = matching_record_index(finding, records);
        let record = record_index.map(|index| &records[index]);
        let evidence = record_index.and_then(|index| evidence_by_record.get(index));
        let topology = rule_topology(finding.candidate_kind);
        let locations = witness_locations(finding, record, topology);
        let candidate_fields = candidate_field_names(&locations);
        let matching_domain = |field: Option<&str>, heap_element: bool| {
            if heap_element {
                topology == ColocationPattern::ContiguousElements
            } else {
                // A resize/push_back mutates the vector header. It is not a
                // witness for workers accessing distinct payload elements.
                !(topology == ColocationPattern::ContiguousElements
                    && record.is_some_and(|record| {
                        record.fields.iter().any(|candidate| {
                            Some(candidate.name.as_str()) == field
                                && has_contiguous_elements(candidate)
                        })
                    }))
            }
        };
        let matching_items = evidence
            .into_iter()
            .flat_map(|set| &set.items)
            .filter(|item| {
                item.field_name
                    .as_deref()
                    .is_some_and(|field| candidate_fields.contains(field))
                    && !item.through_thread_local
                    && !item.through_nonescaping_local
                    && (!item.initialization_phase
                        || topology != ColocationPattern::SameObjectFields)
                    && matching_domain(
                        item.field_name.as_deref(),
                        item.kind == CppEvidenceKind::ContiguousElementAccess,
                    )
            })
            .collect::<Vec<_>>();

        let reported_items = finding
            .access_evidence
            .iter()
            .filter(|item| {
                item.field_name
                    .as_deref()
                    .is_some_and(|field| candidate_fields.contains(field))
                    && !item.semantic_contexts.iter().any(|context| {
                        matches!(
                            context.as_str(),
                            "cpp_thread_local_receiver" | "cpp_nonescaping_local_receiver"
                        ) || (context == "cpp_initialization_phase"
                            && topology == ColocationPattern::SameObjectFields)
                    })
                    && (matches!(
                        finding.candidate_kind,
                        CandidateKind::StaticData | CandidateKind::IndexedWrites
                    ) || matching_domain(
                        item.field_name.as_deref(),
                        item.evidence_kind == "contiguous_element_access",
                    ))
            })
            .collect::<Vec<_>>();
        let accessed_fields = matching_items
            .iter()
            .filter(|item| item.access_kind.is_some())
            .filter_map(|item| item.field_name.as_deref())
            .collect::<HashSet<_>>();
        let reported_accessed_fields = reported_items
            .iter()
            .filter(|item| item.access_kind.is_some())
            .filter_map(|item| item.field_name.as_deref())
            .collect::<HashSet<_>>();
        let external_field_capabilities = record.is_some_and(|record| {
            record.visibility.is_externally_exposed()
                && candidate_fields.len() >= 2
                && candidate_fields.iter().all(|field| {
                    record.fields.iter().any(|candidate| {
                        candidate.name == *field && candidate.visibility.is_externally_exposed()
                    })
                })
        });
        let written_fields = matching_items
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                )
            })
            .filter_map(|item| item.field_name.as_deref())
            .collect::<HashSet<_>>();
        let reported_written_fields = reported_items
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind.as_deref(),
                    Some("write" | "read_modify_write")
                )
            })
            .filter_map(|item| item.field_name.as_deref())
            .collect::<HashSet<_>>();
        let read_fields = matching_items
            .iter()
            .filter(|item| matches!(item.access_kind, Some(CppAccessKind::Read)))
            .filter_map(|item| item.field_name.as_deref())
            .collect::<HashSet<_>>();
        let reported_read_fields = reported_items
            .iter()
            .filter(|item| item.access_kind.as_deref() == Some("read"))
            .filter_map(|item| item.field_name.as_deref())
            .collect::<HashSet<_>>();
        // One source site may denote two abstract elements when its index is
        // derived from a worker/parallel-loop partition.  The topology alone
        // must not invent the second access: an ordinary field access, enum or
        // singleton is not a pair merely because a rule selected an indexed or
        // allocator topology.
        let partitioned_index_access = reported_items.iter().any(|item| {
            (item.in_concurrent_context
                || item.evidence_kind == "api_index_partition"
                || matches!(
                    item.evidence_kind.as_str(),
                    "static_thread_indexed_write" | "static_thread_indexed_access"
                ))
                && item.access_kind.is_some()
                && matches!(
                    item.evidence_kind.as_str(),
                    "direct_worker_partition"
                        | "api_index_partition"
                        | "parallel_indexed_write"
                        | "pthread_worker_partition"
                        | "static_thread_indexed_write"
                        | "static_thread_indexed_access"
                        | "atomic_alias_partitioned_write"
                )
        });
        let external_stride_capability = finding.candidate_kind == CandidateKind::ObjectInstances
            && record.is_some_and(|record| {
                record.visibility.is_externally_exposed()
                    && !record.public_methods.is_empty()
                    && record
                        .total_estimated_size
                        .is_some_and(|size| size <= record.cache_line_size.saturating_mul(2))
            })
            && matching_items.iter().any(|item| {
                matches!(
                    item.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                )
            });
        let topology_storage_supported = external_stride_capability
            || cpp_topology_storage_supported(
                finding,
                record,
                evidence,
                &candidate_fields,
                topology,
                partitioned_index_access,
            );
        let object_pair_access = topology_storage_supported
            && matches!(
                topology,
                ColocationPattern::AdjacentObjects | ColocationPattern::AllocatorObjects
            )
            && (!accessed_fields.is_empty() || !reported_accessed_fields.is_empty());
        let indexed_element_capability = topology_storage_supported
            && matches!(
                topology,
                ColocationPattern::ContiguousElements | ColocationPattern::StaticStorage
            )
            && (!accessed_fields.is_empty() || !reported_accessed_fields.is_empty());
        let topology_pair_access =
            partitioned_index_access || object_pair_access || indexed_element_capability;
        let independently_accessible = topology_pair_access
            || external_field_capabilities
            || has_separable_cpp_accesses(&matching_items)
            // Serialized source accesses are a bounded copy of matching_items,
            // not an independent proof of separate private-state paths.
            || (reported_accessed_fields.len() >= 2
                && (matching_items.is_empty()
                    || !record.is_some_and(|record| {
                        candidate_fields.iter().all(|field| {
                            record.fields.iter().any(|candidate| {
                                candidate.name == *field && !candidate.visibility.is_exposed()
                            })
                        })
                    })))
            || matching_items
                .iter()
                .filter(|item| {
                    item.in_concurrent_context
                        && matches!(
                            item.access_kind,
                            Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                        )
                })
                .filter_map(|item| item.field_name.as_deref())
                .collect::<HashSet<_>>()
                .len()
                >= 2;
        let parallelism = cpp_parallelism(
            finding.candidate_kind,
            topology,
            evidence,
            &matching_items,
            &reported_items,
            independently_accessible,
            external_field_capabilities,
        );
        let has_write = !written_fields.is_empty() || !reported_written_fields.is_empty();
        let write_write = written_fields.len() >= 2
            || reported_written_fields.len() >= 2
            || (partitioned_index_access && !reported_written_fields.is_empty());
        let write_read = written_fields
            .iter()
            .any(|writer| read_fields.iter().any(|reader| reader != writer))
            || reported_written_fields
                .iter()
                .any(|writer| reported_read_fields.iter().any(|reader| reader != writer));
        let access_pattern = if write_write {
            AccessPattern::WriteWrite
        } else if write_read {
            AccessPattern::WriteRead
        } else {
            AccessPattern::WriteUnknownPeer
        };
        let mut pattern = evaluate_static_pattern(StaticPatternInput {
            candidate_kind: finding.candidate_kind,
            frontend: "cpp",
            language_specific_assumptions: cpp_assumptions(
                topology,
                record,
                evidence,
                finding.candidate_kind,
            ),
            access_pattern,
            colocation_pattern: topology,
            parallelism_evidence: parallelism,
            colocation_evidence: record.map_or(ColocationEvidence::Symbolic, |record| {
                if record.compiler_layout_exact {
                    ColocationEvidence::CompilerExact
                } else if record.cache_line_groups_precise {
                    ColocationEvidence::SourceEstimated
                } else {
                    ColocationEvidence::Symbolic
                }
            }),
            distinct_locations: locations.len() >= 2
                && topology_storage_supported
                && !same_bitfield_location(record, &candidate_fields, topology),
            distinct_accesses: topology_pair_access
                || external_field_capabilities
                || accessed_fields.len() >= 2
                || reported_accessed_fields.len() >= 2,
            independently_accessible,
            may_share_cache_line: topology_storage_supported
                && cpp_may_share_cache_line(record, &locations, topology),
            has_write,
            repetition_evidence: evidence.is_some_and(|set| set.max_hotness() > 1.0)
                || matches!(
                    finding.candidate_kind,
                    CandidateKind::StaticData
                        | CandidateKind::IndexedWrites
                        | CandidateKind::SiblingArrays
                ),
            protection_excluded: cpp_protection_excluded(
                record,
                evidence,
                &candidate_fields,
                topology,
                &reported_items,
            ),
            witness_locations: locations,
        });
        // Preserve the discovery-specific evidence checks above, then classify
        // the recovered storage pair. Static placement is orthogonal to arrays.
        if finding.candidate_kind == CandidateKind::StaticData
            && finding.field_list.len() == 1
            && finding.access_evidence.iter().any(|access| {
                matches!(
                    access.evidence_kind.as_str(),
                    "static_array_write" | "static_thread_indexed_write"
                )
            })
        {
            pattern.colocation_pattern = ColocationPattern::ContiguousElements;
        }
        if finding.candidate_kind == CandidateKind::ObjectInstances
            && evidence.is_some_and(|facts| {
                facts.has_allocator_object_storage() && !facts.has_contiguous_object_storage()
            })
        {
            pattern.colocation_pattern = ColocationPattern::AllocatorObjects;
        }
        if pattern.colocation_pattern != topology {
            // Placement assumptions must describe the recovered relation too;
            // allocator-only objects cannot retain an array-contiguity claim.
            pattern.language_specific_assumptions = cpp_assumptions(
                pattern.colocation_pattern,
                record,
                evidence,
                finding.candidate_kind,
            );
        }
        pattern.rule_id = pattern.colocation_pattern.rule_id();
        let keep = core_predicate_holds(&pattern);
        finding.rule_id = pattern.rule_id;
        finding.static_pattern = Some(pattern);
        keep
    });
}

fn same_bitfield_location(
    record: Option<&CppStructInfo>,
    fields: &HashSet<&str>,
    topology: ColocationPattern,
) -> bool {
    if topology != ColocationPattern::SameObjectFields || fields.len() < 2 {
        return false;
    }
    let Some(record) = record else {
        return false;
    };
    let mut group = None;
    for name in fields {
        let Some(field_group) = record
            .fields
            .iter()
            .find(|field| field.name == *name)
            .and_then(|field| field.bitfield_group)
        else {
            return false;
        };
        if group.is_some_and(|group| group != field_group) {
            return false;
        }
        group = Some(field_group);
    }
    true
}

pub(super) fn matching_record_index(finding: &Finding, records: &[CppStructInfo]) -> Option<usize> {
    let name = finding.struct_name.as_deref()?;
    let declaration_line = finding
        .layout_context
        .as_ref()
        .map(|layout| layout.declaration_line);
    if let Some(index) = records.iter().position(|record| {
        record.file == finding.file
            && (record.name == name || record.qualified_name == name)
            && declaration_line.is_none_or(|line| line == record.line)
    }) {
        return Some(index);
    }
    // Some topology findings are intentionally anchored at the allocation or
    // mutation site rather than the type declaration.  The attached layout
    // identity still binds the record when name + declaration line is unique.
    let candidates = records
        .iter()
        .enumerate()
        .filter(|(_, record)| {
            (record.name == name || record.qualified_name == name)
                && declaration_line.is_some_and(|line| line == record.line)
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    (candidates.len() == 1).then(|| candidates[0])
}

fn rule_topology(rule: CandidateKind) -> ColocationPattern {
    default_colocation_pattern(rule)
}

fn witness_locations(
    finding: &Finding,
    record: Option<&CppStructInfo>,
    topology: ColocationPattern,
) -> Vec<String> {
    let owner = finding
        .struct_name
        .as_deref()
        .or(finding.symbol.as_deref())
        .unwrap_or("candidate");
    if topology == ColocationPattern::AdjacentObjects {
        for access in &finding.access_evidence {
            if let (Some(field), Some(peer)) = (
                access.field_name.as_ref(),
                access
                    .semantic_contexts
                    .iter()
                    .find_map(|c| c.strip_prefix("cpp_worker_record_peer:")),
            ) {
                return vec![format!("{owner}[0].{field}"), format!("{owner}[1].{peer}")];
            }
        }
    }
    if finding.candidate_kind == CandidateKind::StaticData
        && topology == ColocationPattern::StaticStorage
        && finding.field_list.len() >= 2
    {
        return finding
            .field_list
            .iter()
            .map(|field| format!("{owner}.{field}[0]"))
            .collect();
    }
    if topology != ColocationPattern::SameObjectFields {
        let payload = finding
            .access_evidence
            .iter()
            .filter(|access| {
                matches!(
                    access.access_kind.as_deref(),
                    Some("write" | "read_modify_write")
                )
            })
            .filter_map(|access| access.field_name.as_ref())
            .find(|field| finding.field_list.contains(field))
            .or_else(|| {
                finding
                    .access_evidence
                    .iter()
                    .filter_map(|access| access.field_name.as_ref())
                    .find(|field| finding.field_list.contains(field))
            })
            .or_else(|| finding.field_list.first())
            .map(|field| format!("{owner}.{field}"))
            .unwrap_or_else(|| owner.to_string());
        return vec![format!("{payload}[0]"), format!("{payload}[1]")];
    }

    let mut fields = finding.field_list.clone();
    if fields.len() < 2
        && let (Some(record), Some(field)) = (record, fields.first())
        && let Some(neighbor) = neighboring_payload(record, field)
    {
        fields.push(neighbor.name.clone());
    }
    fields.sort();
    fields.dedup();
    fields
        .into_iter()
        .map(|field| format!("{owner}.{field}"))
        .collect()
}

fn neighboring_payload<'a>(record: &'a CppStructInfo, field: &str) -> Option<&'a CppFieldInfo> {
    let index = record
        .fields
        .iter()
        .position(|candidate| candidate.name == field)?;
    index
        .checked_sub(1)
        .and_then(|neighbor| record.fields.get(neighbor))
        .filter(|neighbor| !neighbor.is_cache_padded && !neighbor.is_manual_padding)
        .or_else(|| {
            record
                .fields
                .get(index + 1)
                .filter(|neighbor| !neighbor.is_cache_padded && !neighbor.is_manual_padding)
        })
}

fn cpp_topology_storage_supported(
    finding: &Finding,
    record: Option<&CppStructInfo>,
    evidence: Option<&CppEvidenceSet>,
    candidate_fields: &HashSet<&str>,
    topology: ColocationPattern,
    partitioned_index_access: bool,
) -> bool {
    match topology {
        ColocationPattern::SameObjectFields => true,
        ColocationPattern::ContiguousElements => {
            partitioned_index_access
                || finding.access_evidence.iter().any(|item| {
                    matches!(
                        item.evidence_kind.as_str(),
                        "atomic_alias_partitioned_write" | "atomic_alias_mutable_index_api"
                    )
                })
                || record.is_some_and(|record| {
                    record.fields.iter().any(|field| {
                        candidate_fields.contains(field.name.as_str())
                            && (field.is_array
                                || field.ty_str.contains("std::array")
                                || field.ty_str.contains("std::vector")
                                || field.ty_str.contains("vector<")
                                || field.ty_str.contains("absl::FixedArray")
                                || field.ty_str.contains("folly::small_vector"))
                    })
                })
        }
        ColocationPattern::AdjacentObjects => {
            evidence.is_some_and(CppEvidenceSet::has_contiguous_object_storage)
                || finding.access_evidence.iter().any(|a| {
                    a.in_concurrent_context
                        && a.evidence_kind == "direct_worker_partition"
                        && a.semantic_contexts
                            .iter()
                            .any(|c| c.starts_with("cpp_worker_record_peer:"))
                })
        }
        ColocationPattern::AllocatorObjects => evidence.is_some_and(|evidence| {
            evidence.has_allocator_object_storage() || evidence.has_contiguous_object_storage()
        }),
        ColocationPattern::StaticStorage => {
            finding.snippet.contains('[')
                || finding
                    .access_evidence
                    .iter()
                    .any(|item| item.evidence_kind == "static_array_storage")
        }
    }
}

fn candidate_field_names(locations: &[String]) -> HashSet<&str> {
    locations
        .iter()
        .filter_map(|location| {
            location
                .rsplit('.')
                .next()
                .map(|field| field.split('[').next().unwrap_or(field))
        })
        .collect()
}

fn has_separable_cpp_accesses(items: &[&super::types::CppEvidenceItem]) -> bool {
    cpp_access_roles_separable(items, false, &[])
}

pub(super) fn has_distinct_cpp_access_roles(items: &[&super::types::CppEvidenceItem]) -> bool {
    cpp_access_roles_separable(items, true, &[])
}

pub(super) fn has_distinct_cpp_access_roles_with_omissions(
    items: &[&super::types::CppEvidenceItem],
    omitted: &[super::types::CppOmittedAccessRole],
) -> bool {
    cpp_access_roles_separable(items, true, omitted)
}

fn cpp_access_roles_separable(
    items: &[&super::types::CppEvidenceItem],
    allow_overlap: bool,
    omitted: &[super::types::CppOmittedAccessRole],
) -> bool {
    // File is part of callable identity: unrelated same-spelled functions in
    // separate translation units must not be merged into one access role.
    let mut by_function: HashMap<(&str, &str), HashMap<&str, bool>> = HashMap::new();
    for item in items {
        let (Some(function), Some(field), Some(kind)) = (
            item.function_name.as_deref(),
            item.field_name.as_deref(),
            item.access_kind.as_ref(),
        ) else {
            continue;
        };
        let written = matches!(kind, CppAccessKind::Write | CppAccessKind::ReadModifyWrite);
        *by_function
            .entry((&item.file, function))
            .or_default()
            .entry(field)
            .or_default() |= written;
    }
    // Only complete the membership of roles already witnessed by real retained
    // accesses. An omitted function cannot create a new independent role.
    for role in omitted {
        if let Some(fields) = by_function.get_mut(&(role.file.as_str(), role.function.as_str())) {
            *fields.entry(&role.field).or_default() |= role.written;
        }
    }
    let partitions = by_function.values().collect::<Vec<_>>();
    partitions.iter().enumerate().any(|(left_index, left)| {
        partitions.iter().skip(left_index + 1).any(|right| {
            let separate_field_sets = left.keys().any(|field| !right.contains_key(field))
                && right.keys().any(|field| !left.contains_key(field));
            // Reading the same immutable handle does not couple a reader of
            // that handle to a writer of a neighboring field. Require an
            // actual write/read pair and no shared writable field before
            // accepting these otherwise nested access sets.
            let shared_fields_only_read = left.iter().all(|(field, left_write)| {
                right
                    .get(field)
                    .is_none_or(|right_write| !left_write && !right_write)
            });
            let distinct_write_read = left
                .iter()
                .any(|(field, written)| *written && right.keys().any(|peer| peer != field))
                || right
                    .iter()
                    .any(|(field, written)| *written && left.keys().any(|peer| peer != field));
            // False sharing can coexist with true sharing: a consumer may
            // touch both queue fields while a producer only touches one.
            // Do not reject that asymmetric role merely for an overlapping
            // writable field. Identical coupled access sets remain unresolved.
            let asymmetric_roles = allow_overlap
                && (left.keys().any(|field| !right.contains_key(field))
                    || right.keys().any(|field| !left.contains_key(field)));
            let complementary_writers = allow_overlap
                && left
                    .iter()
                    .any(|(field, write)| *write && right.get(field) == Some(&false))
                && right
                    .iter()
                    .any(|(field, write)| *write && left.get(field) == Some(&false));
            (separate_field_sets
                || shared_fields_only_read
                || asymmetric_roles
                || complementary_writers)
                && distinct_write_read
        })
    })
}

fn cpp_parallelism(
    rule: CandidateKind,
    _topology: ColocationPattern,
    evidence: Option<&CppEvidenceSet>,
    matching_items: &[&super::types::CppEvidenceItem],
    reported_items: &[&crate::types::AccessEvidenceContext],
    independently_accessible: bool,
    external_field_capabilities: bool,
) -> ParallelismEvidence {
    let concurrent_matching_access = matching_items.iter().any(|item| {
        item.in_concurrent_context && item.access_kind.is_some() && !item.through_thread_local
    });
    let concurrent_reported_access = reported_items.iter().any(|item| {
        item.in_concurrent_context
            && item.access_kind.is_some()
            && !item
                .semantic_contexts
                .iter()
                .any(|context| context == "cpp_thread_local_receiver")
    });
    if concurrent_matching_access || concurrent_reported_access {
        return ParallelismEvidence::ConcurrentContext;
    }
    if independently_accessible
        && reported_items
            .iter()
            .any(|item| item.evidence_kind == "api_index_partition")
    {
        return ParallelismEvidence::ExternalApiPotential;
    }

    // A type-level shared_ptr fact applies to the record, but ordinary raw
    // pointer/reference facts must be linked to the candidate fields.  The old
    // record-wide raw-pointer scan allowed an unrelated field to establish MHP.
    let shared_record = evidence.is_some_and(|set| {
        set.items
            .iter()
            .any(|item| item.kind == CppEvidenceKind::SharedOwnership)
    });
    let candidate_indirection = matching_items
        .iter()
        .any(|item| item.through_shared_indirection)
        || reported_items
            .iter()
            .any(|item| item.through_shared_indirection);
    if (shared_record || candidate_indirection) && independently_accessible {
        return ParallelismEvidence::SharedReachability;
    }

    let api_signal = evidence.is_some_and(CppEvidenceSet::has_api_signal);
    if independently_accessible && (api_signal || external_field_capabilities) {
        ParallelismEvidence::ExternalApiPotential
    } else if independently_accessible
        && matches!(
            rule,
            CandidateKind::ObjectInstances
                | CandidateKind::StaticData
                | CandidateKind::AtomicArray
                | CandidateKind::SiblingArrays
        )
        && reported_items.iter().any(|item| {
            matches!(
                item.access_kind.as_deref(),
                Some("write" | "read_modify_write")
            )
        })
    {
        // A mutable global/static array, externally usable object-stride type,
        // or concrete indexed storage write provides a candidate-linked MHP
        // capability even when thread creation happens in an external caller.
        ParallelismEvidence::ExternalApiPotential
    } else {
        ParallelismEvidence::Unresolved
    }
}

fn cpp_may_share_cache_line(
    record: Option<&CppStructInfo>,
    locations: &[String],
    topology: ColocationPattern,
) -> bool {
    if topology != ColocationPattern::SameObjectFields {
        return true;
    }
    let Some(record) = record else {
        return false;
    };
    let fields = candidate_field_names(locations);
    let field_names = fields
        .into_iter()
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    fields_may_share_cache_line(record, &field_names)
}

fn cpp_protection_excluded(
    record: Option<&CppStructInfo>,
    evidence: Option<&CppEvidenceSet>,
    fields: &HashSet<&str>,
    topology: ColocationPattern,
    reported_items: &[&crate::types::AccessEvidenceContext],
) -> bool {
    if record.is_some_and(|record| {
        (record.is_cache_aligned
            && topology != ColocationPattern::SameObjectFields
            && topology != ColocationPattern::ContiguousElements
            && !record.fields.iter().any(|field| {
                fields.contains(field.name.as_str())
                    && (has_contiguous_elements(field) || field.is_indirect)
            }))
            || record.fields.iter().any(|field| {
                fields.contains(field.name.as_str())
                    && (field.is_cache_padded || field.is_manual_padding)
                    && (topology == ColocationPattern::SameObjectFields
                        || !has_contiguous_elements(field))
            })
    }) {
        return false;
    }
    if topology == ColocationPattern::SameObjectFields
        && let Some(record) = record
        && fields.len() >= 2
    {
        let guards = fields
            .iter()
            .filter_map(|name| {
                record
                    .fields
                    .iter()
                    .find(|field| field.name == **name)
                    .and_then(|field| field.guarded_by.as_deref())
            })
            .collect::<Vec<_>>();
        if guards.len() == fields.len()
            && guards
                .first()
                .is_some_and(|first| guards.iter().all(|guard| guard == first))
        {
            return false;
        }
        if evidence.is_some_and(|evidence| pair_accesses_share_common_guard(evidence, fields)) {
            return false;
        }
    }
    if topology != ColocationPattern::SameObjectFields {
        // A rendered prefix may contain only locked accesses while later
        // source accesses remain unprotected. Record-backed candidates must
        // use the whole selected-field evidence, not the display budget.
        let bound_worker_pair = reported_items.iter().any(|item| {
            item.evidence_kind == "direct_worker_partition"
                && item
                    .semantic_contexts
                    .iter()
                    .any(|context| context.starts_with("cpp_worker_record_peer:"))
        });
        let protected = if record.is_some() && !bound_worker_pair {
            evidence.is_some_and(|facts| pair_accesses_share_common_guard(facts, fields))
        } else {
            // Explicit worker-boundary candidates carry their own complete
            // access pair; they are not the record renderer's prefix.
            reported_accesses_share_common_guard(reported_items)
        };
        if protected {
            return false;
        }
    }
    true
}

fn reported_accesses_share_common_guard(accesses: &[&crate::types::AccessEvidenceContext]) -> bool {
    let accesses = accesses
        .iter()
        .filter(|item| item.access_kind.is_some())
        .collect::<Vec<_>>();
    let Some(first) = accesses.first() else {
        return false;
    };
    let mut common = reported_guard_ids(first).collect::<HashSet<_>>();
    for access in accesses.iter().skip(1) {
        let held = reported_guard_ids(access).collect::<HashSet<_>>();
        common.retain(|guard| held.contains(guard));
        if common.is_empty() {
            return false;
        }
    }
    !common.is_empty()
}

fn reported_guard_ids(access: &crate::types::AccessEvidenceContext) -> impl Iterator<Item = &str> {
    access
        .semantic_contexts
        .iter()
        .filter_map(|context| context.strip_prefix("cpp_guarded_by:"))
}

fn pair_accesses_share_common_guard(evidence: &CppEvidenceSet, fields: &HashSet<&str>) -> bool {
    // Omitted membership records do not retain a must-held lockset. They
    // cannot complete an all-accesses protection proof for these fields.
    if evidence.omitted_access_roles_overflow
        || evidence
            .omitted_access_roles
            .iter()
            .any(|role| fields.contains(role.field.as_str()))
    {
        return false;
    }
    let accesses = evidence
        .items
        .iter()
        .filter(|item| {
            item.access_kind.is_some()
                && !item.initialization_phase
                && !item.through_thread_local
                && !item.through_nonescaping_local
                && item
                    .field_name
                    .as_deref()
                    .is_some_and(|field| fields.contains(field))
        })
        .collect::<Vec<_>>();
    let covered_fields = accesses
        .iter()
        .filter_map(|item| item.field_name.as_deref())
        .collect::<HashSet<_>>();
    if covered_fields.len() != fields.len() || accesses.is_empty() {
        return false;
    }

    let mut common = accesses[0].guard_ids.iter().collect::<HashSet<_>>();
    for access in accesses.iter().skip(1) {
        common.retain(|guard| access.guard_ids.contains(guard));
        if common.is_empty() {
            return false;
        }
    }
    !common.is_empty()
}

fn cpp_assumptions(
    topology: ColocationPattern,
    record: Option<&CppStructInfo>,
    evidence: Option<&CppEvidenceSet>,
    rule: CandidateKind,
) -> Vec<&'static str> {
    let mut assumptions = Vec::new();
    if record.is_some_and(|record| !record.compiler_layout_exact) {
        assumptions.push("cpp_record_layout_follows_target_abi_estimate");
    }
    if record.is_some_and(|record| {
        record.visibility.is_externally_exposed() && record.public_methods.len() >= 2
    }) {
        assumptions.push("cpp_public_methods_may_independently_access_private_state");
    }
    if matches!(
        topology,
        ColocationPattern::ContiguousElements | ColocationPattern::AdjacentObjects
    ) {
        assumptions.push("cpp_array_or_container_elements_are_contiguous");
    }
    if topology == ColocationPattern::AllocatorObjects {
        assumptions.push("allocator_may_place_independent_objects_in_adjacent_slots");
    }
    if topology == ColocationPattern::StaticStorage {
        assumptions.push("linker_may_place_independent_statics_in_one_block");
    }
    if evidence.is_some_and(|set| {
        set.has_shared_ownership_signal()
            || set.items.iter().any(|item| item.through_shared_indirection)
    }) {
        assumptions.push("cpp_aliasing_or_shared_ownership_may_cross_threads");
    }
    if matches!(
        rule,
        CandidateKind::IndexedWrites | CandidateKind::SiblingArrays
    ) {
        assumptions.push("parallel_index_partitions_may_select_adjacent_elements");
    }
    assumptions
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitfield_names_are_not_distinct_locations_but_separate_objects_are() {
        use crate::cpp_detection::{layout, parser, types::CppFile};
        let files = parser::parse_cpp_files(vec![CppFile {
            path: "bits.hpp".into(),
            source:
                "struct Bits { unsigned a:1; unsigned b:2; unsigned :0; unsigned c:1; int value; };"
                    .into(),
        }]);
        let records = layout::collect_cpp_structs(&files, "fixture", 64);
        let record = Some(&records[0]);
        assert!(same_bitfield_location(
            record,
            &HashSet::from(["a", "b"]),
            ColocationPattern::SameObjectFields
        ));
        for pair in [["a", "c"], ["a", "value"], ["a", "missing"]] {
            assert!(!same_bitfield_location(
                record,
                &HashSet::from(pair),
                ColocationPattern::SameObjectFields
            ));
        }
        for topology in [
            ColocationPattern::AdjacentObjects,
            ColocationPattern::AllocatorObjects,
            ColocationPattern::ContiguousElements,
        ] {
            assert!(!same_bitfield_location(
                record,
                &HashSet::from(["a", "b"]),
                topology
            ));
        }
    }

    #[test]
    fn rule_topologies_cover_cpp_rule_families() {
        assert_eq!(
            rule_topology(CandidateKind::FieldGroup),
            ColocationPattern::SameObjectFields
        );
        assert_eq!(
            rule_topology(CandidateKind::IndexedWrites),
            ColocationPattern::ContiguousElements
        );
        assert_eq!(
            rule_topology(CandidateKind::SeparateAllocations),
            ColocationPattern::AllocatorObjects
        );
    }
}
