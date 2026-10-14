//! Language-neutral false-sharing pattern calculus and Rust adapter.
//!
//! Rules are report families.  This module defines the orthogonal semantic
//! dimensions that make a source location a false-sharing may-risk:
//! interference, cache-line co-location, may-parallel reachability, and the
//! absence of recognized isolation.  Keeping this predicate independent of
//! repository, type, and field names makes its coverage auditable.

use std::collections::{HashMap, HashSet};

use crate::types::{
    AccessPattern, ApiUsageEvidenceSet, AtomicAccessKind, CandidateKind, ColocationEvidence,
    ColocationPattern, ConcurrencyEvidenceSet, EvidenceKind, LayoutSource, ParallelismEvidence,
    StaticPatternContext, StructInfo,
};

pub const STATIC_PATTERN_MODEL_VERSION: &str = "false-sharing-patterns/v4";

/// Language-neutral facts consumed by the false-sharing predicate.
///
/// Frontends are responsible for translating language constructs into these
/// facts. The core deliberately knows nothing about Rust ownership, C++ ABI
/// rules, tree-sitter, or source-code naming conventions.
pub struct StaticPatternInput {
    pub candidate_kind: CandidateKind,
    pub frontend: &'static str,
    pub language_specific_assumptions: Vec<&'static str>,
    pub access_pattern: AccessPattern,
    pub colocation_pattern: ColocationPattern,
    pub parallelism_evidence: ParallelismEvidence,
    pub colocation_evidence: ColocationEvidence,
    pub distinct_locations: bool,
    pub distinct_accesses: bool,
    pub independently_accessible: bool,
    pub may_share_cache_line: bool,
    pub has_write: bool,
    pub repetition_evidence: bool,
    pub protection_excluded: bool,
    pub witness_locations: Vec<String>,
}

/// Materialize the canonical witness shared by every language frontend.
pub fn evaluate_static_pattern(input: StaticPatternInput) -> StaticPatternContext {
    StaticPatternContext {
        model_version: STATIC_PATTERN_MODEL_VERSION,
        rule_id: input.colocation_pattern.rule_id(),
        candidate_kind: input.candidate_kind,
        frontend: input.frontend,
        language_specific_assumptions: input.language_specific_assumptions,
        access_pattern: input.access_pattern,
        colocation_pattern: input.colocation_pattern,
        parallelism_evidence: input.parallelism_evidence,
        colocation_evidence: input.colocation_evidence,
        distinct_locations: input.distinct_locations,
        distinct_accesses: input.distinct_accesses,
        independently_accessible: input.independently_accessible,
        may_share_cache_line: input.may_share_cache_line,
        may_happen_in_parallel: input.parallelism_evidence != ParallelismEvidence::Unresolved,
        has_write: input.has_write,
        repetition_evidence: input.repetition_evidence,
        protection_excluded: input.protection_excluded,
        witness_locations: input.witness_locations,
    }
}

/// Construct a witness for a pair of distinct abstract locations.
///
/// `locations` may denote fields, representative container elements, adjacent
/// object instances, or static items.  Callers must establish the topology-
/// specific `may_share_cache_line` fact before invoking this function.
#[allow(clippy::too_many_arguments)]
pub fn build_pattern_context(
    si: Option<&StructInfo>,
    candidate_kind: CandidateKind,
    locations: Vec<String>,
    colocation_pattern: ColocationPattern,
    may_share_cache_line: bool,
    evidence: Option<&ConcurrencyEvidenceSet>,
    api_usage: Option<&ApiUsageEvidenceSet>,
    implicit_write: bool,
    implicit_parallelism: Option<ParallelismEvidence>,
    repetition_evidence: bool,
    protection_excluded: bool,
) -> StaticPatternContext {
    let effective = evidence.map(effective_access_evidence);
    let evidence = effective.as_ref();
    let access_pattern = classify_access_pattern(evidence, &locations, implicit_write);
    let independently_accessible = colocation_pattern != ColocationPattern::SameObjectFields
        || ((has_separable_access_partitions(evidence, &locations)
            || has_distinct_access_roles(evidence, &locations))
            && rust_same_object_pair_possible(evidence, &locations));
    let blocked_shared_api = matches!(colocation_pattern,
        ColocationPattern::SameObjectFields | ColocationPattern::ContiguousElements)
        && si.is_some_and(|record| record.known_not_sync)
        // A public field can be projected into its own shared reference even
        // when the enclosing object is not Sync.
        && !si.is_some_and(|record| record.fields.iter().any(|field| field.visibility.is_exposed() && normalized_location_set(&locations).contains(field.name.as_str())))
        && !si.is_some_and(|record| record.shared_field_projections.iter().any(|field| normalized_location_set(&locations).contains(field.as_str())))
        && !evidence.into_iter().flat_map(|set| &set.evidence).any(|item| {
            item.field_name.as_ref().is_some_and(|field| normalized_location_set(&locations).contains(field.as_str()))
                && (item.in_concurrent_context || item.through_raw_pointer)
        });
    let parallelism_evidence = if blocked_shared_api {
        ParallelismEvidence::Unresolved
    } else {
        implicit_parallelism.unwrap_or_else(|| {
            classify_parallelism(
                si.is_some_and(|record| record.visibility.is_exposed()),
                evidence,
                api_usage,
                &locations,
                colocation_pattern,
                independently_accessible,
            )
        })
    };
    let has_write = implicit_write || has_matching_write(evidence, &locations);
    let distinct_accesses = matching_accessed_locations(evidence, &locations) >= 2
        || (implicit_write && colocation_pattern != ColocationPattern::SameObjectFields);

    evaluate_static_pattern(StaticPatternInput {
        candidate_kind,
        frontend: "rust",
        language_specific_assumptions: rust_assumptions(si, colocation_pattern, evidence),
        access_pattern,
        colocation_pattern,
        parallelism_evidence,
        colocation_evidence: si.map_or(ColocationEvidence::Symbolic, layout_evidence),
        distinct_locations: locations.len() >= 2,
        distinct_accesses,
        independently_accessible,
        may_share_cache_line,
        has_write,
        repetition_evidence: repetition_evidence || has_repetition_evidence(evidence, &locations),
        protection_excluded: protection_excluded
            && !rust_common_guard(evidence, &locations, colocation_pattern, si),
        witness_locations: locations,
    })
}

fn rust_assumptions(
    si: Option<&StructInfo>,
    colocation_pattern: ColocationPattern,
    evidence: Option<&ConcurrencyEvidenceSet>,
) -> Vec<&'static str> {
    let mut assumptions = Vec::new();
    if si.is_some_and(|record| record.layout_source != LayoutSource::RustcExact) {
        assumptions.push("rust_source_layout_is_not_an_abi_guarantee");
    } else if si.is_some() {
        assumptions.push("rust_compiler_layout_does_not_determine_object_address");
    }
    if matches!(
        colocation_pattern,
        ColocationPattern::ContiguousElements
            | ColocationPattern::AdjacentObjects
            | ColocationPattern::AllocatorObjects
    ) {
        assumptions.push("container_or_allocator_preserves_candidate_adjacency");
    }
    if evidence.is_some_and(|set| set.has_kind(EvidenceKind::ArcWrapped)) {
        assumptions.push("shared_ownership_may_reach_multiple_threads");
    }
    if colocation_pattern == ColocationPattern::StaticStorage {
        assumptions.push("linker_may_place_independent_statics_in_one_block");
        assumptions.push("global_storage_may_be_accessed_by_independent_callers");
    }
    assumptions
}

pub fn core_predicate_holds(pattern: &StaticPatternContext) -> bool {
    pattern.rule_id == pattern.colocation_pattern.rule_id()
        && rule_supports_topology(pattern.candidate_kind, pattern.colocation_pattern)
        && pattern.distinct_locations
        && pattern.distinct_accesses
        && pattern.independently_accessible
        && pattern.may_share_cache_line
        && pattern.may_happen_in_parallel
        && pattern.has_write
        && pattern.protection_excluded
}

fn effective_access_evidence(evidence: &ConcurrencyEvidenceSet) -> ConcurrencyEvidenceSet {
    if evidence.evidence.iter().any(|item| {
        item.semantic_contexts
            .iter()
            .any(|context| context == "rust_object_evidence_incomplete")
    }) {
        return evidence.clone();
    }
    fn source_key(
        item: &crate::types::EvidenceItem,
    ) -> (
        &str,
        usize,
        Option<&str>,
        &EvidenceKind,
        Option<&AtomicAccessKind>,
    ) {
        (
            item.file.as_str(),
            item.line,
            item.field_name.as_deref(),
            &item.kind,
            item.access_kind.as_ref(),
        )
    }
    // Index the bounded caller-path suffixes once. A pair check must not scan
    // every propagated access for every source summary in a large record.
    let mut instantiated = HashMap::new();
    for instance in &evidence.evidence {
        for start in 1..instance.call_path.len() {
            instantiated
                .entry((source_key(instance), &instance.call_path[start..]))
                .and_modify(|depth: &mut usize| *depth = (*depth).max(instance.propagation_depth))
                .or_insert(instance.propagation_depth);
        }
    }
    let mut effective = evidence.clone();
    effective.evidence.retain(|item| {
        item.access_kind.is_none()
            || item.call_path.is_empty()
            || item
                .semantic_contexts
                .iter()
                .any(|context| context == "rust_callable_exposed")
            || instantiated
                .get(&(source_key(item), item.call_path.as_slice()))
                .is_none_or(|depth| *depth <= item.propagation_depth)
    });
    effective
}

fn rust_same_object_pair_possible(
    evidence: Option<&ConcurrencyEvidenceSet>,
    locations: &[String],
) -> bool {
    if evidence.is_some_and(|set| {
        set.evidence.iter().any(|item| {
            item.semantic_contexts
                .iter()
                .any(|context| context == "rust_object_evidence_incomplete")
        })
    }) {
        return true;
    }
    let fields = normalized_location_set(locations)
        .into_iter()
        .collect::<Vec<_>>();
    let items = evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .filter(|item| item.access_kind.is_some())
        .collect::<Vec<_>>();
    let identity = |item: &crate::types::EvidenceItem| {
        item.semantic_contexts.iter().find_map(|context| {
            context
                .strip_prefix("rust_object_identity:")
                .map(str::to_owned)
        })
    };
    let role = |item: &crate::types::EvidenceItem| {
        item.function_name.as_deref().map(|function| {
            let partitions = item
                .semantic_contexts
                .iter()
                .filter(|context| {
                    context.starts_with("rust_execution_domain:")
                        || context.starts_with("control_partition:")
                })
                .cloned()
                .collect::<Vec<_>>();
            (item.file.clone(), function.to_owned(), partitions)
        })
    };
    fields.iter().enumerate().any(|(index, left)| {
        fields.iter().skip(index + 1).any(|right| {
            let left = items
                .iter()
                .filter(|item| item.field_name.as_deref() == Some(*left))
                .collect::<Vec<_>>();
            let right = items
                .iter()
                .filter(|item| item.field_name.as_deref() == Some(*right))
                .collect::<Vec<_>>();
            !left.is_empty()
                && !right.is_empty()
                && left.iter().any(|a| {
                    right.iter().any(|b| {
                        identity(a).is_none()
                            || identity(b).is_none()
                            || (identity(a) == identity(b)
                                && (role(a).is_none() || role(b).is_none() || role(a) != role(b)))
                    })
                })
        })
    })
}

fn rust_common_guard(
    evidence: Option<&ConcurrencyEvidenceSet>,
    locations: &[String],
    topology: ColocationPattern,
    record: Option<&StructInfo>,
) -> bool {
    if evidence.is_some_and(|set| {
        set.evidence.iter().any(|item| {
            item.semantic_contexts
                .iter()
                .any(|context| context == "rust_object_evidence_incomplete")
        })
    }) {
        return false;
    }
    let fields = normalized_location_set(locations);
    let items = evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .filter(|item| {
            item.access_kind.is_some()
                && item
                    .field_name
                    .as_deref()
                    .is_some_and(|field| fields.contains(field))
                && (!item.access_mode.is_exclusive() || item.through_raw_pointer)
                && !item
                    .semantic_contexts
                    .iter()
                    .any(|context| context == "container_element_pointee")
        })
        .collect::<Vec<_>>();
    if items.is_empty()
        || fields.iter().any(|field| {
            !items
                .iter()
                .any(|item| item.field_name.as_deref() == Some(field))
        })
    {
        return false;
    }
    let guards = |item: &crate::types::EvidenceItem| {
        item.semantic_contexts
            .iter()
            .filter_map(|context| context.strip_prefix("rust_guarded_by:"))
            .filter(|guard| {
                guard.starts_with("global:")
                    || (matches!(
                        topology,
                        ColocationPattern::SameObjectFields | ColocationPattern::ContiguousElements
                    ) && record.is_some_and(|record| {
                        guard.starts_with(&format!(
                            "relative:{}:{}:",
                            record.crate_name.as_deref().unwrap_or("unknown"),
                            crate::types::StructKey::from_struct(record).qualified_name()
                        ))
                    }) && guard
                        .split_once("value_origin:")
                        .and_then(|(_, tail)| tail.rsplit_once(':'))
                        .is_some_and(|(origin, _)| {
                            item.semantic_contexts
                                .contains(&format!("value_origin:{origin}"))
                        }))
            })
            .map(str::to_owned)
            .collect::<HashSet<_>>()
    };
    let mut common = guards(items[0]);
    for item in items.iter().skip(1) {
        let held = guards(item);
        common.retain(|guard| held.contains(guard));
    }
    !common.is_empty()
}

/// The topology families each report rule is allowed to represent. Both
/// frontends use this table, so a rule ID cannot silently acquire a different
/// theoretical meaning in C++ and Rust.
pub fn rule_supports_topology(rule: CandidateKind, topology: ColocationPattern) -> bool {
    match rule {
        CandidateKind::FieldGroup | CandidateKind::WriterNeighbor | CandidateKind::MixedFields => {
            topology == ColocationPattern::SameObjectFields
        }
        CandidateKind::ContainerElements
        | CandidateKind::IndexedWrites
        | CandidateKind::AtomicArray
        | CandidateKind::SiblingArrays => topology == ColocationPattern::ContiguousElements,
        CandidateKind::ObjectInstances => matches!(
            topology,
            ColocationPattern::AdjacentObjects | ColocationPattern::AllocatorObjects
        ),
        CandidateKind::StaticData => matches!(
            topology,
            ColocationPattern::StaticStorage | ColocationPattern::ContiguousElements
        ),
        CandidateKind::SeparateAllocations => topology == ColocationPattern::AllocatorObjects,
    }
}

pub fn default_colocation_pattern(rule: CandidateKind) -> ColocationPattern {
    match rule {
        CandidateKind::FieldGroup | CandidateKind::WriterNeighbor | CandidateKind::MixedFields => {
            ColocationPattern::SameObjectFields
        }
        CandidateKind::ContainerElements
        | CandidateKind::IndexedWrites
        | CandidateKind::AtomicArray
        | CandidateKind::SiblingArrays => ColocationPattern::ContiguousElements,
        CandidateKind::ObjectInstances => ColocationPattern::AdjacentObjects,
        CandidateKind::StaticData => ColocationPattern::StaticStorage,
        CandidateKind::SeparateAllocations => ColocationPattern::AllocatorObjects,
    }
}

pub fn layout_evidence(si: &StructInfo) -> ColocationEvidence {
    match si.layout_source {
        LayoutSource::RustcExact => ColocationEvidence::CompilerExact,
        LayoutSource::ReprCEstimate if si.cache_line_groups_precise => {
            ColocationEvidence::RepresentationBounded
        }
        _ if si.cache_line_groups_precise => ColocationEvidence::SourceEstimated,
        _ => ColocationEvidence::Symbolic,
    }
}

fn classify_access_pattern(
    evidence: Option<&ConcurrencyEvidenceSet>,
    locations: &[String],
    implicit_write: bool,
) -> AccessPattern {
    let candidates: HashSet<&str> = locations.iter().map(String::as_str).collect();
    let mut writes = HashSet::new();
    let mut reads = HashSet::new();

    for item in evidence.into_iter().flat_map(|set| &set.evidence) {
        let Some(field) = item.field_name.as_deref() else {
            continue;
        };
        if !candidates.contains(field) {
            continue;
        }
        match item.access_kind {
            Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite) => {
                writes.insert(field);
            }
            Some(AtomicAccessKind::Read) => {
                reads.insert(field);
            }
            None => {}
        }
    }

    if writes.len() >= 2 {
        AccessPattern::WriteWrite
    } else if writes
        .iter()
        .any(|writer| reads.iter().any(|reader| reader != writer))
    {
        AccessPattern::WriteRead
    } else {
        let _ = implicit_write;
        AccessPattern::WriteUnknownPeer
    }
}

fn classify_parallelism(
    project_visible_type: bool,
    evidence: Option<&ConcurrencyEvidenceSet>,
    api_usage: Option<&ApiUsageEvidenceSet>,
    locations: &[String],
    colocation_pattern: ColocationPattern,
    independently_accessible: bool,
) -> ParallelismEvidence {
    let candidates = normalized_location_set(locations);
    let matching_items: Vec<_> = evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .filter(|item| {
            item.field_name
                .as_deref()
                .is_some_and(|field| candidates.contains(field))
        })
        .collect();
    let concurrent_agent_access = matching_items.iter().any(|item| {
        item.in_concurrent_context
            && (!item.access_mode.is_exclusive()
                || item.through_shared_indirection
                || item.through_raw_pointer)
    });
    let concurrent_written_locations = matching_items
        .iter()
        .filter(|item| {
            item.in_concurrent_context
                && matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
        })
        .filter_map(|item| item.field_name.as_deref())
        .collect::<HashSet<_>>()
        .len();
    if concurrent_agent_access || concurrent_written_locations >= 2 {
        return ParallelismEvidence::ConcurrentContext;
    }

    let indexed_topology = matches!(
        colocation_pattern,
        ColocationPattern::ContiguousElements
            | ColocationPattern::AdjacentObjects
            | ColocationPattern::AllocatorObjects
    );
    let explicit_parallel_topology = indexed_topology
        && evidence.is_some_and(|set| {
            set.evidence.iter().any(|item| {
                matches!(
                    item.kind,
                    EvidenceKind::UsedInParallelIter | EvidenceKind::UsedInSpawn
                )
            })
        });
    if explicit_parallel_topology {
        return ParallelismEvidence::ConcurrentContext;
    }

    // Shared ownership is type-wide, while false sharing is a relation between
    // two locations. Require the ownership/raw-pointer path to reach a member
    // of this candidate pair; for same-object fields also require separable
    // access roles. This is the pair-scoped MHP anti-rule.
    let candidate_shared_reachability = matching_items.iter().any(|item| {
        item.through_shared_indirection
            || item.through_raw_pointer
            || item
                .semantic_contexts
                .iter()
                .any(|context| context == "external_object_access")
    });
    let send_sync_capability = evidence.is_some_and(|set| {
        set.evidence
            .iter()
            .any(|item| item.kind == EvidenceKind::SendSyncCapability)
    });
    let indexed_arc_reachability = indexed_topology
        && !matching_items.is_empty()
        && matching_items
            .iter()
            .any(|item| !item.access_mode.is_exclusive())
        && evidence.is_some_and(|set| set.has_kind(EvidenceKind::ArcWrapped));
    if (candidate_shared_reachability || send_sync_capability || indexed_arc_reachability)
        && (indexed_topology || independently_accessible)
    {
        ParallelismEvidence::SharedReachability
    } else if api_usage.is_some_and(ApiUsageEvidenceSet::has_exposed_type_signal)
        && has_nonexclusive_trait_access(evidence, locations)
        && independently_accessible
    {
        // A trait method's visibility is inherited from its trait, so syn does
        // not mark the impl method `pub`.  For an exposed concrete type, a
        // non-exclusive trait access is the trait analogue of a public &self
        // capability and can be invoked by independent callers.
        ParallelismEvidence::ExternalApiPotential
    } else if project_visible_type
        && has_nonexclusive_trait_access(evidence, locations)
        && independently_accessible
    {
        // `pub(crate)` and `pub` items behind private modules are not external
        // API, but their shared-receiver trait methods remain independently
        // callable inside the project. Keep that capability distinct from
        // external exposure so risk categorization does not overstate it.
        ParallelismEvidence::SharedReachability
    } else if api_usage.is_some_and(ApiUsageEvidenceSet::has_parallel_usage_signal)
        && (indexed_topology || independently_accessible)
    {
        ParallelismEvidence::ExternalApiPotential
    } else {
        ParallelismEvidence::Unresolved
    }
}

fn has_nonexclusive_trait_access(
    evidence: Option<&ConcurrencyEvidenceSet>,
    locations: &[String],
) -> bool {
    let candidates = normalized_location_set(locations);
    evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .any(|item| {
            !item.access_mode.is_exclusive()
                && item
                    .field_name
                    .as_deref()
                    .is_some_and(|field| candidates.contains(field))
                && item
                    .semantic_contexts
                    .iter()
                    .any(|context| context == "trait_impl")
        })
}

fn has_matching_write(evidence: Option<&ConcurrencyEvidenceSet>, locations: &[String]) -> bool {
    let candidates = normalized_location_set(locations);
    evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .any(|item| {
            matches!(
                item.access_kind,
                Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
            ) && item
                .field_name
                .as_deref()
                .is_some_and(|field| candidates.contains(field))
        })
}

fn matching_accessed_locations(
    evidence: Option<&ConcurrencyEvidenceSet>,
    locations: &[String],
) -> usize {
    let candidates = normalized_location_set(locations);
    evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .filter_map(|item| item.field_name.as_deref())
        .filter(|field| candidates.contains(field))
        .collect::<HashSet<_>>()
        .len()
}

fn has_repetition_evidence(
    evidence: Option<&ConcurrencyEvidenceSet>,
    locations: &[String],
) -> bool {
    let candidates = normalized_location_set(locations);
    evidence
        .into_iter()
        .flat_map(|set| &set.evidence)
        .any(|item| {
            item.hotness_score > 1.0
                && item
                    .field_name
                    .as_deref()
                    .is_some_and(|field| candidates.contains(field))
        })
}

/// A field pair is independently addressable when two non-exclusive access
/// paths partition the candidate set in different ways. Merely observing two
/// fields in one compound protocol operation does not establish false sharing:
/// it is true sharing of one logical state at the abstraction level available
/// to the analyzer.
pub fn has_separable_access_partitions(
    evidence: Option<&ConcurrencyEvidenceSet>,
    locations: &[String],
) -> bool {
    let candidates = normalized_location_set(locations);
    if candidates.len() < 2 {
        return false;
    }
    let mut per_access_role: std::collections::HashMap<String, HashSet<&str>> =
        std::collections::HashMap::new();
    for item in evidence.into_iter().flat_map(|set| &set.evidence) {
        if item.access_kind.is_none() || item.access_mode.is_exclusive() {
            continue;
        }
        let Some(field) = item.field_name.as_deref() else {
            continue;
        };
        if !candidates.contains(field) {
            continue;
        }
        let Some(function) = item.function_name.as_deref() else {
            continue;
        };
        let control_partition = item
            .semantic_contexts
            .iter()
            .filter(|context| context.starts_with("control_partition:"))
            .cloned()
            .collect::<Vec<_>>()
            .join("/");
        let control_partition = if control_partition.is_empty() {
            "control_partition:root".to_string()
        } else {
            control_partition
        };
        per_access_role
            .entry(format!("{function}@{control_partition}"))
            .or_default()
            .insert(field);
    }

    let partitions: Vec<_> = per_access_role.values().collect();
    partitions.iter().enumerate().any(|(left_idx, left)| {
        partitions.iter().skip(left_idx + 1).any(|right| {
            left.iter().any(|field| !right.contains(field))
                && right.iter().any(|field| !left.contains(field))
        })
    })
}

/// Explicitly concurrent writers are a relation-level witness even when they
/// are syntactically nested in one scoped function. W-R roles alone are not
/// sufficient here: a snapshot reader and a writer touching the same protocol
/// state are true sharing unless their per-function field sets form distinct
/// partitions, which `has_separable_access_partitions` handles above.
fn has_distinct_access_roles(
    evidence: Option<&ConcurrencyEvidenceSet>,
    locations: &[String],
) -> bool {
    let candidates = normalized_location_set(locations);
    let mut concurrent_writes = HashSet::new();
    for item in evidence.into_iter().flat_map(|set| &set.evidence) {
        let Some(field) = item.field_name.as_deref() else {
            continue;
        };
        if !candidates.contains(field) {
            continue;
        }
        match item.access_kind {
            Some(AtomicAccessKind::Read) => {}
            Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite) => {
                if item.in_concurrent_context {
                    concurrent_writes.insert(field);
                }
            }
            None => {}
        }
    }
    concurrent_writes.len() >= 2
}

fn normalized_location_set(locations: &[String]) -> HashSet<&str> {
    locations
        .iter()
        .filter_map(|location| location_field_name(location))
        .collect()
}

fn location_field_name(location: &str) -> Option<&str> {
    let tail = location.rsplit('.').next()?;
    Some(tail.split('[').next().unwrap_or(tail))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_predicate_requires_every_coherence_precondition() {
        let mut pattern = StaticPatternContext {
            model_version: STATIC_PATTERN_MODEL_VERSION,
            rule_id: crate::types::RuleId::ContiguousElements,
            candidate_kind: CandidateKind::IndexedWrites,
            frontend: "test",
            language_specific_assumptions: Vec::new(),
            access_pattern: AccessPattern::WriteWrite,
            colocation_pattern: ColocationPattern::ContiguousElements,
            parallelism_evidence: ParallelismEvidence::ConcurrentContext,
            colocation_evidence: ColocationEvidence::SourceEstimated,
            distinct_locations: true,
            distinct_accesses: true,
            independently_accessible: true,
            may_share_cache_line: true,
            may_happen_in_parallel: true,
            has_write: true,
            repetition_evidence: false,
            protection_excluded: true,
            witness_locations: vec!["slot[0]".into(), "slot[1]".into()],
        };
        assert!(core_predicate_holds(&pattern));
        pattern.protection_excluded = false;
        assert!(!core_predicate_holds(&pattern));
    }
}
