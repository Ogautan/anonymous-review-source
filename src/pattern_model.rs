//! Language-neutral false-sharing pattern calculus and Rust adapter.
//!
//! Rules are report families.  This module defines the orthogonal semantic
//! dimensions that make a source location a false-sharing may-risk:
//! interference, cache-line co-location, may-parallel reachability, and the
//! absence of recognized isolation.  Keeping this predicate independent of
//! repository, type, and field names makes its coverage auditable.

use std::collections::HashSet;

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
    let access_pattern = classify_access_pattern(evidence, &locations, implicit_write);
    let independently_accessible = colocation_pattern != ColocationPattern::SameObjectFields
        || has_separable_access_partitions(evidence, &locations)
        || has_distinct_access_roles(evidence, &locations);
    let parallelism_evidence = implicit_parallelism.unwrap_or_else(|| {
        classify_parallelism(
            si.is_some_and(|record| record.visibility.is_exposed()),
            evidence,
            api_usage,
            &locations,
            colocation_pattern,
            independently_accessible,
        )
    });
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
        protection_excluded,
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
