//! Rust finding construction and serialization of recovered access facts.
use crate::helpers::stable_finding_hash;
use crate::types::{
    AccessEvidenceContext, AccessMode, AtomicAccessKind, CandidateKind, ConcurrencyEvidenceSet,
    EvidenceItem, EvidenceKind, Finding, RiskCategory, Severity, UsageLocation,
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn make_finding(
    category: RiskCategory,
    rule: CandidateKind,
    title: &'static str,
    severity: Severity,
    file: &str,
    line: usize,
    crate_name: Option<&str>,
    snippet: String,
    suggestion: &'static str,
    confidence: f32,
    struct_name: Option<&str>,
    field_list: &[String],
    evidence_descs: &[String],
    evidence_set: Option<&ConcurrencyEvidenceSet>,
) -> Finding {
    let finding_hash = stable_finding_hash(rule.identity_salt(), file, line, &snippet);
    let usage_locations = evidence_set
        .map(|ev| {
            ev.evidence
                .iter()
                .map(|item| UsageLocation {
                    file: item.file.clone(),
                    line: item.line,
                    description: item.description.clone(),
                })
                .collect()
        })
        .unwrap_or_default();
    let access_evidence = evidence_set
        .map(|set| set.evidence.iter().map(access_evidence_context).collect())
        .unwrap_or_default();

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
        crate_name: crate_name.map(|s| s.to_string()),
        snippet,
        suggestion,
        confidence,
        struct_name: struct_name.map(|s| s.to_string()),
        symbol: finding_symbol(struct_name, field_list),
        field_list: field_list.to_vec(),
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

fn access_evidence_context(item: &EvidenceItem) -> AccessEvidenceContext {
    AccessEvidenceContext {
        evidence_kind: match item.kind {
            EvidenceKind::ArcWrapped => "shared_ownership",
            EvidenceKind::MutexWrapped => "mutex_wrapped",
            EvidenceKind::RwLockWrapped => "rwlock_wrapped",
            EvidenceKind::SendSyncCapability => "send_sync_capability",
            EvidenceKind::UsedInSpawn => "thread_spawn",
            EvidenceKind::UsedInParallelIter => "parallel_iterator",
            EvidenceKind::AtomicFieldOps => "atomic_field_operation",
            EvidenceKind::HotSyncFieldOps => "hot_sync_operation",
            EvidenceKind::PlainFieldWrite => "plain_field_write",
            EvidenceKind::PlainFieldRead => "plain_field_read",
            EvidenceKind::FieldAccessInConcurrentContext => "concurrent_field_access",
        }
        .to_string(),
        access_kind: item.access_kind.as_ref().map(|kind| {
            match kind {
                AtomicAccessKind::Read => "read",
                AtomicAccessKind::Write => "write",
                AtomicAccessKind::ReadModifyWrite => "read_modify_write",
            }
            .to_string()
        }),
        field_name: item.field_name.clone(),
        hotness_score: item.hotness_score,
        in_concurrent_context: item.in_concurrent_context,
        access_mode: match item.access_mode {
            AccessMode::Unknown => "unknown",
            AccessMode::Shared => "shared",
            AccessMode::Exclusive => "exclusive",
        }
        .to_string(),
        function_name: item.function_name.clone(),
        propagation_depth: item.propagation_depth,
        call_path: item.call_path.clone(),
        semantic_contexts: item.semantic_contexts.clone(),
        through_shared_indirection: item.through_shared_indirection,
        through_raw_pointer: item.through_raw_pointer,
        file: item.file.clone(),
        line: item.line,
        description: item.description.clone(),
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

pub(crate) fn with_risk_factors(mut finding: Finding, risk_factors: Vec<String>) -> Finding {
    finding.risk_factors = risk_factors;
    finding
}
