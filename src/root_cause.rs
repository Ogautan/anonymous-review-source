use std::collections::HashMap;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::types::{
    AccessEvidenceContext, CandidateKind, ColocationPattern, Finding, RiskCategory, Severity,
    UsageLocation,
};

/// Findings after record/object-level root-cause clustering.
///
/// `occurrence_count` counts detector findings before clustering (after exact
/// duplicate removal). `findings.len()` is therefore the number of root-cause
/// groups that require review.
pub struct ClusteredFindings {
    pub findings: Vec<Finding>,
    pub occurrence_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RootCauseKey {
    project: String,
    file: String,
    kind: &'static str,
    object: String,
    /// Avoids merging two same-named declarations in one file and keeps group
    /// IDs unique within a report.
    declaration_line: Option<usize>,
}

/// Merge detector occurrences that describe the same reviewable root cause.
///
/// Record findings retain their declaration, topology and padding components.
/// Bound array occurrences share a declaration key across files and compatible
/// rule families. Unresolved findings retain the legacy file-local grouping.
/// This is a reporting operation; merged evidence cannot establish a new risk.
pub fn cluster_findings(root: &Path, findings: Vec<Finding>) -> ClusteredFindings {
    let normalized_root = normalized_root(root);
    let occurrence_count = findings
        .iter()
        .map(|finding| finding.finding_occurrence_count.max(1))
        .sum();
    let mut groups: Vec<Finding> = Vec::new();
    let mut positions: HashMap<RootCauseKey, usize> = HashMap::new();

    for mut finding in findings {
        finding.finding_occurrence_count = finding.finding_occurrence_count.max(1);
        if !finding
            .usage_locations
            .iter()
            .any(|site| site.file == finding.file && site.line == finding.line)
        {
            finding.usage_locations.push(UsageLocation {
                file: finding.file.clone(),
                line: finding.line,
                description: format!("{} occurrence", finding.candidate_kind),
            });
        }
        let key = root_cause_key(&normalized_root, &finding);
        let group_id = stable_group_id(&key, &finding);

        if let Some(position) = positions.get(&key).copied() {
            merge_finding(&mut groups[position], finding);
        } else {
            finding.finding_group_id = group_id;
            normalize_group(&mut finding);
            positions.insert(key, groups.len());
            groups.push(finding);
        }
    }

    ClusteredFindings {
        findings: groups,
        occurrence_count,
    }
}

/// Attach the broad group identity before a frontend refines an occurrence's
/// fields. This lets it count rejected groups without confusing a narrower
/// supported location set with a wholly rejected risk.
pub(crate) fn assign_group_ids(root: &Path, findings: &mut [Finding]) {
    let normalized_root = normalized_root(root);
    for finding in findings {
        let key = root_cause_key(&normalized_root, finding);
        finding.finding_group_id = stable_group_id(&key, finding);
    }
}

fn normalized_root(root: &Path) -> PathBuf {
    std::fs::canonicalize(root).unwrap_or_else(|_| root.to_path_buf())
}

fn root_cause_key(root: &Path, finding: &Finding) -> RootCauseKey {
    let project = finding
        .crate_name
        .clone()
        .unwrap_or_else(|| "unknown".to_string());
    let file = relative_file(root, &finding.file);

    if let Some(record) = &finding.struct_name {
        let layout = finding.layout_context.as_ref();
        let declaration_line = layout
            .map(|layout| layout.declaration_line)
            .unwrap_or(finding.line);
        let mut object = layout
            .map(|layout| layout.canonical_type.clone())
            .filter(|identity| !identity.is_empty())
            .unwrap_or_else(|| record.clone());
        if let Some(component) = cpp_record_component(finding) {
            object.push('|');
            object.push_str(&component);
        }
        let normalized_storage_identity = finding
            .storage_identity
            .as_deref()
            .map(|identity| relative_storage_identity(root, identity));
        return RootCauseKey {
            project,
            file: normalized_storage_identity
                .as_ref()
                .and_then(|identity| identity.split_once("::").map(|(file, _)| file.to_string()))
                .unwrap_or(file),
            kind: record_topology_family(finding),
            object,
            declaration_line: Some(declaration_line),
        };
    }

    if let Some(storage_identity) = &finding.storage_identity {
        let normalized_storage_identity = relative_storage_identity(root, storage_identity);
        return RootCauseKey {
            project,
            file: normalized_storage_identity.clone(),
            kind: match finding
                .static_pattern
                .as_ref()
                .map(|p| p.colocation_pattern)
            {
                Some(ColocationPattern::ContiguousElements) => "storage_contiguous_elements",
                Some(ColocationPattern::StaticStorage)
                    if finding.candidate_kind == CandidateKind::StaticData
                        && finding.field_list.len() == 1 =>
                {
                    "storage_contiguous_elements"
                }
                _ => rule_family(finding.candidate_kind),
            },
            object: normalized_storage_identity.clone(),
            declaration_line: None,
        };
    }

    let mut fields = finding.field_list.clone();
    fields.sort();
    fields.dedup();
    let storage_identity = matches!(
        finding.candidate_kind,
        CandidateKind::ContainerElements
            | CandidateKind::StaticData
            | CandidateKind::IndexedWrites
            | CandidateKind::AtomicArray
            | CandidateKind::SiblingArrays
    )
    .then(|| (!fields.is_empty()).then(|| fields.join("+")))
    .flatten();
    let object = storage_identity
        .or_else(|| finding.symbol.clone().filter(|symbol| !symbol.is_empty()))
        .or_else(|| (!fields.is_empty()).then(|| fields.join("+")))
        .unwrap_or_else(|| finding.finding_hash.clone());

    RootCauseKey {
        project,
        file,
        kind: rule_family(finding.candidate_kind),
        object,
        declaration_line: None,
    }
}

fn record_topology_family(finding: &Finding) -> &'static str {
    match finding
        .static_pattern
        .as_ref()
        .map(|pattern| pattern.colocation_pattern)
    {
        Some(ColocationPattern::SameObjectFields) | None => "record_same_object",
        Some(ColocationPattern::ContiguousElements) => "record_contiguous_elements",
        Some(ColocationPattern::AdjacentObjects) => "record_adjacent_objects",
        Some(ColocationPattern::AllocatorObjects) => "record_allocator_objects",
        Some(ColocationPattern::StaticStorage) => "record_static_storage",
    }
}

/// Record-level clustering must not reconstruct a candidate across a padding
/// boundary.  Findings on opposite sides are separate reviewable root causes,
/// even when they belong to the same declaration and different rules.
fn cpp_record_component(finding: &Finding) -> Option<String> {
    let layout = finding.layout_context.as_ref()?;
    if layout.language != "cpp" || finding.field_list.is_empty() {
        return None;
    }
    let selected = finding
        .field_list
        .iter()
        .collect::<std::collections::HashSet<_>>();
    let mut segment = 0usize;
    let mut selected_segments = Vec::new();
    for field in &layout.fields {
        if selected.contains(&field.name) && !selected_segments.contains(&segment) {
            selected_segments.push(segment);
        }
        if field.is_manual_padding || field.is_cache_padded {
            segment += 1;
        }
    }
    if selected_segments.is_empty() {
        return None;
    }
    Some(format!(
        "component:{}",
        selected_segments
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join("+")
    ))
}

fn relative_file(root: &Path, file: &str) -> String {
    let path = Path::new(file);
    let relative = path.strip_prefix(root).unwrap_or(path);
    relative
        .components()
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

fn relative_storage_identity(root: &Path, identity: &str) -> String {
    let Some((file, object)) = identity.split_once("::") else {
        return relative_file(root, identity);
    };
    format!("{}::{object}", relative_file(root, file))
}

fn rule_family(candidate_kind: CandidateKind) -> &'static str {
    match candidate_kind {
        CandidateKind::StaticData => "static_state",
        CandidateKind::IndexedWrites => "indexed_stride",
        CandidateKind::AtomicArray => "atomic_alias_stride",
        CandidateKind::ContainerElements | CandidateKind::SiblingArrays => "container_stride",
        _ => "source_candidate",
    }
}

fn stable_group_id(key: &RootCauseKey, finding: &Finding) -> String {
    let language = finding
        .layout_context
        .as_ref()
        .map(|layout| layout.language.as_str())
        .unwrap_or("unknown");
    let layout_identity = finding
        .layout_context
        .as_ref()
        .map(layout_identity)
        .unwrap_or_default();
    let layout_identity = if key.kind == "storage_contiguous_elements" {
        String::new()
    } else {
        layout_identity
    };
    let material = format!(
        "{}|{}|{}|{}|{}|{:?}|{}",
        key.project,
        key.file,
        language,
        key.kind,
        key.object,
        key.declaration_line,
        layout_identity
    );
    let mut hasher = Sha256::new();
    hasher.update(material.as_bytes());
    format!("fsg-{}", &hex::encode(hasher.finalize())[..24])
}

fn layout_identity(layout: &crate::types::LayoutContext) -> String {
    let fields = layout
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}:{}:{:?}:{:?}",
                field.name, field.ty, field.offset, field.estimated_size
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let cache_lines = layout
        .cache_line_groups
        .iter()
        .map(|group| group.join("+"))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{}|{:?}|{:?}|{}|{}",
        layout.layout_source,
        layout.total_estimated_size,
        layout.repr_align_bytes,
        fields,
        cache_lines
    )
}

fn merge_finding(existing: &mut Finding, mut incoming: Finding) {
    let group_id = existing.finding_group_id.clone();
    let occurrence_count = existing
        .finding_occurrence_count
        .saturating_add(incoming.finding_occurrence_count.max(1));
    let mut all_rules = vec![existing.candidate_kind, incoming.candidate_kind];
    all_rules.extend(existing.related_candidate_kinds.iter().copied());
    all_rules.extend(incoming.related_candidate_kinds.iter().copied());

    if should_replace_representative(existing, &incoming) {
        std::mem::swap(existing, &mut incoming);
    }

    if category_rank(&incoming.category) > category_rank(&existing.category) {
        existing.category = incoming.category;
    }
    if severity_rank(&incoming.severity) > severity_rank(&existing.severity) {
        existing.severity = incoming.severity;
    }
    existing.confidence = existing.confidence.max(incoming.confidence);
    if existing.layout_context.is_none() {
        existing.layout_context = incoming.layout_context.take();
    }
    if existing.static_pattern.is_none() {
        existing.static_pattern = incoming.static_pattern.take();
    }
    if existing.crate_name.is_none() {
        existing.crate_name = incoming.crate_name.take();
    }

    extend_unique(&mut existing.field_list, incoming.field_list);
    extend_unique(&mut existing.risk_factors, incoming.risk_factors);
    extend_unique(
        &mut existing.concurrency_evidence,
        incoming.concurrency_evidence,
    );
    extend_unique_locations(&mut existing.usage_locations, incoming.usage_locations);
    extend_unique_accesses(&mut existing.access_evidence, incoming.access_evidence);

    all_rules.sort_unstable();
    all_rules.dedup();
    all_rules.retain(|rule| *rule != existing.candidate_kind);
    existing.related_candidate_kinds = all_rules;
    existing.finding_group_id = group_id;
    existing.finding_occurrence_count = occurrence_count;
    normalize_group(existing);
}

fn should_replace_representative(existing: &Finding, incoming: &Finding) -> bool {
    rule_specificity(incoming.candidate_kind)
        .cmp(&rule_specificity(existing.candidate_kind))
        .then_with(|| category_rank(&incoming.category).cmp(&category_rank(&existing.category)))
        .then_with(|| severity_rank(&incoming.severity).cmp(&severity_rank(&existing.severity)))
        .then_with(|| incoming.confidence.total_cmp(&existing.confidence))
        .then_with(|| existing.finding_hash.cmp(&incoming.finding_hash))
        .is_gt()
}

fn rule_specificity(candidate_kind: CandidateKind) -> u8 {
    match candidate_kind {
        CandidateKind::SeparateAllocations => 100,
        CandidateKind::SiblingArrays => 95,
        CandidateKind::AtomicArray => 94,
        CandidateKind::IndexedWrites => 93,
        CandidateKind::StaticData => 92,
        CandidateKind::ObjectInstances => 90,
        CandidateKind::ContainerElements => 85,
        CandidateKind::MixedFields => 70,
        CandidateKind::WriterNeighbor => 60,
        CandidateKind::FieldGroup => 50,
    }
}

fn category_rank(category: &RiskCategory) -> u8 {
    match category {
        RiskCategory::HotInProject => 3,
        RiskCategory::ApiUsageLatent => 2,
        RiskCategory::ColdOrConditional => 1,
    }
}

fn severity_rank(severity: &Severity) -> u8 {
    match severity {
        Severity::High => 3,
        Severity::Medium => 2,
        Severity::Low => 1,
    }
}

fn extend_unique<T: PartialEq>(target: &mut Vec<T>, source: Vec<T>) {
    for item in source {
        if !target.contains(&item) {
            target.push(item);
        }
    }
}

fn extend_unique_locations(target: &mut Vec<UsageLocation>, source: Vec<UsageLocation>) {
    for location in source {
        if !target
            .iter()
            .any(|current| same_location(current, &location))
        {
            target.push(location);
        }
    }
}

fn same_location(left: &UsageLocation, right: &UsageLocation) -> bool {
    left.file == right.file && left.line == right.line && left.description == right.description
}

fn extend_unique_accesses(
    target: &mut Vec<AccessEvidenceContext>,
    source: Vec<AccessEvidenceContext>,
) {
    for access in source {
        if !target.iter().any(|current| same_access(current, &access)) {
            target.push(access);
        }
    }
}

fn same_access(left: &AccessEvidenceContext, right: &AccessEvidenceContext) -> bool {
    left.evidence_kind == right.evidence_kind
        && left.access_kind == right.access_kind
        && left.field_name == right.field_name
        && left.hotness_score == right.hotness_score
        && left.in_concurrent_context == right.in_concurrent_context
        && left.access_mode == right.access_mode
        && left.function_name == right.function_name
        && left.propagation_depth == right.propagation_depth
        && left.call_path == right.call_path
        && left.semantic_contexts == right.semantic_contexts
        && left.through_shared_indirection == right.through_shared_indirection
        && left.through_raw_pointer == right.through_raw_pointer
        && left.file == right.file
        && left.line == right.line
        && left.description == right.description
}

fn normalize_group(finding: &mut Finding) {
    finding.field_list.sort();
    finding.field_list.dedup();
    finding.related_candidate_kinds.sort_unstable();
    finding.related_candidate_kinds.dedup();
    finding
        .related_candidate_kinds
        .retain(|rule| *rule != finding.candidate_kind);
    finding.usage_locations.sort_by(|left, right| {
        left.file
            .cmp(&right.file)
            .then_with(|| left.line.cmp(&right.line))
            .then_with(|| left.description.cmp(&right.description))
    });
    finding.access_evidence.sort_by(|left, right| {
        left.file
            .cmp(&right.file)
            .then_with(|| left.line.cmp(&right.line))
            .then_with(|| left.field_name.cmp(&right.field_name))
            .then_with(|| left.evidence_kind.cmp(&right.evidence_kind))
            .then_with(|| left.function_name.cmp(&right.function_name))
    });
    if let Some(record) = &finding.struct_name {
        let default_record_symbol = finding.symbol.as_deref().is_none_or(|symbol| {
            symbol == record
                || symbol
                    .strip_prefix(record)
                    .is_some_and(|tail| tail.starts_with('.'))
        });
        if default_record_symbol {
            finding.symbol = Some(record.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{LayoutContext, LayoutFieldContext, RiskCategory, Severity};

    fn record_finding(
        file: &str,
        canonical_type: &str,
        candidate_kind: CandidateKind,
        field: &str,
        occurrence_line: usize,
    ) -> Finding {
        Finding {
            category: RiskCategory::ColdOrConditional,
            rule_id: crate::pattern_model::default_colocation_pattern(candidate_kind).rule_id(),
            candidate_kind,
            related_candidate_kinds: Vec::new(),
            finding_group_id: String::new(),
            finding_occurrence_count: 1,
            title: "test finding",
            severity: Severity::Medium,
            file: file.to_string(),
            line: occurrence_line,
            crate_name: Some("fixture".to_string()),
            snippet: format!("State.{field}"),
            suggestion: "test suggestion",
            confidence: 0.5,
            struct_name: Some("State".to_string()),
            symbol: Some(format!("State.{field}")),
            field_list: vec![field.to_string()],
            static_pattern: None,
            layout_context: Some(LayoutContext {
                language: "rust".to_string(),
                struct_name: "State".to_string(),
                canonical_type: canonical_type.to_string(),
                declaration_line: 10,
                cache_line_size: 64,
                layout_certainty: "estimated".to_string(),
                fields: Vec::new(),
                cache_line_groups: Vec::new(),
                cache_line_groups_precise: false,
                repr_c: false,
                repr_rust: true,
                repr_align_bytes: None,
                repr_packed: false,
                has_cache_padded: false,
                manual_padding_fields: Vec::new(),
                total_estimated_size: Some(16),
                layout_source: "rust_default_estimate".to_string(),
                used_rustc_layout: false,
            }),
            access_evidence: Vec::new(),
            risk_factors: vec![format!("risk for {field}")],
            concurrency_evidence: Vec::new(),
            usage_locations: vec![UsageLocation {
                file: file.to_string(),
                line: occurrence_line,
                description: format!("write {field}"),
            }],
            finding_hash: format!("{candidate_kind}-{field}-{occurrence_line}"),
            storage_identity: None,
        }
    }

    #[test]
    fn merges_record_fields_rules_and_locations_into_one_group() {
        let first = record_finding(
            "/checkout/src/lib.rs",
            "runtime::State",
            CandidateKind::FieldGroup,
            "left",
            20,
        );
        let second = record_finding(
            "/checkout/src/lib.rs",
            "runtime::State",
            CandidateKind::ObjectInstances,
            "right",
            30,
        );

        let clustered = cluster_findings(Path::new("/checkout"), vec![first, second]);

        assert_eq!(clustered.occurrence_count, 2);
        assert_eq!(clustered.findings.len(), 1);
        let group = &clustered.findings[0];
        assert_eq!(group.finding_occurrence_count, 2);
        assert_eq!(group.candidate_kind, "object_instances");
        assert_eq!(group.related_candidate_kinds, [CandidateKind::FieldGroup]);
        assert_eq!(group.field_list, ["left", "right"]);
        assert_eq!(group.usage_locations.len(), 2);
        assert_eq!(group.symbol.as_deref(), Some("State"));
    }

    #[test]
    fn preserves_an_explicit_allocation_site_callable_symbol() {
        let mut finding = record_finding(
            "/checkout/src/state.cpp",
            "runtime::State",
            CandidateKind::SeparateAllocations,
            "counter",
            20,
        );
        finding.symbol = Some("allocate_state".to_string());
        let clustered = cluster_findings(Path::new("/checkout"), vec![finding]);
        assert_eq!(
            clustered.findings[0].symbol.as_deref(),
            Some("allocate_state")
        );
    }

    #[test]
    fn group_id_ignores_checkout_path_and_occurrence_lines() {
        let first = record_finding(
            "/first/src/lib.rs",
            "runtime::State",
            CandidateKind::FieldGroup,
            "left",
            20,
        );
        let second = record_finding(
            "/second/src/lib.rs",
            "runtime::State",
            CandidateKind::FieldGroup,
            "left",
            200,
        );

        let first_id = cluster_findings(Path::new("/first"), vec![first]).findings[0]
            .finding_group_id
            .clone();
        let second_id = cluster_findings(Path::new("/second"), vec![second]).findings[0]
            .finding_group_id
            .clone();

        assert_eq!(first_id, second_id);
    }

    #[test]
    fn canonical_type_keeps_same_named_module_records_separate() {
        let first = record_finding(
            "/checkout/src/lib.rs",
            "first::State",
            CandidateKind::FieldGroup,
            "left",
            20,
        );
        let second = record_finding(
            "/checkout/src/lib.rs",
            "second::State",
            CandidateKind::FieldGroup,
            "left",
            40,
        );

        let clustered = cluster_findings(Path::new("/checkout"), vec![first, second]);
        let ids: std::collections::HashSet<_> = clustered
            .findings
            .iter()
            .map(|finding| finding.finding_group_id.as_str())
            .collect();

        assert_eq!(clustered.findings.len(), 2);
        assert_eq!(ids.len(), 2);
    }

    #[test]
    fn declaration_line_keeps_duplicate_record_names_separate() {
        let first = record_finding(
            "/checkout/src/lib.rs",
            "generated::State",
            CandidateKind::FieldGroup,
            "left",
            20,
        );
        let mut second = record_finding(
            "/checkout/src/lib.rs",
            "generated::State",
            CandidateKind::FieldGroup,
            "left",
            40,
        );
        second
            .layout_context
            .as_mut()
            .expect("layout")
            .declaration_line = 30;

        let clustered = cluster_findings(Path::new("/checkout"), vec![first, second]);
        assert_eq!(clustered.findings.len(), 2);
        assert_ne!(
            clustered.findings[0].finding_group_id,
            clustered.findings[1].finding_group_id
        );
    }

    #[test]
    fn canonical_storage_identity_merges_cross_file_access_occurrences() {
        let mut declaration = record_finding(
            "/checkout/src/pq.c",
            "pqEntries",
            CandidateKind::IndexedWrites,
            "pqEntries",
            15,
        );
        let mut caller = record_finding(
            "/checkout/src/packet.c",
            "pqEntries",
            CandidateKind::IndexedWrites,
            "pqEntries",
            313,
        );
        let identity = "/checkout/src/pq.c::pqEntries@15".to_string();
        declaration.storage_identity = Some(identity.clone());
        caller.storage_identity = Some(identity);

        let clustered = cluster_findings(Path::new("/checkout"), vec![declaration, caller]);

        assert_eq!(clustered.occurrence_count, 2);
        assert_eq!(clustered.findings.len(), 1);
        assert_eq!(clustered.findings[0].finding_occurrence_count, 2);
        assert_eq!(clustered.findings[0].usage_locations.len(), 2);
    }

    #[test]
    fn bound_storage_id_is_stable_across_checkouts_and_input_order() {
        let make = |root: &str, file: &str, line| {
            let mut finding = record_finding(
                &format!("{root}/{file}"),
                "slots",
                CandidateKind::IndexedWrites,
                "slots",
                line,
            );
            finding.struct_name = None;
            finding.layout_context = None;
            finding.storage_identity = Some(format!("{root}/storage.cpp::slots@7"));
            finding
        };
        let a = cluster_findings(
            Path::new("/first"),
            vec![make("/first", "a.cpp", 12), make("/first", "b.cpp", 34)],
        );
        let b = cluster_findings(
            Path::new("/second"),
            vec![make("/second", "b.cpp", 34), make("/second", "a.cpp", 12)],
        );
        assert_eq!(a.findings.len(), 1);
        assert_eq!(
            a.findings[0].finding_group_id,
            b.findings[0].finding_group_id
        );
        assert_eq!(a.findings[0].finding_hash, b.findings[0].finding_hash);
        let again = cluster_findings(Path::new("/first"), a.findings.clone());
        assert_eq!(
            again.findings[0].finding_group_id,
            a.findings[0].finding_group_id
        );
        assert_eq!(again.occurrence_count, 2);
    }

    #[test]
    fn cpp_padding_components_are_not_merged_back_into_one_root_cause() {
        let mut left = record_finding(
            "/checkout/src/state.h",
            "State",
            CandidateKind::MixedFields,
            "left",
            20,
        );
        let mut right = record_finding(
            "/checkout/src/state.h",
            "State",
            CandidateKind::MixedFields,
            "right",
            30,
        );
        for finding in [&mut left, &mut right] {
            let layout = finding.layout_context.as_mut().expect("layout");
            layout.language = "cpp".to_string();
            layout.repr_rust = false;
            layout.has_cache_padded = true;
            layout.manual_padding_fields = vec!["padding".to_string()];
            layout.fields = vec![
                test_layout_field("left", false),
                test_layout_field("padding", true),
                test_layout_field("right", false),
            ];
        }

        let clustered = cluster_findings(Path::new("/checkout"), vec![left, right]);
        assert_eq!(clustered.findings.len(), 2);
        assert_ne!(
            clustered.findings[0].finding_group_id,
            clustered.findings[1].finding_group_id
        );
    }

    fn test_layout_field(name: &str, is_manual_padding: bool) -> LayoutFieldContext {
        LayoutFieldContext {
            name: name.to_string(),
            ty: "int".to_string(),
            estimated_size: Some(4),
            offset: None,
            range: None,
            cache_line: None,
            cache_line_range: None,
            is_atomic: false,
            is_hot_scalar: false,
            is_hot_sync: false,
            is_cache_padded: false,
            is_manual_padding,
            is_indirect: false,
        }
    }
}
