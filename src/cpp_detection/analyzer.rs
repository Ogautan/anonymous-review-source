use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::root_cause::cluster_findings;
use crate::types::{
    AblationComponent, AnalysisDiagnostic, AnalysisOptions, CandidateKind, DETECTOR_VERSION,
    Finding, ItemVisibility, REPORT_SCHEMA_VERSION, Report, ReportSummary, RiskCategory,
};

use super::compiler_sidecar::{apply_compiler_facts, run_compiler_sidecar};
use super::evidence::{
    collect_atomic_alias_array_candidates_with_commands, collect_cpp_evidence_with_commands,
    collect_indexed_write_candidates_with_commands,
    collect_static_hot_state_candidates_with_commands,
};
use super::layout::{ablate_protection_evidence, collect_cpp_structs};
use super::parser::parse_cpp_files;
use super::rules::apply_cpp_rules;
use super::types::{CppAccessKind, CppEvidenceKind, CppEvidenceSet};
use super::workspace;

const MAX_PARSE_DIAGNOSTIC_EXAMPLES: usize = 20;

pub fn looks_like_cpp_project(root: &Path) -> bool {
    workspace::looks_like_cpp_project(root)
}

pub fn analyze_cpp_path_with_options(root: &Path, options: &AnalysisOptions) -> Report {
    let project = workspace::discover_cpp_project(root);
    let project_name = project.name;
    let mut diagnostics = project.diagnostics;
    let compile_commands = project.compile_commands;
    let mut parsed_files = parse_cpp_files(project.files);
    super::parser::apply_source_dialects(&mut parsed_files, &compile_commands);
    let parser_fallbacks = parsed_files
        .iter()
        .filter(|file| file.tree.is_none())
        .count();
    if parser_fallbacks > 0 {
        diagnostics.push(AnalysisDiagnostic::warning(
            "parse",
            None::<String>,
            format!(
                "tree-sitter parsing was unavailable for {parser_fallbacks} file(s); regex fallback was used"
            ),
        ));
    }
    let syntax_error_files = parsed_files
        .iter()
        .filter(|file| {
            file.tree
                .as_ref()
                .is_some_and(|tree| tree.root_node().has_error())
        })
        .collect::<Vec<_>>();
    if !syntax_error_files.is_empty() {
        diagnostics.push(AnalysisDiagnostic::warning(
            "parse",
            None::<String>,
            format!(
                "tree-sitter recovered from C/C++ syntax errors in {} file(s); showing at most {} examples",
                syntax_error_files.len(),
                MAX_PARSE_DIAGNOSTIC_EXAMPLES.min(syntax_error_files.len())
            ),
        ));
        for file in syntax_error_files
            .into_iter()
            .take(MAX_PARSE_DIAGNOSTIC_EXAMPLES)
        {
            diagnostics.push(AnalysisDiagnostic::warning(
                "parse",
                Some(file.path.clone()),
                "tree-sitter recovered from one or more C/C++ syntax errors",
            ));
        }
    }
    let mut structs = collect_cpp_structs(&parsed_files, &project_name, options.cache_line_size);
    super::layout_macros::apply(&parsed_files, &mut structs, &compile_commands);
    let mut evidence_map =
        collect_cpp_evidence_with_commands(&parsed_files, &structs, &compile_commands);
    if let Some(sidecar) = &options.cpp_semantic_sidecar {
        match run_compiler_sidecar(
            sidecar,
            root,
            options.cache_line_size,
            &compile_commands,
            &structs,
            &evidence_map,
        ) {
            Ok(facts) => {
                let coverage = facts.coverage.clone();
                let (layout_count, access_count) = apply_compiler_facts(
                    &facts,
                    &mut structs,
                    &mut evidence_map,
                    options.cache_line_size,
                );
                if !coverage.command_mode.is_empty() || coverage.commands_selected > 0 {
                    diagnostics.push(AnalysisDiagnostic::warning(
                        "cpp_compiler_semantics",
                        Some(sidecar.to_string_lossy()),
                        format!(
                            "semantic coverage: mode={}, clean_tus={}/{}, confirmed_accesses={}/{}, functions={}, call_edges={}, cfg_files={}, cfg_blocks={}",
                            coverage.command_mode,
                            coverage.translation_units_clean,
                            coverage.translation_units_attempted,
                            coverage.confirmed_accesses,
                            coverage.candidate_accesses,
                            coverage.functions,
                            coverage.call_edges,
                            coverage.cfg_files,
                            coverage.cfg_blocks,
                        ),
                    ));
                }
                for message in facts
                    .diagnostics
                    .into_iter()
                    .take(MAX_PARSE_DIAGNOSTIC_EXAMPLES)
                {
                    diagnostics.push(AnalysisDiagnostic::warning(
                        "cpp_compiler_semantics",
                        None::<String>,
                        message,
                    ));
                }
                if layout_count == 0 && access_count == 0 {
                    diagnostics.push(AnalysisDiagnostic::warning(
                        "cpp_compiler_semantics",
                        Some(sidecar.to_string_lossy()),
                        "compiler sidecar returned no applicable exact layout or access facts",
                    ));
                }
            }
            Err(error) => diagnostics.push(AnalysisDiagnostic::warning(
                "cpp_compiler_semantics",
                Some(sidecar.to_string_lossy()),
                error,
            )),
        }
    }
    if options.ablated(AblationComponent::Protection) {
        for record in &mut structs {
            ablate_protection_evidence(record, options.cache_line_size);
        }
    }
    if options.ablated(AblationComponent::Hotness) {
        for record in &mut structs {
            for field in &mut record.fields {
                field.is_hot_scalar = false;
            }
            record.hot_scalar_fields.clear();
        }
    }
    if options.ablated(AblationComponent::Api) {
        for record in &mut structs {
            record.visibility = ItemVisibility::Private;
            record.public_fields.clear();
            record.public_methods.clear();
        }
    }
    if options.ablated(AblationComponent::Layout) {
        structs.clear();
    }
    apply_evidence_ablation(&mut evidence_map, options);
    let indexed_writes = if options.ablated(AblationComponent::Write)
        || options.ablated(AblationComponent::MayParallel)
    {
        Vec::new()
    } else {
        collect_indexed_write_candidates_with_commands(
            &parsed_files,
            &structs,
            options.cache_line_size,
            &compile_commands,
        )
    };
    let atomic_alias_arrays =
        collect_atomic_alias_array_candidates_with_commands(&parsed_files, &compile_commands);
    let static_hot_state = if options.ablated(AblationComponent::Hotness) {
        Vec::new()
    } else {
        collect_static_hot_state_candidates_with_commands(
            &parsed_files,
            &structs,
            options.cache_line_size,
            &compile_commands,
        )
    };

    let mut findings = apply_cpp_rules(
        &structs,
        &evidence_map,
        &indexed_writes,
        &atomic_alias_arrays,
        &static_hot_state,
        options,
    );

    findings.retain(|finding| options.enabled(finding.rule_id));

    super::evidence::bind_declared_storage(&parsed_files, &mut findings);

    let mut seen_hashes: HashSet<String> = HashSet::new();
    findings.retain(|finding| {
        seen_hashes.insert(format!("{}:{}", finding.finding_hash, finding.category))
    });
    // A report group is a presentation unit, not a source of new evidence.
    // Validate individual occurrences before their fields, rules and accesses
    // are unioned. Keep the broad group population for speculative accounting;
    // rejected occurrences in a surviving group are not extra risk groups.
    let broad_groups = if options.cpp_include_speculative {
        Vec::new()
    } else {
        crate::root_cause::assign_group_ids(root, &mut findings);
        let broad = cluster_findings(root, findings.clone());
        super::reportability::retain_reportable(&mut findings, &structs, &evidence_map);
        broad.findings
    };
    let retained_broad_groups = findings
        .iter()
        .map(|finding| finding.finding_group_id.clone())
        .collect::<HashSet<_>>();
    let clustered = cluster_findings(root, findings);
    let mut findings = clustered.findings;
    for finding in &mut findings {
        // Each incoming occurrence already has a checked witness. Preserve
        // their location union in the grouped presentation without borrowing
        // evidence to admit further occurrences after the merge.
        if !options.cpp_include_speculative
            && let Some(record) = super::pattern::matching_record_index(finding, &structs)
                .map(|index| &structs[index])
            && let Some(pattern) = &mut finding.static_pattern
            && pattern.colocation_pattern == crate::types::ColocationPattern::SameObjectFields
        {
            pattern.witness_locations = finding
                .field_list
                .iter()
                .map(|field| format!("{}.{}", record.name, field))
                .collect();
        }
    }

    if let Some(ref filter) = options.category_filter {
        findings.retain(|finding| &finding.category == filter);
    }

    let speculative_candidates = broad_groups
        .iter()
        .filter(|finding| {
            options
                .category_filter
                .as_ref()
                .is_none_or(|category| finding.category == *category)
                && !retained_broad_groups.contains(&finding.finding_group_id)
        })
        .count();

    sort_findings(&mut findings);
    let candidate_findings = findings.len();
    let finding_occurrence_count = findings
        .iter()
        .map(|finding| finding.finding_occurrence_count)
        .sum();
    if let Some(limit) = options.max_findings {
        retain_ranked_findings(&mut findings, limit);
    }
    let mut summary = summarize(&findings, candidate_findings, finding_occurrence_count);
    summary.cpp_speculative_candidates = speculative_candidates;
    let truncated_facts = evidence_map
        .iter()
        .map(|evidence| evidence.truncated_items + evidence.truncated_api_items)
        .sum();
    if truncated_facts > 0 {
        diagnostics.push(AnalysisDiagnostic::warning(
            "evidence",
            None::<String>,
            format!("bounded C++ evidence collection dropped {truncated_facts} fact(s)"),
        ));
    }
    if evidence_map
        .iter()
        .any(|facts| facts.omitted_access_roles_overflow)
    {
        diagnostics.push(AnalysisDiagnostic::warning(
            "evidence",
            None::<String>,
            "bounded C++ omitted-access membership summary overflowed; affected same-object callable partitions remain speculative",
        ));
    }

    Report {
        schema_version: REPORT_SCHEMA_VERSION,
        detector_version: DETECTOR_VERSION,
        scanned_files: parsed_files.len(),
        scanned_crates: vec![project_name],
        enabled_rules: options.enabled_rule_names(),
        ablated_components: options.ablated_component_names(),
        cache_line_size: options.cache_line_size,
        analysis_incomplete: !diagnostics.is_empty(),
        truncated_facts,
        diagnostics,
        summary,
        findings,
    }
}

fn apply_evidence_ablation(evidence_by_record: &mut [CppEvidenceSet], options: &AnalysisOptions) {
    for evidence in evidence_by_record {
        if options.ablated(AblationComponent::Api) {
            evidence.api_items.clear();
        }
        evidence.items.retain(|item| {
            if options.ablated(AblationComponent::Write)
                && matches!(
                    item.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                )
            {
                return false;
            }
            if options.ablated(AblationComponent::MayParallel)
                && matches!(
                    item.kind,
                    CppEvidenceKind::ThreadSpawn
                        | CppEvidenceKind::OpenMp
                        | CppEvidenceKind::ParallelLibrary
                        | CppEvidenceKind::SharedOwnership
                        | CppEvidenceKind::ConcurrentFieldAccess
                        | CppEvidenceKind::CompilerSemanticAccess
                )
            {
                return false;
            }
            if options.ablated(AblationComponent::Hotness)
                && item.kind == CppEvidenceKind::LoopHotness
            {
                return false;
            }
            if options.ablated(AblationComponent::Protection)
                && item.kind == CppEvidenceKind::LockProtected
            {
                return false;
            }
            true
        });
        for item in &mut evidence.items {
            if options.ablated(AblationComponent::MayParallel) {
                item.in_concurrent_context = false;
            }
            if options.ablated(AblationComponent::Hotness) {
                item.hotness_score = 0.0;
            }
        }
    }
}

fn sort_findings(findings: &mut [Finding]) {
    findings.sort_by(|left, right| {
        finding_actionability_score(right)
            .cmp(&finding_actionability_score(left))
            .then_with(|| left.file.cmp(&right.file))
            .then_with(|| left.line.cmp(&right.line))
    });
}

fn finding_actionability_score(finding: &Finding) -> u32 {
    let category_score = match finding.category {
        RiskCategory::HotInProject => 3_000,
        RiskCategory::ApiUsageLatent => 1_800,
        RiskCategory::ColdOrConditional => 800,
    };
    let rule_score = match finding.candidate_kind {
        CandidateKind::StaticData
        | CandidateKind::IndexedWrites
        | CandidateKind::AtomicArray
        | CandidateKind::SiblingArrays => 700,
        CandidateKind::ContainerElements
        | CandidateKind::ObjectInstances
        | CandidateKind::SeparateAllocations => 500,
        CandidateKind::MixedFields => 350,
        CandidateKind::FieldGroup => 300,
        CandidateKind::WriterNeighbor => 250,
    };
    let concurrent_writes: HashSet<_> = finding
        .access_evidence
        .iter()
        .filter(|item| {
            item.in_concurrent_context
                && matches!(
                    item.access_kind.as_deref(),
                    Some("write" | "read_modify_write")
                )
        })
        .filter_map(|item| item.field_name.as_deref())
        .collect();
    let strong_indexed_write_score = u32::from(
        finding.candidate_kind == CandidateKind::IndexedWrites
            && finding.access_evidence.iter().any(|evidence| {
                matches!(
                    evidence.evidence_kind.as_str(),
                    "direct_worker_partition" | "api_index_partition"
                )
            }),
    ) * 1_800;
    category_score
        + rule_score
        + strong_indexed_write_score
        + concurrent_writes.len().min(8) as u32 * 200
        + finding.field_list.len().min(12) as u32 * 20
        + finding.access_evidence.len().min(24) as u32 * 10
        + finding.related_candidate_kinds.len().min(8) as u32 * 20
        + (finding.confidence.clamp(0.0, 1.0) * 200.0).round() as u32
}

fn retain_ranked_findings(findings: &mut Vec<Finding>, limit: usize) {
    if findings.len() <= limit {
        return;
    }
    if limit == 0 {
        findings.clear();
        return;
    }

    let mut selected = HashSet::new();
    let mut selected_per_rule: HashMap<CandidateKind, usize> = HashMap::new();
    // Keep 90% of the queue as a true global evidence ranking. Use the final
    // 10% only to make sure a lower-volume rule is represented; reserving a
    // large quota up front displaced high-scoring findings in huge projects.
    let global_quota = (limit * 9 / 10).max(1).min(limit);
    for (index, finding) in findings.iter().take(global_quota).enumerate() {
        selected.insert(index);
        *selected_per_rule.entry(finding.candidate_kind).or_default() += 1;
    }
    let per_rule_quota = ((limit - global_quota) / 10).max(1);
    for (index, finding) in findings.iter().enumerate() {
        if selected.len() >= limit {
            break;
        }
        let count = selected_per_rule.entry(finding.candidate_kind).or_default();
        if *count < per_rule_quota {
            selected.insert(index);
            *count += 1;
        }
    }
    for index in 0..findings.len() {
        if selected.len() >= limit {
            break;
        }
        selected.insert(index);
    }

    let mut index = 0usize;
    findings.retain(|_| {
        let keep = selected.contains(&index);
        index += 1;
        keep
    });
}

fn summarize(
    findings: &[Finding],
    candidate_findings: usize,
    finding_occurrence_count: usize,
) -> ReportSummary {
    ReportSummary {
        hot_in_project: findings
            .iter()
            .filter(|finding| finding.category == RiskCategory::HotInProject)
            .count(),
        api_usage_latent: findings
            .iter()
            .filter(|finding| finding.category == RiskCategory::ApiUsageLatent)
            .count(),
        cold_or_conditional: findings
            .iter()
            .filter(|finding| finding.category == RiskCategory::ColdOrConditional)
            .count(),
        candidate_findings,
        suppressed_candidates: candidate_findings.saturating_sub(findings.len()),
        cpp_speculative_candidates: 0,
        finding_occurrence_count,
        finding_group_count: candidate_findings,
    }
}
