use std::collections::HashSet;
use std::path::Path;

use crate::api_usage::collect_api_usage_evidence;
use crate::concurrency_evidence::collect_concurrency_evidence_with_stats;
use crate::module_visibility::apply_external_reachability;
use crate::root_cause::cluster_findings;
use crate::rules::{
    apply_file_rules_with_accessors, apply_struct_rules, collect_indexed_accessors,
    collect_storage_topologies,
};
use crate::rustc_layout::collect_rustc_layouts;
use crate::struct_layout::{collect_structs_from_file, enrich_structs_with_type_registry};
use crate::types::{
    AblationComponent, AnalysisDiagnostic, AnalysisOptions, ConcurrencyEvidenceSet,
    DETECTOR_VERSION, EvidenceKind, Finding, ParsedFile, REPORT_SCHEMA_VERSION, Report,
    ReportSummary, RiskCategory, StructInfo,
};
use crate::workspace::{
    canonical_path, collect_rs_files, discover_crates, module_path_for_rs_file,
};

/// Main entry point: two-pass analysis with cross-file concurrency evidence.
pub fn analyze_path_with_options(root: &Path, options: &AnalysisOptions) -> Report {
    if !root.exists() {
        return empty_report(
            options,
            vec![AnalysisDiagnostic::fatal(
                "input",
                Some(root.to_string_lossy()),
                "analysis path does not exist",
            )],
        );
    }

    let mut diagnostics = Vec::new();
    let cargo_manifest = root.join("Cargo.toml");
    if cargo_manifest.is_file() {
        match std::fs::read_to_string(&cargo_manifest) {
            Ok(source) => {
                if let Err(error) = source.parse::<toml::Value>() {
                    diagnostics.push(AnalysisDiagnostic::warning(
                        "workspace",
                        Some(cargo_manifest.to_string_lossy()),
                        format!("failed to parse Cargo manifest: {error}"),
                    ));
                }
            }
            Err(error) => diagnostics.push(AnalysisDiagnostic::warning(
                "workspace",
                Some(cargo_manifest.to_string_lossy()),
                format!("failed to read Cargo manifest: {error}"),
            )),
        }
    }
    let crates = discover_crates(root);
    let crate_names: Vec<String> = crates.iter().map(|c| c.name.clone()).collect();

    // Deduplicate files across crates (a file can belong to overlapping crate roots).
    // Keep the first (most specific) crate association for each canonical path.
    let mut seen_paths = HashSet::new();
    let mut parsed_files: Vec<ParsedFile> = Vec::new();

    for ci in &crates {
        for path in collect_rs_files(&ci.root) {
            let canonical_path = canonical_path(&path);
            if !seen_paths.insert(canonical_path.clone()) {
                continue;
            }
            let source = match std::fs::read_to_string(&path) {
                Ok(s) => s,
                Err(error) => {
                    diagnostics.push(AnalysisDiagnostic::warning(
                        "read",
                        Some(path.to_string_lossy()),
                        format!("failed to read Rust source: {error}"),
                    ));
                    continue;
                }
            };
            let ast = match syn::parse_file(&source) {
                Ok(a) => a,
                Err(error) => {
                    diagnostics.push(AnalysisDiagnostic::warning(
                        "parse",
                        Some(path.to_string_lossy()),
                        format!("failed to parse Rust source: {error}"),
                    ));
                    continue;
                }
            };
            parsed_files.push(ParsedFile {
                path: canonical_path.to_string_lossy().to_string(),
                module_path: module_path_for_rs_file(&ci.root, &path),
                source,
                ast,
                crate_name: Some(ci.name.clone()),
            });
        }
    }

    let scanned_files = parsed_files.len();
    if scanned_files == 0 {
        diagnostics.push(AnalysisDiagnostic::fatal(
            "discovery",
            Some(root.to_string_lossy()),
            "no analyzable Rust source files were found",
        ));
    }

    // --- Pass 1: collect struct layouts + concurrency evidence ---

    let mut all_structs: Vec<StructInfo> = Vec::new();
    for pf in &parsed_files {
        all_structs.extend(collect_structs_from_file(pf, options.cache_line_size));
    }

    apply_external_reachability(&parsed_files, &mut all_structs);

    enrich_structs_with_type_registry(&mut all_structs, options.cache_line_size);

    if options.use_rustc_layout {
        match collect_rustc_layouts(root) {
            Ok(layouts) => crate::struct_layout::apply_rustc_layouts(
                &mut all_structs,
                &layouts,
                options.cache_line_size,
            ),
            Err(err) => diagnostics.push(AnalysisDiagnostic::warning(
                "rustc_layout",
                Some(root.to_string_lossy()),
                err,
            )),
        }
    }

    if options.ablated(AblationComponent::Protection) {
        for si in &mut all_structs {
            crate::struct_layout::ablate_protection_evidence(si, options.cache_line_size);
        }
    }
    if options.ablated(AblationComponent::Hotness) {
        for si in &mut all_structs {
            for field in &mut si.fields {
                field.is_hot_scalar = false;
            }
            si.hot_scalar_fields.clear();
        }
    }
    if options.ablated(AblationComponent::Layout) {
        // Remove the record-layout channel while retaining independent
        // file-level rules (for example, thread-indexed writes).  This is more
        // interpretable than pretending all fields share one cache line.
        all_structs.clear();
    }

    let evidence_collection = collect_concurrency_evidence_with_stats(
        &parsed_files,
        &all_structs,
        options.use_interprocedural_evidence,
    );
    let truncated_facts = evidence_collection.truncated_facts;
    let mut evidence_map = evidence_collection.evidence_map;
    if truncated_facts > 0 {
        diagnostics.push(AnalysisDiagnostic::warning(
            "evidence",
            None::<String>,
            format!("bounded Rust evidence analysis dropped {truncated_facts} fact(s)"),
        ));
    }
    apply_evidence_ablation(&mut evidence_map, options);
    let api_usage_map = if options.ablated(AblationComponent::Api) {
        Default::default()
    } else {
        collect_api_usage_evidence(&parsed_files, &all_structs)
    };
    let storage_topologies = collect_storage_topologies(&parsed_files, &all_structs);

    // --- Pass 2: apply rules with evidence cross-reference ---

    let mut findings: Vec<Finding> = Vec::new();

    findings.extend(apply_struct_rules(
        &all_structs,
        &evidence_map,
        &api_usage_map,
        &storage_topologies,
        options,
    ));

    let indexed_accessors = collect_indexed_accessors(&parsed_files);
    for pf in &parsed_files {
        findings.extend(apply_file_rules_with_accessors(
            &pf.source,
            &pf.path,
            &pf.ast,
            pf.crate_name.as_deref(),
            options,
            &indexed_accessors,
        ));
    }
    findings.extend(crate::rust_statics::collect_findings(
        &parsed_files,
        &all_structs,
        options,
    ));

    findings.retain(|finding| options.enabled(finding.rule_id));

    crate::rust_storage::bind_findings(&parsed_files, &all_structs, &mut findings);

    // Remove exact scan duplicates first, then fold field/rule/access
    // occurrences into reviewable root-cause groups.
    let mut seen_hashes = HashSet::new();
    findings.retain(|finding| {
        seen_hashes.insert((
            finding.finding_hash.clone(),
            finding.category.to_string(),
            finding.storage_identity.clone(),
        ))
    });
    let clustered = cluster_findings(root, findings);
    let unfiltered_occurrence_count = clustered.occurrence_count;
    let mut findings = clustered.findings;

    if let Some(ref filter) = options.category_filter {
        findings.retain(|f| &f.category == filter);
    }

    let finding_occurrence_count = if options.category_filter.is_none() {
        unfiltered_occurrence_count
    } else {
        findings
            .iter()
            .map(|finding| finding.finding_occurrence_count)
            .sum()
    };
    let finding_group_count = findings.len();

    findings.sort_by_key(|f| match f.category {
        RiskCategory::HotInProject => 0,
        RiskCategory::ApiUsageLatent => 1,
        RiskCategory::ColdOrConditional => 2,
    });

    let summary = ReportSummary {
        hot_in_project: findings
            .iter()
            .filter(|f| f.category == RiskCategory::HotInProject)
            .count(),
        api_usage_latent: findings
            .iter()
            .filter(|f| f.category == RiskCategory::ApiUsageLatent)
            .count(),
        cold_or_conditional: findings
            .iter()
            .filter(|f| f.category == RiskCategory::ColdOrConditional)
            .count(),
        candidate_findings: findings.len(),
        suppressed_candidates: 0,
        cpp_speculative_candidates: 0,
        finding_occurrence_count,
        finding_group_count,
    };

    Report {
        schema_version: REPORT_SCHEMA_VERSION,
        detector_version: DETECTOR_VERSION,
        scanned_files,
        scanned_crates: crate_names,
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

fn empty_report(options: &AnalysisOptions, diagnostics: Vec<AnalysisDiagnostic>) -> Report {
    Report {
        schema_version: REPORT_SCHEMA_VERSION,
        detector_version: DETECTOR_VERSION,
        scanned_files: 0,
        scanned_crates: Vec::new(),
        enabled_rules: options.enabled_rule_names(),
        ablated_components: options.ablated_component_names(),
        cache_line_size: options.cache_line_size,
        analysis_incomplete: true,
        truncated_facts: 0,
        diagnostics,
        summary: ReportSummary {
            hot_in_project: 0,
            api_usage_latent: 0,
            cold_or_conditional: 0,
            candidate_findings: 0,
            suppressed_candidates: 0,
            cpp_speculative_candidates: 0,
            finding_occurrence_count: 0,
            finding_group_count: 0,
        },
        findings: Vec::new(),
    }
}

fn apply_evidence_ablation(
    evidence_map: &mut std::collections::HashMap<crate::types::StructKey, ConcurrencyEvidenceSet>,
    options: &AnalysisOptions,
) {
    for evidence in evidence_map.values_mut() {
        evidence.evidence.retain(|item| {
            if options.ablated(AblationComponent::Write)
                && matches!(
                    item.access_kind,
                    Some(
                        crate::types::AtomicAccessKind::Write
                            | crate::types::AtomicAccessKind::ReadModifyWrite
                    )
                )
            {
                return false;
            }
            if options.ablated(AblationComponent::MayParallel)
                && matches!(
                    item.kind,
                    EvidenceKind::ArcWrapped
                        | EvidenceKind::UsedInSpawn
                        | EvidenceKind::UsedInParallelIter
                        | EvidenceKind::FieldAccessInConcurrentContext
                )
            {
                return false;
            }
            if options.ablated(AblationComponent::Protection)
                && matches!(
                    item.kind,
                    EvidenceKind::MutexWrapped | EvidenceKind::RwLockWrapped
                )
            {
                return false;
            }
            true
        });

        for item in &mut evidence.evidence {
            if options.ablated(AblationComponent::MayParallel) {
                item.in_concurrent_context = false;
            }
            if options.ablated(AblationComponent::Hotness) {
                item.hotness_score = 0.0;
                item.loop_context = None;
            }
        }
    }
}
