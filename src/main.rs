use clap::{Parser, ValueEnum};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use false_sharing_detector::analyzer::analyze_path_with_options;
use false_sharing_detector::cpp_detection::{
    analyze_cpp_path_with_options, looks_like_cpp_project,
};
use false_sharing_detector::types::{AblationComponent, AnalysisOptions, RiskCategory, RuleId};
use false_sharing_detector::types::{
    DETECTOR_VERSION, REPORT_SCHEMA_VERSION, Report, ReportSummary,
};

#[derive(Debug, Parser)]
#[command(
    name = "false-sharing-detector",
    about = "Detect potential false-sharing patterns in Rust and C++ source"
)]
struct Cli {
    /// Source path: workspace root, crate directory, or source directory
    #[arg(default_value = ".")]
    path: PathBuf,

    /// Enable only the specified storage-relation rules
    #[arg(long = "rule", value_enum, value_delimiter = ',')]
    rules: Vec<RuleId>,

    /// Write the analysis report as JSON
    #[arg(long)]
    json: bool,

    /// Source language: auto, rust, or cpp
    #[arg(long, value_enum, default_value_t = Language::Auto)]
    language: Language,

    /// Return only findings in the specified risk category
    #[arg(long, value_parser = parse_category)]
    category: Option<RiskCategory>,

    /// Effective cache-line/interference size in bytes: 32, 64, or 128
    #[arg(long, default_value_t = 64, value_parser = parse_cache_line_size)]
    cache_line_size: usize,

    /// C++: return all reportable findings; the default limit is 200
    #[arg(long)]
    all_candidates: bool,

    /// C++: include speculative candidates with incomplete concurrency or storage evidence
    #[arg(long)]
    cpp_include_speculative: bool,

    /// C++: compiler semantic sidecar executable (versioned JSON over stdin/stdout)
    #[arg(long)]
    cpp_semantic_sidecar: Option<PathBuf>,

    /// Obtain Rust field layouts using nightly rustc -Zprint-type-sizes
    #[arg(long)]
    rustc_layout: bool,

    /// Disable bounded interprocedural summary propagation in Rust
    #[arg(long)]
    no_interprocedural: bool,

    /// Disable the specified analysis components for ablation experiments
    #[arg(long = "ablate", value_enum, value_delimiter = ',')]
    ablations: Vec<AblationComponent>,
}

#[derive(Debug, Clone, Copy, ValueEnum)]
#[clap(rename_all = "snake_case")]
enum Language {
    Auto,
    Rust,
    Cpp,
}

#[derive(Debug, Clone, Copy)]
enum SelectedLanguage {
    Rust,
    Cpp,
    Mixed,
}

fn parse_category(s: &str) -> Result<RiskCategory, String> {
    match s.to_lowercase().as_str() {
        "hot_in_project" => Ok(RiskCategory::HotInProject),
        "api_usage_latent" => Ok(RiskCategory::ApiUsageLatent),
        "cold_or_conditional" => Ok(RiskCategory::ColdOrConditional),
        _ => Err(format!(
            "unknown category '{s}', expected hot_in_project|api_usage_latent|cold_or_conditional"
        )),
    }
}

fn parse_cache_line_size(s: &str) -> Result<usize, String> {
    match s.parse::<usize>() {
        Ok(size @ (32 | 64 | 128)) => Ok(size),
        _ => Err(format!(
            "unsupported cache-line size '{s}', expected 32|64|128"
        )),
    }
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let selected_language = resolve_language(&cli.path, cli.language);
    let mut options = analysis_options_for_language(selected_language, &cli.rules);
    options.category_filter = cli.category;
    options.cache_line_size = cli.cache_line_size;
    if matches!(
        selected_language,
        SelectedLanguage::Cpp | SelectedLanguage::Mixed
    ) && !cli.all_candidates
    {
        options.max_findings = Some(200);
    }
    options.use_rustc_layout =
        cli.rustc_layout && !matches!(selected_language, SelectedLanguage::Cpp);
    options.use_interprocedural_evidence =
        !cli.no_interprocedural && !matches!(selected_language, SelectedLanguage::Cpp);
    options.cpp_semantic_sidecar = cli.cpp_semantic_sidecar;
    options.cpp_include_speculative = cli.cpp_include_speculative;
    options.ablated_components = cli.ablations.into_iter().collect();

    let report = match selected_language {
        SelectedLanguage::Cpp => analyze_cpp_path_with_options(&cli.path, &options),
        SelectedLanguage::Rust => analyze_path_with_options(&cli.path, &options),
        SelectedLanguage::Mixed => merge_reports(
            analyze_path_with_options(&cli.path, &options),
            analyze_cpp_path_with_options(&cli.path, &options),
        ),
    };
    let exit_code = if report.has_fatal_diagnostics() {
        ExitCode::from(2)
    } else {
        ExitCode::SUCCESS
    };

    if cli.json {
        match serde_json::to_string_pretty(&report) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("Cannot serialize the analysis report: {error}");
                return ExitCode::from(1);
            }
        }
        return exit_code;
    }

    for diagnostic in &report.diagnostics {
        let file = diagnostic
            .file
            .as_deref()
            .map(|file| format!(" ({file})"))
            .unwrap_or_default();
        eprintln!(
            "Analysis diagnostic [{:?}/{}]{}: {}",
            diagnostic.severity, diagnostic.stage, file, diagnostic.message
        );
    }

    // Human-readable output
    println!("Scanned files: {}", report.scanned_files);
    if !report.scanned_crates.is_empty() {
        println!("Scanned crates: {}", report.scanned_crates.join(", "));
    }
    println!("Enabled rules: {}", report.enabled_rules.join(", "));
    println!("Effective cache-line/interference size: {} B", report.cache_line_size);
    println!(
        "Findings: {} hot_in_project, {} api_usage_latent, {} cold_or_conditional",
        report.summary.hot_in_project,
        report.summary.api_usage_latent,
        report.summary.cold_or_conditional
    );
    println!(
        "Root-cause grouping: {} occurrences -> {} finding groups",
        report.summary.finding_occurrence_count, report.summary.finding_group_count
    );
    if report.summary.suppressed_candidates > 0 {
        println!(
            "Showing {} / {} candidates; {} candidates omitted (use --all-candidates)",
            report.findings.len(),
            report.summary.candidate_findings,
            report.summary.suppressed_candidates
        );
    }
    if report.summary.cpp_speculative_candidates > 0 {
        println!(
            "{} additional speculative candidates lack reportable evidence (use --cpp-include-speculative)",
            report.summary.cpp_speculative_candidates
        );
    }
    println!();

    if report.findings.is_empty() {
        println!("No reportable false-sharing risk patterns found.");
        println!("Static analysis may miss risks; runtime perf/c2c measurements or profiling can provide additional evidence.");
        return exit_code;
    }

    let mut current_cat = None;
    for (idx, f) in report.findings.iter().enumerate() {
        if current_cat.as_ref() != Some(&f.category) {
            current_cat = Some(f.category);
            println!("=== {} ===", f.category);
        }

        print!(
            "[{}] {} ({:?})\n  Category: {}\n  Location: {}:{}\n",
            idx + 1,
            f.title,
            f.severity,
            f.category,
            f.file,
            f.line,
        );
        if let Some(ref cn) = f.crate_name {
            println!("  crate: {cn}");
        }
        if let Some(ref symbol) = f.symbol {
            println!("  Symbol: {symbol}");
        }
        println!(
            "  Root-cause group: {} ({} occurrences)",
            f.finding_group_id, f.finding_occurrence_count
        );
        if !f.related_candidate_kinds.is_empty() {
            println!(
                "  Additional candidate provenance: {}",
                f.related_candidate_kinds
                    .iter()
                    .map(|rule| rule.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
        println!("  Snippet: {}", f.snippet);
        println!("  Suggestion: {}", f.suggestion);
        println!("  Confidence: {:.0}%", f.confidence * 100.0);
        if !f.risk_factors.is_empty() {
            println!("  Risk factors:");
            for factor in &f.risk_factors {
                println!("    - {factor}");
            }
        }
        if !f.concurrency_evidence.is_empty() {
            println!("  Concurrency evidence:");
            for e in &f.concurrency_evidence {
                println!("    - {e}");
            }
        }
        if !f.usage_locations.is_empty() {
            println!("  Usage locations ({}):", f.usage_locations.len());
            // Show up to 10 usage locations
            for (i, loc) in f.usage_locations.iter().take(10).enumerate() {
                println!(
                    "    [{}] {}:{} - {}",
                    i + 1,
                    loc.file,
                    loc.line,
                    loc.description
                );
            }
            if f.usage_locations.len() > 10 {
                println!("    ... {} additional usage locations", f.usage_locations.len() - 10);
            }
        }
        println!();
    }
    exit_code
}

fn resolve_language(path: &Path, requested: Language) -> SelectedLanguage {
    match requested {
        Language::Auto => {
            let rust = path.join("Cargo.toml").is_file()
                || path.extension().is_some_and(|extension| extension == "rs");
            let cpp = looks_like_cpp_project(path);
            match (rust, cpp) {
                (true, true) => SelectedLanguage::Mixed,
                (false, true) => SelectedLanguage::Cpp,
                _ => SelectedLanguage::Rust,
            }
        }
        Language::Rust => SelectedLanguage::Rust,
        Language::Cpp => SelectedLanguage::Cpp,
    }
}

fn analysis_options_for_language(
    language: SelectedLanguage,
    requested_rules: &[RuleId],
) -> AnalysisOptions {
    if !requested_rules.is_empty() {
        return AnalysisOptions::with_rules(requested_rules);
    }

    match language {
        SelectedLanguage::Cpp | SelectedLanguage::Rust | SelectedLanguage::Mixed => {
            AnalysisOptions::all_rules()
        }
    }
}

fn merge_reports(left: Report, right: Report) -> Report {
    let mut findings = left.findings;
    findings.extend(right.findings);
    findings.sort_by(|left, right| {
        left.category
            .cmp(&right.category)
            .then_with(|| left.file.cmp(&right.file))
            .then_with(|| left.line.cmp(&right.line))
            .then_with(|| left.rule_id.cmp(&right.rule_id))
    });
    let mut scanned_crates = left.scanned_crates;
    scanned_crates.extend(right.scanned_crates);
    scanned_crates.sort();
    scanned_crates.dedup();
    let mut diagnostics = left.diagnostics;
    diagnostics.extend(right.diagnostics);
    let candidate_findings = left.summary.candidate_findings + right.summary.candidate_findings;
    let suppressed_candidates =
        left.summary.suppressed_candidates + right.summary.suppressed_candidates;
    let finding_occurrence_count =
        left.summary.finding_occurrence_count + right.summary.finding_occurrence_count;

    Report {
        schema_version: REPORT_SCHEMA_VERSION,
        detector_version: DETECTOR_VERSION,
        scanned_files: left.scanned_files + right.scanned_files,
        scanned_crates,
        enabled_rules: left.enabled_rules,
        ablated_components: left.ablated_components,
        cache_line_size: left.cache_line_size,
        analysis_incomplete: left.analysis_incomplete || right.analysis_incomplete,
        truncated_facts: left.truncated_facts + right.truncated_facts,
        diagnostics,
        summary: ReportSummary {
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
            suppressed_candidates,
            cpp_speculative_candidates: left.summary.cpp_speculative_candidates
                + right.summary.cpp_speculative_candidates,
            finding_occurrence_count,
            finding_group_count: findings.len(),
        },
        findings,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cache_line_size_defaults_to_64_bytes() {
        let cli = Cli::try_parse_from(["false-sharing-detector"]).expect("parse default CLI");
        assert_eq!(cli.cache_line_size, 64);
    }

    #[test]
    fn cache_line_size_accepts_supported_values() {
        for expected in [32, 64, 128] {
            let cli = Cli::try_parse_from([
                "false-sharing-detector",
                "--cache-line-size",
                &expected.to_string(),
            ])
            .expect("parse supported cache-line size");
            assert_eq!(cli.cache_line_size, expected);
        }
    }

    #[test]
    fn cache_line_size_rejects_unsupported_values() {
        let error = Cli::try_parse_from(["false-sharing-detector", "--cache-line-size", "96"])
            .expect_err("reject unsupported cache-line size");
        assert!(error.to_string().contains("expected 32|64|128"));
    }
}
