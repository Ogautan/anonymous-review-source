use false_sharing_detector::types::RuleId;
use false_sharing_detector::{
    analyzer::analyze_path_with_options, cpp_detection::analyze_cpp_path_with_options,
    types::AnalysisOptions,
};
use std::fs;
use tempfile::tempdir;

#[test]
fn cpp_cross_file_indexed_occurrences_share_one_global_storage_group() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("decl.cpp"),
        "int values[64];\nvoid direct() { values[omp_get_thread_num()]++; }\n",
    )
    .unwrap();
    fs::write(
        root.path().join("use.cpp"),
        "extern int values[64];\nvoid worker() { values[omp_get_thread_num()]++; }\n",
    )
    .unwrap();

    let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    options.cpp_include_speculative = true;
    let report = analyze_cpp_path_with_options(root.path(), &options);
    let findings = report
        .findings
        .iter()
        .filter(|finding| finding.field_list == ["values"])
        .collect::<Vec<_>>();

    assert_eq!(findings.len(), 1, "{report:#?}");
    assert_eq!(findings[0].finding_occurrence_count, 2, "{report:#?}");
    assert_eq!(report.summary.finding_group_count, 1, "{report:#?}");
    assert!(
        findings[0]
            .storage_identity
            .as_deref()
            .is_some_and(|identity| identity.contains("decl.cpp::values@1"))
    );
    assert!(
        findings[0]
            .usage_locations
            .iter()
            .any(|location| location.file.ends_with("use.cpp"))
    );
}

#[test]
fn cpp_summary_keeps_callee_storage_despite_caller_shadow() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("storage.cpp"),
        "int slots[64];\nvoid update(int worker_id) {\nslots[worker_id]++;\n}\n",
    )
    .unwrap();
    fs::write(root.path().join("caller.cpp"), "void update(int);\nint slots[64];\nvoid run() {\nint worker_id = omp_get_thread_num();\nupdate(worker_id);\nslots[worker_id]++;\n}\n").unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    options.cpp_include_speculative = true;
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert_eq!(report.findings.len(), 2, "{report:#?}");
    let storage = report
        .findings
        .iter()
        .find(|f| {
            f.storage_identity
                .as_deref()
                .is_some_and(|s| s.contains("storage.cpp::slots"))
        })
        .unwrap();
    assert!(
        storage
            .usage_locations
            .iter()
            .any(|l| l.file.ends_with("caller.cpp")),
        "{report:#?}"
    );
    assert!(report.findings.iter().any(|f| {
        f.storage_identity
            .as_deref()
            .is_some_and(|s| s.contains("caller.cpp::slots"))
    }));
}

#[test]
fn cpp_internal_arrays_are_distinct_objects() {
    let root = tempdir().unwrap();
    for file in ["one.cpp", "two.cpp"] {
        fs::write(
            root.path().join(file),
            "static int slots[64];\nvoid run() { slots[omp_get_thread_num()]++; }\n",
        )
        .unwrap();
    }
    let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    options.cpp_include_speculative = true;
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert_eq!(report.findings.len(), 2, "{report:#?}");
    assert_ne!(
        report.findings[0].finding_group_id,
        report.findings[1].finding_group_id
    );
}

fn rust_project(files: &[(&str, &str)]) -> tempfile::TempDir {
    let root = tempdir().unwrap();
    fs::create_dir(root.path().join("src")).unwrap();
    fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname = \"storage_test\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    for (name, source) in files {
        fs::write(root.path().join("src").join(name), source).unwrap();
    }
    root
}

#[test]
fn rust_static_paths_and_explicit_aliases_share_one_root() {
    let root = rust_project(&[
        (
            "lib.rs",
            "mod state; mod caller;\nfn run() { (0..8).into_par_iter().for_each(|i| { crate::state::SLOTS[i] = 1; }); }\n",
        ),
        (
            "state.rs",
            "pub static mut SLOTS: [u64; 64] = [0; 64];\nfn run() { (0..8).into_par_iter().for_each(|i| { SLOTS[i] = 2; }); }\n",
        ),
        (
            "caller.rs",
            "use crate::state::SLOTS as COUNTERS;\nfn run() { (0..8).into_par_iter().for_each(|i| { COUNTERS[i] = 3; }); }\n",
        ),
    ]);
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert_eq!(report.findings.len(), 1, "{report:#?}");
    assert_eq!(
        report.findings[0].finding_occurrence_count, 3,
        "{report:#?}"
    );
    assert_eq!(report.findings[0].usage_locations.len(), 3);
}

#[test]
fn rust_separate_statics_in_one_file_are_separate_roots() {
    let root = rust_project(&[(
        "lib.rs",
        "static mut LEFT: [u64;64] = [0;64];\nstatic mut RIGHT: [u64;64] = [0;64];\nfn run() { (0..8).into_par_iter().for_each(|i| { LEFT[i] = 1; RIGHT[i] = 2; }); }\n",
    )]);
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert_eq!(report.findings.len(), 2, "{report:#?}");
    assert_ne!(
        report.findings[0].finding_group_id,
        report.findings[1].finding_group_id
    );
}

#[test]
fn rust_same_member_names_in_different_records_are_distinct() {
    let root = rust_project(&[(
        "lib.rs",
        "struct Left { slots: Vec<u64> }\nstruct Right { slots: Vec<u64> }\nimpl Left { fn run(&mut self) { (0..8).into_par_iter().for_each(|i| { self.slots[i] = 1; }); } }\nimpl Right { fn run(&mut self) { (0..8).into_par_iter().for_each(|i| { self.slots[i] = 1; }); } }\n",
    )]);
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert_eq!(report.findings.len(), 2, "{report:#?}");
    assert!(report.findings.iter().all(|f| f.struct_name.is_some()));
    assert_ne!(
        report.findings[0].finding_group_id,
        report.findings[1].finding_group_id
    );
}

#[test]
fn rust_static_shadowed_by_parameter_is_not_the_same_storage() {
    let root = rust_project(&[(
        "lib.rs",
        "static mut SLOTS: [u64;64] = [0;64];\nfn global() { (0..8).into_par_iter().for_each(|i| { SLOTS[i] = 1; }); }\nfn parameter(SLOTS: &mut [u64]) { (0..8).into_par_iter().for_each(|i| { SLOTS[i] = 2; }); }\n",
    )]);
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert_eq!(report.findings.len(), 2, "{report:#?}");
    assert_eq!(
        report
            .findings
            .iter()
            .filter(|f| f.storage_identity.is_some())
            .count(),
        1
    );
}

#[test]
fn cpp_static_and_indexed_rules_share_storage_root() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("a.cpp"),
        "std::atomic<int> counters[8];\nvoid run() { counters[omp_get_thread_num()]++; }\n",
    )
    .unwrap();
    let mut options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    options.cpp_include_speculative = true;
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert_eq!(report.findings.len(), 1, "{report:#?}");
    assert_eq!(
        report.findings[0].finding_occurrence_count, 2,
        "{report:#?}"
    );
    assert_eq!(report.findings[0].related_candidate_kinds.len(), 1);
}

#[test]
fn cpp_included_extern_declaration_binds_to_definition() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("slots.h"), "extern int slots[8];\n").unwrap();
    fs::write(
        root.path().join("a.cpp"),
        "int slots[8];\nvoid run() { slots[omp_get_thread_num()]++; }\n",
    )
    .unwrap();
    fs::write(
        root.path().join("b.cpp"),
        "#include \"slots.h\"\nvoid run_other() { slots[omp_get_thread_num()]++; }\n",
    )
    .unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    options.cpp_include_speculative = true;
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert_eq!(report.findings.len(), 1, "{report:#?}");
    assert_eq!(report.findings[0].finding_occurrence_count, 2);
}

#[test]
fn rust_local_allocations_with_same_name_keep_distinct_roots() {
    let function = r#"
fn FUNCTION(workers: usize, len: usize) {
    let mut groups = Vec::with_capacity(len);
    let groups_ptr = unsafe { SyncPtr::new(groups.as_mut_ptr()) };
    (0..workers).into_par_iter().for_each(|agent| {
        let groups = unsafe { std::slice::from_raw_parts_mut(groups_ptr.get(), len) };
        for index in 0..len {
            if belongs_to_partition(index, agent, workers) {
                unsafe { *groups.get_unchecked_mut(index) = agent; }
            }
        }
    });
}
"#;
    let source = function.replace("FUNCTION", "first") + &function.replace("FUNCTION", "second");
    let root = rust_project(&[("lib.rs", &source)]);
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert_eq!(report.findings.len(), 2, "{report:#?}");
    assert!(report.findings.iter().all(|f| f.storage_identity.is_some()));
    assert_ne!(
        report.findings[0].finding_group_id,
        report.findings[1].finding_group_id
    );
}
