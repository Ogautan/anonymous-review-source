use false_sharing_detector::analyzer::analyze_path_with_options;
use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
use false_sharing_detector::pattern_model::core_predicate_holds;
use false_sharing_detector::types::{ALL_RULES, AnalysisOptions, ColocationPattern, RuleId};
use std::{fs, process::Command};

fn rust_findings(
    source: &str,
    rule: RuleId,
    block: usize,
) -> Vec<false_sharing_detector::types::Finding> {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("lib.rs"), source).unwrap();
    let options = AnalysisOptions {
        cache_line_size: block,
        ..AnalysisOptions::with_rules(&[rule])
    };
    let report = analyze_path_with_options(root.path(), &options);
    assert!(!report.analysis_incomplete, "{report:#?}");
    report.findings
}

#[test]
fn owner_alignment_preserves_internal_field_risks() {
    for block in [32, 64, 128] {
        for alignment in ["#[repr(C)]", "#[repr(C, align(128))]"] {
            let source = format!(
                "use std::sync::atomic::{{AtomicU64, Ordering}};\n{alignment}\npub struct State {{ first: AtomicU64, second: AtomicU64 }}\nimpl State {{ pub fn one(&self) {{ self.first.fetch_add(1, Ordering::Relaxed); }} pub fn two(&self) {{ self.second.fetch_add(1, Ordering::Relaxed); }} }}"
            );
            assert!(
                !rust_findings(&source, RuleId::SameObjectFields, block).is_empty(),
                "{source}"
            );
        }
    }
}

#[test]
fn local_wrapper_layout_controls_protection_instead_of_its_name() {
    for block in [32, 64, 128] {
        for wrapper in ["Word", "CachePaddedWord"] {
            for (alignment, protected) in [("", false), ("#[repr(align(128))]", true)] {
                let source = format!(
                    "use std::sync::atomic::{{AtomicU64, Ordering}};\n{alignment}\npub struct {wrapper}(pub AtomicU64);\npub struct Data {{ first: {wrapper}, second: {wrapper} }}\nimpl Data {{ pub fn one(&self) {{ self.first.0.fetch_add(1, Ordering::Relaxed); }} pub fn two(&self) {{ self.second.0.fetch_add(1, Ordering::Relaxed); }} }}"
                );
                assert_eq!(
                    rust_findings(&source, RuleId::SameObjectFields, block).is_empty(),
                    protected,
                    "{source}"
                );
            }
        }
    }
}

#[test]
fn guard_method_names_do_not_establish_a_lock_protocol() {
    for (increment, read) in [("increment", "inspect"), ("lock", "Guard_read")] {
        let source = format!(
            "use std::sync::atomic::{{AtomicUsize, Ordering}};\nuse std::cell::UnsafeCell;\npub struct Data {{ flag: AtomicUsize, value: UnsafeCell<u64> }}\nunsafe impl Sync for Data {{}}\nimpl Data {{ pub fn {increment}(&self) {{ self.flag.fetch_add(1, Ordering::Relaxed); }} pub fn {read}(&self) -> u64 {{ unsafe {{ *self.value.get() }} }} }}"
        );
        assert!(
            !rust_findings(&source, RuleId::SameObjectFields, 64).is_empty(),
            "{source}"
        );
    }
}

#[test]
fn indexed_writes_require_parallel_execution_and_distinct_locations() {
    for source in [
        "fn scope(f: impl FnOnce()) { f(); } fn run(data: &mut [u64]) { scope(|| data[0] = 1); }",
        "fn spawn(f: impl FnOnce()) { f(); } fn run(data: &mut [u64]) { spawn(|| data[0] = 1); }",
        "fn run(data: &mut [u64]) { std::thread::scope(|_| data[0] = 1); }",
        "fn run(data: &mut [u64]) { std::thread::scope(|s| { s.spawn(|| data[0] = 1); }); }",
        "fn run() { std::thread::scope(|s| { for worker in 0..4 { s.spawn(move || { let mut data = vec![0; 4]; data[worker] = 1; }); } }); }",
        "static mut DATA: [u64; 4] = [0; 4]; fn run() { (0..4).into_par_iter().for_each(|agent| { fn unused(agent: usize) { unsafe { DATA[agent] = 1; } } }); }",
    ] {
        assert!(
            rust_findings(source, RuleId::ContiguousElements, 64).is_empty(),
            "{source}"
        );
    }
    let source = "use std::thread as workers; fn run() { static mut DATA: [u64; 4] = [0; 4]; workers::scope(|s| { for worker in 0..4 { s.spawn(move || { unsafe { DATA[worker] = 1; } }); } }); }";
    assert!(!rust_findings(source, RuleId::ContiguousElements, 64).is_empty());
}

#[test]
fn buffer_partition_names_cannot_prove_cache_isolation() {
    for block in [32, 64, 128] {
        for (length, offset) in [
            ("capacity_len", "partition_offset"),
            ("aligned_len", "cache_line_offset"),
        ] {
            let source = format!(
                "fn run(workers: usize, len: usize) {{ let {length} = len; let {offset} = 0; let mut groups = Vec::with_capacity({length}); let ptr = groups.as_mut_ptr(); (0..workers).into_par_iter().for_each(|agent| {{ let slice = unsafe {{ std::slice::from_raw_parts_mut(ptr.add(agent), 1) }}; if agent < len {{ unsafe {{ *slice.get_unchecked_mut(0) = agent; }} }} }}); }}"
            );
            assert!(
                !rust_findings(&source, RuleId::ContiguousElements, block).is_empty(),
                "{source}"
            );
        }
    }
}

fn check_rust_relation(source: &str, expected: RuleId) {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("lib.rs"), source).unwrap();
    for size in [32, 64, 128] {
        for relation in ALL_RULES {
            let mut options = AnalysisOptions::with_rules(&[relation]);
            options.cache_line_size = size;
            let report = analyze_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                relation == expected,
                "{relation}, B={size}: {report:#?}"
            );
            for finding in report.findings {
                let pattern = finding.static_pattern.as_ref().unwrap();
                assert_eq!(finding.rule_id, expected);
                assert_eq!(pattern.rule_id, expected);
                assert!(core_predicate_holds(pattern));
                let json = serde_json::to_value(&finding).unwrap();
                assert_eq!(json["rule_id"], expected.as_str());
                assert!(json.get("related_rule_ids").is_none());
                assert!(json["candidate_kind"].is_string());
            }
        }
    }
}

#[test]
fn independent_allocations_are_selected_from_object_discovery() {
    check_rust_relation(
        r#"
struct AgentSlot { observed: std::cell::Cell<u64>, state: u64 }
impl AgentSlot {
    fn observe(&self) -> u64 { self.observed.get() }
    fn update(&mut self) { self.state += 1; }
}
fn install(agent_key: usize) {
    let raw = Box::into_raw(Box::new(AgentSlot { observed: todo!(), state: 0 }));
    unsafe { REGISTRY.insert(agent_key, &(*raw)); }
}
fn install_all() { for agent_key in 0..8 { install(agent_key); } }
"#,
        RuleId::IndependentAllocations,
    );
}

#[test]
fn independent_statics_exclude_continuous_storage() {
    check_rust_relation(
        r#"
use std::sync::{LazyLock, OnceLock};
struct Harness;
static PRIMARY: OnceLock<Harness> = OnceLock::new();
static FALLBACK: LazyLock<Harness> = LazyLock::new(|| Harness);
pub fn get_or_install(value: Harness) -> &'static Harness {
    let _ = PRIMARY.set(value);
    PRIMARY.get().unwrap_or(&FALLBACK)
}
"#,
        RuleId::IndependentStatics,
    );
}

#[test]
fn static_arrays_use_the_element_relation_in_cpp_and_cli() {
    let root = tempfile::tempdir().unwrap();
    fs::write(
        root.path().join("example.cpp"),
        r#"
#include <atomic>
static std::atomic<int> counters[16];
void update() {
#pragma omp parallel for
    for (int index = 0; index < 16; ++index) {
        counters[index].fetch_add(1);
    }
}
"#,
    )
    .unwrap();
    for relation in ALL_RULES {
        let report =
            analyze_cpp_path_with_options(root.path(), &AnalysisOptions::with_rules(&[relation]));
        assert_eq!(
            !report.findings.is_empty(),
            relation == RuleId::ContiguousElements,
            "{report:#?}"
        );
        for finding in report.findings {
            let pattern = finding.static_pattern.unwrap();
            assert_eq!(
                pattern.colocation_pattern,
                ColocationPattern::ContiguousElements
            );
            assert_eq!(finding.rule_id, pattern.rule_id);
            assert!(
                pattern
                    .language_specific_assumptions
                    .contains(&"cpp_array_or_container_elements_are_contiguous")
            );
            assert!(core_predicate_holds(&pattern));
        }
    }
    let output = Command::new(env!("CARGO_BIN_EXE_false-sharing-detector"))
        .arg(root.path())
        .args([
            "--language",
            "cpp",
            "--rule",
            "contiguous_elements",
            "--json",
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["schema_version"], "false-sharing-static-report/v5");
    assert_eq!(
        report["enabled_rules"],
        serde_json::json!(["contiguous_elements"])
    );
    assert!(!report["findings"].as_array().unwrap().is_empty());
    let obsolete = Command::new(env!("CARGO_BIN_EXE_false-sharing-detector"))
        .args(["--rule", "fs001"])
        .output()
        .unwrap();
    assert!(!obsolete.status.success());
}

#[test]
fn same_object_discovery_methods_share_one_rule() {
    check_rust_relation(
        r#"
use std::sync::atomic::{AtomicUsize, Ordering};
#[repr(C)]
pub struct Counts { left: AtomicUsize, right: AtomicUsize }
impl Counts {
    pub fn left(&self) { self.left.fetch_add(1, Ordering::Relaxed); }
    pub fn right(&self) { self.right.fetch_add(1, Ordering::Relaxed); }
}
"#,
        RuleId::SameObjectFields,
    );
}

#[test]
fn raw_buffer_element_alignment_is_checked_against_the_configured_block() {
    for block in [32, 64, 128] {
        let source = "#[repr(align(64))] struct Slot(u64); fn run(len: usize) { let mut data = Vec::<Slot>::with_capacity(len); let ptr = data.as_mut_ptr(); (0..len).into_par_iter().for_each(|agent| { let slice = unsafe { std::slice::from_raw_parts_mut(ptr.add(agent), 1) }; if agent < len { unsafe { *slice.get_unchecked_mut(0) = Slot(1); } } }); }";
        assert_eq!(
            rust_findings(source, RuleId::ContiguousElements, block).is_empty(),
            block <= 64,
            "B={block}"
        );
    }
}

#[test]
fn a_parallel_guard_does_not_turn_one_raw_slot_into_distinct_locations() {
    for index in ["0", "index"] {
        let statement = if index == "index" {
            "for index in 0..1 { *slice.get_unchecked_mut(index) = agent; }"
        } else {
            "*slice.get_unchecked_mut(0) = agent;"
        };
        let source = format!(
            "fn run(len: usize) {{ let mut data = Vec::with_capacity(len); let ptr = data.as_mut_ptr(); (0..len).into_par_iter().for_each(|agent| {{ let slice = unsafe {{ std::slice::from_raw_parts_mut(ptr, 1) }}; if agent < len {{ unsafe {{ {statement} }} }} }}); }}"
        );
        assert!(
            rust_findings(&source, RuleId::ContiguousElements, 64).is_empty(),
            "{source}"
        );
    }
}

#[test]
fn source_backed_slice_accessors_preserve_indices_without_name_contracts() {
    for name in ["slot", "read_at"] {
        for (body, expected) in [
            ("&mut self[index]", true),
            (
                "if cfg!(debug_assertions) { &mut self[index] } else { self.get_unchecked_mut(index) }",
                true,
            ),
            ("&mut self[0]", false),
        ] {
            let root = tempfile::tempdir().unwrap();
            fs::write(root.path().join("accessor.rs"), format!("trait Access<T> {{ unsafe fn {name}(&mut self, index: usize) -> &mut T; }} impl<T> Access<T> for [T] {{ unsafe fn {name}(&mut self, index: usize) -> &mut T {{ {body} }} }}")).unwrap();
            fs::write(root.path().join("run.rs"), format!("fn run(len: usize) {{ let mut data = Vec::with_capacity(len); let ptr = data.as_mut_ptr(); (0..len).into_par_iter().for_each(|agent| {{ let slice = unsafe {{ std::slice::from_raw_parts_mut(ptr, len) }}; for index in 0..len {{ if index % len == agent {{ unsafe {{ *slice.{name}(index) = agent; }} }} }} }}); }}")).unwrap();
            let report = analyze_path_with_options(
                root.path(),
                &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
            );
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "{name}: {body}: {report:#?}"
            );
        }
    }
}
