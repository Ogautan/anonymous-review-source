use false_sharing_detector::analyzer::analyze_path_with_options;
use false_sharing_detector::pattern_model::core_predicate_holds;
use false_sharing_detector::types::AnalysisOptions;
use false_sharing_detector::types::RuleId;
use std::fs;

fn setup_test_dir(_name: &str, files: &[(&str, &str)]) -> tempfile::TempDir {
    let root = tempfile::tempdir().unwrap();
    for (name, source) in files {
        let path = root.path().join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }
    root
}

#[test]
fn writer_neighbor_reports_both_fields_and_keeps_later_accessed_peers() {
    for cache_line_size in [32, 64, 128] {
        let root = setup_test_dir(
            "writer_neighbor_pairs",
            &[(
                "src/lib.rs",
                r#"
use std::sync::atomic::{AtomicUsize, Ordering};
pub struct State {
    pub unused: usize,
    pub counter: AtomicUsize,
    pub first: usize,
    pub second: usize,
}
impl State {
    pub fn increment(&self) { self.counter.fetch_add(1, Ordering::Relaxed); }
    pub fn read_first(&self) -> usize { self.first }
    pub fn read_second(&self) -> usize { self.second }
}
"#,
            )],
        );
        let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
        options.cache_line_size = cache_line_size;
        let report = analyze_path_with_options(root.path(), &options);
        for peer in ["first", "second"] {
            let finding = report
                .findings
                .iter()
                .find(|f| {
                    f.field_list.contains(&"counter".to_string())
                        && f.field_list.contains(&peer.to_string())
                })
                .unwrap_or_else(|| {
                    panic!(
                        "missing counter/{peer} at {cache_line_size}: {:#?}",
                        report.findings
                    )
                });
            assert_eq!(finding.field_list.len(), 3);
            // The relation also enables the field-group discovery alongside both writer-neighbor pairs.
            assert_eq!(finding.finding_occurrence_count, 3);
            assert!(core_predicate_holds(
                finding.static_pattern.as_ref().unwrap()
            ));
        }
        assert!(
            report
                .findings
                .iter()
                .all(|f| !f.field_list.iter().any(|n| n == "unused"))
        );
    }
}

#[test]
fn per_agent_object_reports_accessed_read_fields_but_requires_a_writer() {
    for (write, aligned, expected) in [
        (true, false, true),
        (false, false, false),
        (true, true, false),
    ] {
        let root = setup_test_dir(
            "per_agent_reads",
            &[(
                "src/lib.rs",
                &format!(
                    r#"
{}
struct AgentSlot {{ observed: std::cell::Cell<u64>, state: u64, unused: u64 }}
impl AgentSlot {{
    fn observe(&self) -> u64 {{ self.observed.get() }}
    fn update(&mut self) {{ {} }}
}}
fn install(agent_key: usize) {{
    let raw = Box::into_raw(Box::new(AgentSlot {{ observed: todo!(), state: 0, unused: 0 }}));
    unsafe {{ REGISTRY.insert(agent_key, &(*raw)); }}
}}
fn install_all() {{ for agent_key in 0..8 {{ install(agent_key); }} }}
"#,
                    if aligned { "#[repr(align(128))]" } else { "" },
                    if write { "self.state += 1;" } else { "" }
                ),
            )],
        );
        let report = analyze_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[
                RuleId::ContiguousElements,
                RuleId::IndependentAllocations,
            ]),
        );
        let finding = report
            .findings
            .iter()
            .find(|f| f.struct_name.as_deref() == Some("AgentSlot"));
        assert_eq!(
            finding.is_some(),
            expected,
            "write={write}, aligned={aligned}"
        );
        if let Some(finding) = finding {
            assert!(finding.field_list.contains(&"observed".into()));
            assert!(finding.field_list.contains(&"state".into()));
            assert!(!finding.field_list.contains(&"unused".into()));
            assert!(
                finding
                    .static_pattern
                    .as_ref()
                    .unwrap()
                    .witness_locations
                    .iter()
                    .all(|location| location.ends_with(".state"))
            );
        }
    }
}

#[test]
fn writer_neighbor_does_not_cross_a_known_repr_c_gap_to_recover_a_peer() {
    for cache_line_size in [32, 64, 128] {
        let source = format!(
            r#"
use std::sync::atomic::{{AtomicUsize, Ordering}};
#[repr(C)]
pub struct State {{
    pub counter: AtomicUsize,
    pub middle: [u8; {}],
    pub peer: std::cell::Cell<usize>,
}}
impl State {{
    pub fn increment(&self) {{ self.counter.fetch_add(1, Ordering::Relaxed); }}
    pub fn observe(&self) -> usize {{ self.peer.get() }}
}}
"#,
            cache_line_size * 2
        );
        let root = setup_test_dir("writer_neighbor_separated", &[("src/lib.rs", &source)]);
        let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
        options.cache_line_size = cache_line_size;
        let report = analyze_path_with_options(root.path(), &options);
        assert!(
            report.findings.is_empty(),
            "size={cache_line_size}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn writer_neighbor_value_reads_are_not_inferred_from_borrows_or_arbitrary_clone_calls() {
    let root = setup_test_dir(
        "writer_neighbor_borrow_only",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicUsize, Ordering};
pub struct Opaque;
impl Opaque { pub fn clone(&self) -> usize { 0 } }
pub struct State { pub counter: AtomicUsize, pub payload: usize, pub opaque: Opaque }
impl State {
    pub fn increment(&self) { self.counter.fetch_add(1, Ordering::Relaxed); }
    pub fn address(&self) -> &usize { &self.payload }
    pub fn borrowed(&self) { let reference = &self.payload; consume(reference); }
    pub fn custom_clone(&self) -> usize { self.opaque.clone() }
}
"#,
        )],
    );
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn object_instances_uses_minimum_stride_for_same_field_across_objects() {
    let dir = setup_test_dir(
        "object_instances_minimum_stride",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct WideNode {
    first: String,
    second: String,
    third: String,
    state: AtomicUsize,
}

impl WideNode {
    pub fn advance(&self) {
        self.state.fetch_add(1, Ordering::Relaxed);
    }
}

struct Pool {
    nodes: Vec<WideNode>,
}

fn schedule(node: Arc<WideNode>) {
    std::thread::spawn(move || node.advance());
}
"#,
        )],
    );

    let at_64 =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    let report_64 = analyze_path_with_options(dir.path(), &at_64);
    assert!(
        report_64
            .findings
            .iter()
            .all(|f| !(f.candidate_kind == "object_instances"
                && f.struct_name.as_deref() == Some("WideNode"))),
        "at B=64, three inline String handles separate the same atomic field"
    );

    let mut at_128 =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    at_128.cache_line_size = 128;
    let report_128 = analyze_path_with_options(dir.path(), &at_128);
    assert!(
        report_128.findings.iter().any(|f| {
            f.candidate_kind == "object_instances" && f.struct_name.as_deref() == Some("WideNode")
        }),
        "the 80-byte minimum stride cannot exclude colocation at B=128"
    );
}

#[test]
fn object_instances_keeps_cross_field_boundary_risk_for_wide_objects() {
    let dir = setup_test_dir(
        "object_instances_wide_cross_field",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct WideNode {
    first: String,
    second: String,
    third: String,
    head: AtomicUsize,
    tail: AtomicUsize,
}

impl WideNode {
    pub fn advance(&self) {
        self.head.fetch_add(1, Ordering::Relaxed);
        self.tail.fetch_add(1, Ordering::Relaxed);
    }
}

struct Pool {
    nodes: Vec<WideNode>,
}

fn schedule(node: Arc<WideNode>) {
    std::thread::spawn(move || node.advance());
}
"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]),
    );
    assert!(
        report.findings.iter().any(|f| {
            f.candidate_kind == "object_instances" && f.struct_name.as_deref() == Some("WideNode")
        }),
        "different fields near an object boundary may still share a line"
    );
}
