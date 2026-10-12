use false_sharing_detector::analyzer::analyze_path_with_options;
use false_sharing_detector::pattern_model::core_predicate_holds;
use false_sharing_detector::types::AnalysisOptions;
use false_sharing_detector::types::RuleId;
use std::fs;

#[test]
fn cargo_custom_targets_keep_entries_modules_and_logical_module_names() {
    let source = "use std::sync::{Arc, atomic::{AtomicU64, Ordering}};\npub struct State { left: AtomicU64, right: AtomicU64 }\nimpl State { pub fn one(&self) { self.left.fetch_add(1, Ordering::Relaxed); } pub fn two(&self) { self.right.fetch_add(1, Ordering::Relaxed); } }\npub fn use_state(s: Arc<State>) { s.one(); s.two(); }\n";
    for (manifest, entry, module) in [
        ("[lib]\npath = 'lib.rs'", "lib.rs", None),
        (
            "[lib]\npath = 'custom/entry.rs'",
            "custom/entry.rs",
            Some((
                "custom/renamed.rs",
                "#[path = \"renamed.rs\"] pub mod counters;\n",
            )),
        ),
        (
            "[[bin]]\nname = 'driver'\npath = 'app/driver.rs'",
            "app/driver.rs",
            Some(("app/counters.rs", "pub mod counters;\nfn main() {}\n")),
        ),
    ] {
        let root = tempfile::tempdir().unwrap();
        fs::write(
            root.path().join("Cargo.toml"),
            format!(
                "[package]\nname = 'fixture'\nversion = '0.1.0'\nedition = '2024'\n{manifest}\n"
            ),
        )
        .unwrap();
        fs::create_dir_all(root.path().join(entry).parent().unwrap()).unwrap();
        if let Some((path, entry_source)) = module {
            fs::write(root.path().join(entry), entry_source).unwrap();
            fs::write(root.path().join(path), source).unwrap();
        } else {
            fs::write(root.path().join(entry), source).unwrap();
        }
        fs::create_dir(root.path().join("src")).unwrap();
        fs::write(
            root.path().join("src/unused.rs"),
            "// Not part of the declared target.\n",
        )
        .unwrap();
        let report = analyze_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert!(!report.analysis_incomplete, "{report:#?}");
        let finding = report
            .findings
            .iter()
            .find(|finding| finding.struct_name.as_deref() == Some("State"))
            .expect("custom target should be analyzed");
        let canonical = &finding.layout_context.as_ref().unwrap().canonical_type;
        assert_eq!(
            canonical,
            if module.is_some() {
                "counters::State"
            } else {
                "State"
            }
        );
    }
}

#[test]
fn missing_declared_cargo_target_reports_incomplete_discovery() {
    let root = setup_test_dir(
        "missing_target",
        &[
            (
                "Cargo.toml",
                "[package]\nname='fixture'\nversion='0.1.0'\n[lib]\npath='absent.rs'\n",
            ),
            (
                "src/unused.rs",
                "// Existing unrelated source must not hide the missing target.\n",
            ),
        ],
    );
    let report = analyze_path_with_options(root.path(), &AnalysisOptions::all_rules());
    assert!(report.analysis_incomplete, "{report:#?}");
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.stage == "discovery"
                && diagnostic.message.contains("declared Cargo source target"))
    );
}

#[test]
fn shared_api_respects_known_sync_restrictions_and_explicit_overrides() {
    for (declaration, implementation, expected) in [
        ("std::cell::Cell<u8>", "", false),
        ("std::cell::RefCell<u8>", "", false),
        ("std::cell::UnsafeCell<u8>", "", false),
        ("std::rc::Rc<u8>", "", false),
        ("Box<std::cell::Cell<u8>>", "", false),
        ("std::sync::Mutex<std::cell::Cell<u8>>", "", true),
        ("Opaque", "", true),
        (
            "u8",
            "#[cfg(feature = \"not_sync\")] impl !Sync for State {}",
            true,
        ),
        ("std::cell::Cell<u8>", "unsafe impl Sync for State {}", true),
        (
            "std::cell::Cell<u8>",
            "#[cfg(feature = \"shared\")] unsafe impl Sync for State {}",
            true,
        ),
        (
            "std::cell::Cell<u8>",
            "unsafe impl Send for State {}",
            false,
        ),
        ("u8", "impl !Sync for State {}", false),
    ] {
        let source = format!(
            "use std::sync::{{Arc,atomic::{{AtomicU64,Ordering}}}};\npub struct State {{ left:AtomicU64,right:AtomicU64,private:{declaration} }}\n{implementation}\nimpl State {{pub fn one(&self){{self.left.fetch_add(1,Ordering::Relaxed);}}pub fn two(&self){{self.right.fetch_add(1,Ordering::Relaxed);}}}}\npub fn use_state(s:Arc<State>){{s.one();s.two();}}\n"
        );
        let root = setup_test_dir("sync_restrictions", &[("lib.rs", &source)]);
        let report = analyze_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert!(!report.analysis_incomplete, "{report:#?}");
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{declaration}, {implementation}: {report:#?}"
        );
    }
}

#[test]
fn sync_restrictions_follow_imports_aliases_and_local_wrappers() {
    for (types, payload, expected) in [
        ("use std::cell::Cell as LocalCell;", "LocalCell<u8>", false),
        ("use std::cell;", "cell::Cell<u8>", false),
        ("use std::cell::*;", "Cell<u8>", false),
        ("type Payload = std::cell::Cell<u8>;", "Payload", false),
        (
            "#[cfg(feature = \"local\")] type Payload = std::cell::Cell<u8>; #[cfg(not(feature = \"local\"))] type Payload = u8;",
            "Payload",
            true,
        ),
        ("struct Payload(std::cell::Cell<u8>);", "Payload", false),
        (
            "struct Payload(std::cell::Cell<u8>); unsafe impl Sync for Payload {}",
            "Payload",
            true,
        ),
        ("struct Cell<T>(T);", "Cell<u8>", true),
        (
            "struct Cell<T>(T); type Payload = Cell<u8>;",
            "Payload",
            true,
        ),
        (
            "mod custom { pub struct Cell<T>(pub T); }",
            "custom::Cell<u8>",
            true,
        ),
    ] {
        let source = format!(
            "use std::sync::{{Arc,atomic::{{AtomicU64,Ordering}}}};\n{types}\npub struct State{{left:AtomicU64,right:AtomicU64,payload:{payload}}}\nimpl State{{pub fn one(&self){{self.left.fetch_add(1,Ordering::Relaxed);}}pub fn two(&self){{self.right.fetch_add(1,Ordering::Relaxed);}}}}\npub fn use_state(s:Arc<State>){{s.one();s.two();}}\n"
        );
        let root = setup_test_dir("sync_bindings", &[("lib.rs", &source)]);
        let report = analyze_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{types}: {report:#?}"
        );
    }
}

#[test]
fn non_sync_receiver_keeps_concrete_raw_pointer_parallel_accesses() {
    let source = "use std::sync::atomic::{AtomicU64,Ordering};\npub struct State{left:AtomicU64,right:AtomicU64,payload:std::cell::Cell<u8>}\npub unsafe fn one(s:*const State){unsafe{(*s).left.fetch_add(1,Ordering::Relaxed);}}\npub unsafe fn two(s:*const State){unsafe{(*s).right.fetch_add(1,Ordering::Relaxed);}}\n";
    let root = setup_test_dir("raw_sync_bypass", &[("lib.rs", source)]);
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(!report.findings.is_empty(), "{report:#?}");
}

#[test]
fn non_sync_receiver_can_expose_sync_field_references() {
    for projection in ["pub left: AtomicU64", "left: AtomicU64"] {
        let getter = if projection.starts_with("pub") {
            ""
        } else {
            "pub fn left_ref(&self) -> &AtomicU64 { &self.left }"
        };
        let source = format!(
            "use std::sync::{{Arc,atomic::{{AtomicU64,Ordering}}}};\npub struct State{{{projection},right:AtomicU64,private:std::cell::Cell<u8>}}\nimpl State{{pub fn one(&self){{self.left.fetch_add(1,Ordering::Relaxed);}}pub fn two(&self){{self.right.fetch_add(1,Ordering::Relaxed);}}{getter}}}\npub fn use_state(s:Arc<State>){{s.one();s.two();}}\n"
        );
        let root = setup_test_dir("field_projection", &[("lib.rs", &source)]);
        let report = analyze_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert!(
            !report.findings.is_empty(),
            "{projection}, {getter}: {report:#?}"
        );
    }
}

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
