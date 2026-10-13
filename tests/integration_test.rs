use false_sharing_detector::analyzer::analyze_path_with_options;
use false_sharing_detector::pattern_model::core_predicate_holds;
use false_sharing_detector::types::RuleId;
use false_sharing_detector::types::{
    AccessPattern, AnalysisOptions, ColocationPattern, RiskCategory,
};
use std::fs;
use std::process::Command;

fn setup_test_dir(_name: &str, files: &[(&str, &str)]) -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    for (filename, content) in files {
        let path = dir.path().join(filename);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(&path, content).unwrap();
    }
    dir
}

fn has_installed_nightly_toolchain() -> bool {
    Command::new("rustup")
        .arg("toolchain")
        .arg("list")
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| {
            String::from_utf8_lossy(&output.stdout)
                .lines()
                .filter_map(|line| line.split_whitespace().next())
                .any(|name| name.starts_with("nightly"))
        })
        .unwrap_or(false)
}

// --- field_group: Multiple atomic fields ---

#[test]
fn field_group_detects_unpadded_heterogeneous_waker_and_list_state() {
    let dir = setup_test_dir(
        "field_group_heterogeneous_hot_state",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

struct AtomicWaker;
impl AtomicWaker {
    fn register(&self) {}
}

mod list {
    pub struct Tx<T>(pub std::marker::PhantomData<T>);
    impl<T> Tx<T> {
        pub fn push(&self) {}
    }
}

pub(crate) struct Chan<T> {
    tx: list::Tx<T>,
    rx_waker: AtomicWaker,
    tx_count: AtomicUsize,
}

impl<T> Chan<T> {
    pub(crate) fn push(&self) {
        self.tx.push();
    }

    pub(crate) fn poll(&self) {
        self.rx_waker.register();
    }

    pub(crate) fn clone_sender(&self) {
        self.tx_count.fetch_add(1, Ordering::Relaxed);
    }
}

fn drive<T>(chan: Arc<Chan<T>>) {
    let sender = Arc::clone(&chan);
    std::thread::spawn(move || sender.push());
    let receiver = Arc::clone(&chan);
    std::thread::spawn(move || receiver.poll());
    chan.clone_sender();
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|finding| {
            finding.struct_name.as_deref() == Some("Chan")
                && finding.field_list.iter().any(|field| field == "tx")
        })
        .expect("heterogeneous lock-free handle/waker state should be detected");

    assert!(finding.field_list.iter().any(|field| field == "tx"));
    assert!(finding.field_list.iter().any(|field| field == "rx_waker"));
    assert_eq!(
        finding
            .layout_context
            .as_ref()
            .map(|layout| layout.layout_certainty.as_str()),
        Some("symbolic")
    );
}

#[test]
fn field_group_heterogeneous_hot_state_respects_cache_padding() {
    let dir = setup_test_dir(
        "field_group_heterogeneous_hot_state_padded",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicUsize;

struct AtomicWaker;
mod list { pub struct Tx<T>(pub std::marker::PhantomData<T>); }
#[repr(align(64))]
struct CachePadded<T>(T);

pub(crate) struct Chan<T> {
    tx: CachePadded<list::Tx<T>>,
    rx_waker: CachePadded<AtomicWaker>,
    tx_count: AtomicUsize,
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|finding| finding.struct_name.as_deref() != Some("Chan")),
        "CachePadded heterogeneous fields must be excluded from the candidate cluster"
    );
}

#[test]
fn field_group_private_layout_only_is_not_reported() {
    let dir = setup_test_dir(
        "field_group_private_layout_only",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicU64, Ordering};

struct MyStruct {
    counter_a: AtomicU64,
    counter_b: AtomicU64,
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "field_group"),
        "private layout-only structs should be suppressed by default"
    );
}

#[test]
fn field_group_hot_in_project_when_arc_wrapped_and_atomic_ops() {
    let dir = setup_test_dir(
        "field_group_hot_in_project",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

struct SharedCounters {
    read_count: AtomicU64,
    write_count: AtomicU64,
}

impl SharedCounters {
    fn inc_read(&self) {
        self.read_count.fetch_add(1, Ordering::Relaxed);
    }
    fn inc_write(&self) {
        self.write_count.fetch_add(1, Ordering::Relaxed);
    }
}

fn usage() {
    let s: Arc<SharedCounters> = Arc::new(SharedCounters {
        read_count: AtomicU64::new(0),
        write_count: AtomicU64::new(0),
    });
    let s2 = Arc::clone(&s);
    std::thread::spawn(move || {
        s2.inc_write();
    });
    s.inc_read();
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    let field_group: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.candidate_kind == "field_group")
        .collect();

    assert!(!field_group.is_empty(), "should detect field_group");
    assert!(
        field_group
            .iter()
            .any(|f| f.category == RiskCategory::HotInProject),
        "with Arc + atomic ops, should be hot_in_project. categories: {:?}",
        field_group.iter().map(|f| &f.category).collect::<Vec<_>>()
    );

    let hot = field_group
        .iter()
        .find(|f| f.category == RiskCategory::HotInProject)
        .unwrap();
    assert!(
        !hot.concurrency_evidence.is_empty(),
        "hot_in_project finding should have evidence"
    );
    assert!(hot.confidence >= 0.80);
    let pattern = hot
        .static_pattern
        .as_ref()
        .expect("field_group pattern witness");
    assert_eq!(pattern.access_pattern, AccessPattern::WriteWrite);
    assert_eq!(
        pattern.colocation_pattern,
        ColocationPattern::SameObjectFields
    );
    assert!(core_predicate_holds(pattern));
}

#[test]
fn field_group_classifies_distinct_field_write_read_interference() {
    let dir = setup_test_dir(
        "field_group_write_read",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

struct SharedState {
    producer_epoch: AtomicU64,
    observer_epoch: AtomicU64,
}

impl SharedState {
    fn publish(&self) {
        self.producer_epoch.store(1, Ordering::Release);
    }
    fn observe(&self) -> u64 {
        self.observer_epoch.load(Ordering::Acquire)
    }
}

fn use_state(state: Arc<SharedState>) {
    let peer = Arc::clone(&state);
    std::thread::spawn(move || peer.publish());
    let _ = state.observe();
}
"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("SharedState"))
        .expect("write/read interference should remain a false-sharing may-risk");
    assert_eq!(
        finding.static_pattern.as_ref().map(|p| p.access_pattern),
        Some(AccessPattern::WriteRead)
    );
}

#[test]
fn field_group_shared_self_writes_are_not_treated_as_exclusive_ownership() {
    let dir = setup_test_dir(
        "field_group_shared_self_not_exclusive",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

struct SharedState {
    phase: AtomicU64,
    generation: AtomicU64,
}

impl SharedState {
    fn advance_phase(&self) {
        self.phase.fetch_add(1, Ordering::Relaxed);
    }

    fn advance_generation(&self) {
        self.generation.fetch_add(1, Ordering::Relaxed);
    }
}

fn share(state: Arc<SharedState>) {
    let other = Arc::clone(&state);
    std::thread::spawn(move || other.advance_phase());
    state.advance_generation();
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);
    assert!(report.findings.iter().any(|finding| {
        finding.candidate_kind == "field_group"
            && finding.struct_name.as_deref() == Some("SharedState")
    }));
}

#[test]
fn field_group_ignores_arc_of_atomic_fields() {
    let dir = setup_test_dir(
        "field_group_arc_fields",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::AtomicBool;

struct MyActor {
    started: Arc<AtomicBool>,
    stopping: Arc<AtomicBool>,
    stopped: Arc<AtomicBool>,
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "field_group"),
        "Arc<Atomic*> pointers should not be treated as inline atomic fields"
    );
}

#[test]
fn field_group_true_sharing_pattern_is_suppressed() {
    let dir = setup_test_dir(
        "field_group_true_sharing",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

struct Histogram {
    count: AtomicU64,
    sum: AtomicU64,
}

impl Histogram {
    fn record(&self, value: u64) {
        self.count.fetch_add(1, Ordering::Relaxed);
        self.sum.fetch_add(value, Ordering::Relaxed);
    }
}

fn usage(hist: Arc<Histogram>) {
    hist.record(1);
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "field_group"),
        "co-updated atomic fields should be suppressed as likely true sharing"
    );
}

#[test]
fn field_group_api_usage_latent_for_independent_stats_counters() {
    let dir = setup_test_dir(
        "field_group_independent_stats",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct ReadCacheStats {
    hit: AtomicUsize,
    miss: AtomicUsize,
}

impl ReadCacheStats {
    pub fn track_hit(&self) {
        self.hit.fetch_add(1, Ordering::Relaxed);
    }

    pub fn track_miss(&self) {
        self.miss.fetch_add(1, Ordering::Relaxed);
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|f| {
            f.candidate_kind == "field_group" && f.struct_name.as_deref() == Some("ReadCacheStats")
        })
        .expect("independent hot stats counters should trigger field_group");

    assert_eq!(finding.category, RiskCategory::ApiUsageLatent);
    assert!(
        finding
            .risk_factors
            .iter()
            .any(|factor| factor.contains("访问分离证据")),
        "finding should explain the name-independent access partition"
    );
}

#[test]
fn field_group_not_triggered_with_cache_padded() {
    let dir = setup_test_dir(
        "field_group_padded",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicU64;

#[repr(align(64))]
struct CachePadded<T>(T);

struct PaddedCounters {
    read_count: CachePadded<AtomicU64>,
    write_count: CachePadded<AtomicU64>,
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    let field_group: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.candidate_kind == "field_group")
        .collect();
    assert!(
        field_group.is_empty(),
        "CachePadded fields should not trigger field_group"
    );
}

#[test]
fn field_group_detects_unpadded_fields_even_when_one_field_is_cache_padded() {
    let dir = setup_test_dir(
        "field_group_partial_padding",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicU64;

#[repr(align(64))]
struct CachePadded<T>(T);

struct PartialPadding {
    a: CachePadded<AtomicU64>,
    b: AtomicU64,
    c: AtomicU64,
}

fn update_b(shared: std::sync::Arc<PartialPadding>) {
    shared.b.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}
fn update_c(shared: std::sync::Arc<PartialPadding>) {
    shared.c.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .any(|f| f.candidate_kind == "field_group"
                && f.field_list == vec!["b".to_string(), "c".to_string()]),
        "field-level padding should not hide remaining unpadded adjacent atomics"
    );
}

#[test]
fn field_group_manual_padding_separates_atomic_fields() {
    let dir = setup_test_dir(
        "field_group_manual_padding",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicU64;

#[repr(C)]
struct ManuallyPadded {
    a: AtomicU64,
    _pad: [u8; 64],
    b: AtomicU64,
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "field_group"),
        "manual padding should make the two atomic fields fall into different cache-line groups"
    );
}

#[test]
fn rustc_layout_suppresses_false_positive_after_field_reordering() {
    if !has_installed_nightly_toolchain() {
        eprintln!("skipping rustc layout integration test: no installed nightly toolchain");
        return;
    }

    let dir = setup_test_dir(
        "rustc_layout_reordered",
        &[
            (
                "Cargo.toml",
                r#"
[package]
name = "rustc_layout_reordered"
version = "0.1.0"
edition = "2024"
"#,
            ),
            (
                "src/lib.rs",
                r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, AtomicU64, Ordering};

pub struct ReorderedCounters {
    small: AtomicU8,
    wide: AtomicU64,
    payload: [u8; 70],
}

impl ReorderedCounters {
    pub fn inc_small(&self) {
        self.small.fetch_add(1, Ordering::Relaxed);
    }

    pub fn inc_wide(&self) {
        self.wide.fetch_add(1, Ordering::Relaxed);
    }
}

pub fn usage() {
    let state = Arc::new(ReorderedCounters {
        small: AtomicU8::new(0),
        wide: AtomicU64::new(0),
        payload: [0; 70],
    });
    let other = Arc::clone(&state);
    std::thread::spawn(move || other.inc_small());
    state.inc_wide();
}
"#,
            ),
        ],
    );

    let default_options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let default_report = analyze_path_with_options(dir.path(), &default_options);
    assert!(
        default_report.findings.iter().any(|f| {
            f.candidate_kind == "field_group"
                && f.struct_name.as_deref() == Some("ReorderedCounters")
        }),
        "default conservative layout should still report adjacent declared atomics"
    );

    let mut rustc_options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    rustc_options.use_rustc_layout = true;
    let rustc_report = analyze_path_with_options(dir.path(), &rustc_options);
    assert!(
        rustc_report.findings.iter().all(|f| {
            !(f.candidate_kind == "field_group"
                && f.struct_name.as_deref() == Some("ReorderedCounters"))
        }),
        "rustc layout should use reordered fields and avoid the false positive"
    );
}

#[test]
fn rustc_layout_falls_back_when_not_a_cargo_project() {
    let dir = setup_test_dir(
        "rustc_layout_fallback",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

pub struct Counters {
    a: AtomicU64,
    b: AtomicU64,
}

impl Counters {
    pub fn inc_a(&self) {
        self.a.fetch_add(1, Ordering::Relaxed);
    }
    pub fn inc_b(&self) {
        self.b.fetch_add(1, Ordering::Relaxed);
    }
}

fn usage() {
    let counters = Arc::new(Counters {
        a: AtomicU64::new(0),
        b: AtomicU64::new(0),
    });
    let left = Arc::clone(&counters);
    let right = Arc::clone(&counters);
    std::thread::spawn(move || left.inc_a());
    std::thread::spawn(move || right.inc_b());
}
"#,
        )],
    );

    let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    options.use_rustc_layout = true;
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .any(|f| f.candidate_kind == "field_group"
                && f.struct_name.as_deref() == Some("Counters")),
        "non-cargo inputs should keep the existing static layout estimate"
    );
}

#[test]
fn field_group_repr_align_smaller_than_cache_line_is_not_enough() {
    let dir = setup_test_dir(
        "field_group_small_align",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicU64;

#[repr(align(32))]
struct UnderAligned {
    a: AtomicU64,
    b: AtomicU64,
}

fn update_a(shared: std::sync::Arc<UnderAligned>) {
    shared.a.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}
fn update_b(shared: std::sync::Arc<UnderAligned>) {
    shared.b.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .any(|f| f.candidate_kind == "field_group"),
        "repr(align(32)) is not cache-line protection for the default 64-byte model"
    );
}

#[test]
fn configured_cache_line_size_detects_transparent_64_byte_wrappers_at_128() {
    let vulnerable = setup_test_dir(
        "field_group_effective_128",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[repr(align(64))]
struct Padded<T>(T);

struct Ring {
    head: Padded<AtomicUsize>,
    flush: Padded<AtomicUsize>,
}

impl Ring {
    fn release(&self, value: usize) {
        self.head.0.store(value, Ordering::Release);
    }
    fn publish(&self, value: usize) {
        self.flush.0.store(value, Ordering::Release);
    }
}

fn run(ring: Arc<Ring>) {
    let consumer = Arc::clone(&ring);
    std::thread::spawn(move || consumer.release(1));
    std::thread::spawn(move || ring.publish(1));
}
"#,
        )],
    );

    let at_64 = analyze_path_with_options(
        vulnerable.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(at_64.findings.iter().all(|finding| {
        !(finding.struct_name.as_deref() == Some("Ring")
            && finding.field_list.contains(&"head".to_string())
            && finding.field_list.contains(&"flush".to_string()))
    }));

    let mut at_128_options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    at_128_options.cache_line_size = 128;
    let at_128 = analyze_path_with_options(vulnerable.path(), &at_128_options);
    let finding = at_128
        .findings
        .iter()
        .find(|finding| {
            finding.struct_name.as_deref() == Some("Ring")
                && finding.field_list.contains(&"head".to_string())
                && finding.field_list.contains(&"flush".to_string())
        })
        .expect("128-byte effective granularity should colocate head and flush");
    assert_eq!(
        finding
            .layout_context
            .as_ref()
            .map(|layout| layout.cache_line_size),
        Some(128)
    );
    assert!(finding.access_evidence.iter().any(|access| {
        access.field_name.as_deref() == Some("head")
            && access
                .semantic_contexts
                .iter()
                .any(|context| context == "transparent_wrapper_projection")
    }));

    let fixed = setup_test_dir(
        "field_group_effective_128_fixed",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[repr(align(128))]
struct Padded<T>(T);

struct Ring {
    head: Padded<AtomicUsize>,
    flush: Padded<AtomicUsize>,
}

impl Ring {
    fn release(&self, value: usize) {
        self.head.0.store(value, Ordering::Release);
    }
    fn publish(&self, value: usize) {
        self.flush.0.store(value, Ordering::Release);
    }
}

fn run(ring: Arc<Ring>) {
    let consumer = Arc::clone(&ring);
    std::thread::spawn(move || consumer.release(1));
    std::thread::spawn(move || ring.publish(1));
}
"#,
        )],
    );
    let fixed_report = analyze_path_with_options(fixed.path(), &at_128_options);
    assert!(fixed_report.findings.iter().all(|finding| {
        !(finding.struct_name.as_deref() == Some("Ring")
            && finding.field_list.contains(&"head".to_string())
            && finding.field_list.contains(&"flush".to_string()))
    }));
}

// --- indexed_writes: Parallel indexed write ---

#[test]
fn indexed_writes_cold_or_conditional_for_parallel_self_indexed_write() {
    let dir = setup_test_dir(
        "indexed_writes",
        &[(
            "src/lib.rs",
            r#"
struct SharedState {
    shards: Vec<u64>,
}

impl SharedState {
    fn update(&mut self, indexes: Vec<usize>) {
        indexes.par_iter().for_each(|idx| {
            self.shards[*idx] = 42;
        });
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);

    let writer_neighbor: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.candidate_kind == "indexed_writes")
        .collect();
    assert!(!writer_neighbor.is_empty(), "should detect indexed_writes");
    assert!(
        writer_neighbor
            .iter()
            .all(|f| f.category == RiskCategory::ColdOrConditional)
    );
}

#[test]
fn indexed_writes_ignores_local_array_inside_spawn() {
    let dir = setup_test_dir(
        "indexed_writes_local",
        &[(
            "src/lib.rs",
            r#"
fn example() {
    std::thread::spawn(|| {
        let mut result = [0u32; 4];
        result[0] = 1;
    });
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "indexed_writes"),
        "local arrays in spawned closures should not be treated as shared indexed writes"
    );
}

// --- container_elements/writer_neighbor/object_instances: cache-sensitive layout rules ---

#[test]
fn container_elements_detects_unpadded_sharded_lock_container() {
    let dir = setup_test_dir(
        "container_elements_shards",
        &[(
            "src/lib.rs",
            r#"
use std::sync::RwLock;
use std::collections::HashMap;

pub struct DashMap<K, V> {
    shift: usize,
    shards: Box<[RwLock<HashMap<K, V>>]>,
}

impl<K, V> DashMap<K, V> {
    pub fn get(&self, index: usize, _key: &K) -> Option<&V> {
        let _guard = self.shards[index].read().unwrap();
        None
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);

    let indexed_writes: Vec<_> = report
        .findings
        .iter()
        .filter(|f| {
            f.candidate_kind == "container_elements" && f.struct_name.as_deref() == Some("DashMap")
        })
        .collect();
    assert!(
        !indexed_writes.is_empty(),
        "should detect unpadded sharded locks"
    );
    assert!(
        indexed_writes
            .iter()
            .any(|f| f.field_list.contains(&"shards".into()))
    );
}

#[test]
fn container_elements_ignores_cache_padded_sharded_lock_container() {
    let dir = setup_test_dir(
        "container_elements_padded_shards",
        &[(
            "src/lib.rs",
            r#"
use std::sync::RwLock;
use std::collections::HashMap;

#[repr(align(64))]
struct CachePadded<T>(T);

struct DashMap<K, V> {
    shift: usize,
    shards: Box<[CachePadded<RwLock<HashMap<K, V>>>]>,
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "container_elements"),
        "CachePadded sharded locks should not trigger container_elements"
    );
}

#[test]
fn container_elements_suppresses_single_mutex_vec_container() {
    let dir = setup_test_dir(
        "container_elements_mutex_vec",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Mutex;

pub struct Reporter {
    queue: Mutex<Vec<u64>>,
}

impl Reporter {
    pub fn push(&self, value: u64) {
        self.queue.lock().unwrap().push(value);
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| !(f.candidate_kind == "container_elements"
                && f.field_list.contains(&"queue".to_string()))),
        "a single Mutex<Vec<T>> guards the whole container and should not be treated as sharded slots"
    );
}

#[test]
fn container_elements_reports_vec_of_mutex_shards_when_elements_are_independent() {
    let dir = setup_test_dir(
        "container_elements_vec_mutex_shards",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Mutex;

pub struct Sharded {
    shards: Vec<Mutex<u64>>,
}

impl Sharded {
    pub fn get(&self, idx: usize) -> u64 {
        *self.shards[idx].lock().unwrap()
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .any(|f| f.candidate_kind == "container_elements"
                && f.field_list.contains(&"shards".to_string())),
        "Vec<Mutex<T>> exposes independently locked contiguous elements and should remain detectable"
    );
}

#[test]
fn container_elements_ignores_plain_numeric_histogram() {
    let dir = setup_test_dir(
        "container_elements_plain_histogram",
        &[(
            "src/lib.rs",
            r#"
struct Histogram {
    buckets: Vec<u64>,
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "container_elements"),
        "plain numeric containers are too broad for low-noise container_elements"
    );
}

#[test]
fn container_elements_detects_indexed_atomic_inside_boxed_tuple_array() {
    let dir = setup_test_dir(
        "container_elements_boxed_tuple_atomic",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

trait HistogramFn {
    fn record(&self, value: usize);
}

struct Histogram {
    buckets: Box<[(f64, AtomicU32); 26]>,
}

impl HistogramFn for Histogram {
    fn record(&self, value: usize) {
        self.buckets[value % 26].1.fetch_add(1, Ordering::Relaxed);
    }
}

struct Storage;

impl Storage {
    fn histogram(&self) -> Arc<Histogram> {
        unimplemented!()
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report.findings.iter().any(|finding| {
            finding.candidate_kind == "container_elements"
                && finding.struct_name.as_deref() == Some("Histogram")
                && finding.field_list == ["buckets"]
        }),
        "a shared boxed tuple array with an indexed atomic projection is a contiguous-element risk"
    );
}

#[test]
fn field_group_treats_generic_get_as_read_not_rmw() {
    let dir = setup_test_dir(
        "field_group_generic_get_is_read",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;

struct Setting(u64);

impl Setting {
    fn get(&self) -> u64 { self.0 }
}

pub struct Config {
    first: Setting,
    second: Setting,
}

pub async fn serve(config: Arc<Config>) {
    let _ = config.first.get();
    let _ = config.second.get();
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|finding| finding.struct_name.as_deref() != Some("Config")),
        "a generic get accessor is read-only and cannot establish HasWrite"
    );
}

#[test]
fn field_group_suppresses_owned_clone_moved_to_each_task() {
    let dir = setup_test_dir(
        "field_group_owned_clone_per_task",
        &[(
            "src/lib.rs",
            r#"
#[derive(Clone)]
struct Request {
    offset: usize,
    limit: usize,
}

fn launch(request: &Request) {
    for _ in 0..4 {
        let mut local = request.clone();
        std::thread::spawn(move || {
            local.offset = 0;
            local.limit = 10;
        });
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|finding| finding.struct_name.as_deref() != Some("Request")),
        "independent owned clones transferred to tasks do not share one object"
    );
}

#[test]
fn field_group_suppresses_exclusive_object_inside_concurrent_task() {
    let dir = setup_test_dir(
        "field_group_exclusive_task_object",
        &[(
            "src/lib.rs",
            r#"
struct TaskState {
    accepted: usize,
    rejected: usize,
}

fn launch(mut state: TaskState) {
    std::thread::spawn(move || {
        state.accepted += 1;
        state.rejected += 1;
    });
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|finding| finding.struct_name.as_deref() != Some("TaskState")),
        "concurrent execution does not defeat exclusive ownership of one moved object"
    );
}

#[test]
fn indexed_writes_suppresses_buffer_allocated_inside_parallel_closure() {
    let dir = setup_test_dir(
        "indexed_writes_agent_local_vec",
        &[(
            "src/lib.rs",
            r#"
fn launch() {
    std::thread::scope(|scope| {
        for worker in 0..4 {
            scope.spawn(move || {
                let mut current_depths = vec![0u8; 64];
                if worker < current_depths.len() {
                    current_depths[worker] = 1;
                }
            });
        }
    });
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|finding| finding.candidate_kind != "indexed_writes"),
        "a buffer allocated inside each worker closure is agent-local"
    );
}

#[test]
fn container_elements_ignores_plain_priority_map_scalar_array() {
    let dir = setup_test_dir(
        "container_elements_priority_map_scalar_array",
        &[(
            "src/lib.rs",
            r#"
enum IOPriority {
    Low,
    High,
}

enum IOType {
    Flush,
}

struct IORateLimiter {
    priority_map: [IOPriority; 2],
}

impl IORateLimiter {
    fn set_io_priority(&mut self, io_type: IOType, io_priority: IOPriority) {
        self.priority_map[io_type as usize] = io_priority;
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::all_rules();
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report.findings.iter().all(|f| {
            !f.field_list.contains(&"priority_map".to_string())
                && f.symbol.as_deref() != Some("IORateLimiter.priority_map")
        }),
        "plain enum array with &mut self setter should remain outside strict static detection"
    );
}

#[test]
fn static_data_detects_static_lock_array() {
    let dir = setup_test_dir(
        "static_data_static_array",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicUsize, Ordering};
struct SeqLock(AtomicUsize);
impl SeqLock { fn write(&self) { self.0.fetch_add(1, Ordering::Relaxed); } }
fn lock(addr: usize) -> &'static SeqLock {
    static LOCKS: [SeqLock; 97] = [const { SeqLock(AtomicUsize::new(0)) }; 97];
    &LOCKS[addr % 97]
}
pub fn update(addr: usize) { lock(addr).write(); }
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .any(|f| f.candidate_kind == "static_data" && f.field_list.contains(&"LOCKS".into())),
        "static lock arrays should trigger static_data"
    );
}

#[test]
fn static_data_ignores_adjacent_singletons_without_mutable_payload_or_access() {
    let dir = setup_test_dir(
        "static_data_static_singletons",
        &[(
            "src/lib.rs",
            r#"
use std::sync::{LazyLock, OnceLock};

struct Harness;

static HARNESS: OnceLock<Harness> = OnceLock::new();
static NOOP_HARNESS: LazyLock<Harness> = LazyLock::new(|| Harness);
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "static_data"),
        "adjacent OnceLock/LazyLock statics without mutable payload or access evidence are too broad to report"
    );
}

#[test]
fn static_data_ignores_singleton_without_concrete_neighbor_even_with_init_write() {
    let dir = setup_test_dir(
        "static_data_static_singleton_access",
        &[(
            "src/lib.rs",
            r#"
use std::sync::OnceLock;

struct Harness;

static HARNESS: OnceLock<Harness> = OnceLock::new();

pub fn install_harness() {
    let _ = HARNESS.set(Harness);
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "static_data"),
        "one singleton without a concrete second location cannot establish false sharing"
    );
}

#[test]
fn static_data_ignores_hot_singleton_static_with_read_only_access() {
    let dir = setup_test_dir(
        "static_data_static_singleton_read_only_access",
        &[(
            "src/lib.rs",
            r#"
use std::sync::OnceLock;

struct Harness;

static HARNESS: OnceLock<Harness> = OnceLock::new();

pub fn harness() -> Option<&'static Harness> {
    HARNESS.get()
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "static_data"),
        "plain read/get access to a singleton static should not trigger static_data"
    );
}

#[test]
fn static_data_ignores_business_method_names_on_plain_singleton_payload() {
    let dir = setup_test_dir(
        "static_data_static_singleton_plain_payload_write_method",
        &[(
            "src/lib.rs",
            r#"
use std::sync::LazyLock;

struct Harness;

impl Harness {
    pub fn write(&self) {}
}

static HARNESS: LazyLock<Harness> = LazyLock::new(|| Harness);

pub fn harness() {
    HARNESS.write();
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "static_data"),
        "method names such as write must not trigger without a sync/atomic/cell payload type"
    );
}

#[test]
fn static_data_ignores_atomic_word_inside_plain_payload_type_name() {
    let dir = setup_test_dir(
        "static_data_static_singleton_plain_atomic_name_payload",
        &[(
            "src/lib.rs",
            r#"
use std::sync::LazyLock;

struct AtomicStats {
    value: usize,
}

static STATS: LazyLock<AtomicStats> = LazyLock::new(|| AtomicStats { value: 0 });
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "static_data"),
        "payload type names containing Atomic are not atomic payload evidence"
    );
}

#[test]
fn static_data_suppresses_adjacent_singletons_without_access_witnesses() {
    let dir = setup_test_dir(
        "static_data_static_singletons_mutable_payload",
        &[(
            "src/lib.rs",
            r#"
use std::sync::{LazyLock, Mutex, OnceLock};
use std::sync::atomic::AtomicU64;

struct Harness {
    calls: AtomicU64,
}

static HARNESS: OnceLock<Harness> = OnceLock::new();
static NOOP_HARNESS: LazyLock<Mutex<Harness>> = LazyLock::new(|| {
    Mutex::new(Harness { calls: AtomicU64::new(0) })
});
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "static_data")
    );
}

#[test]
fn static_data_detects_two_accessed_static_sync_locations() {
    let dir = setup_test_dir(
        "static_data_accessed_singletons",
        &[(
            "src/lib.rs",
            r#"
use std::sync::{LazyLock, OnceLock};
use std::sync::atomic::{AtomicU64, Ordering};

static LEFT: OnceLock<AtomicU64> = OnceLock::new();
static RIGHT: LazyLock<AtomicU64> = LazyLock::new(|| AtomicU64::new(0));

pub fn update() {
    let _ = LEFT.set(AtomicU64::new(1));
    RIGHT.fetch_add(1, Ordering::Relaxed);
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.candidate_kind == "static_data")
        .expect("two accessed static locations should form a static-storage pattern");
    let pattern = finding.static_pattern.as_ref().expect("pattern witness");
    assert_eq!(pattern.colocation_pattern, ColocationPattern::StaticStorage);
    assert_eq!(pattern.access_pattern, AccessPattern::WriteWrite);
}

#[test]
fn static_data_detects_static_singleton_write_read_interference() {
    let dir = setup_test_dir(
        "static_data_accessed_singleton_write_read",
        &[(
            "src/lib.rs",
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
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.candidate_kind == "static_data")
        .expect("a written singleton and accessed read-only peer form a W-R pattern");
    let pattern = finding.static_pattern.as_ref().expect("pattern witness");
    assert_eq!(pattern.access_pattern, AccessPattern::WriteRead);
    assert!(finding.field_list.contains(&"PRIMARY".to_string()));
    assert!(finding.field_list.contains(&"FALLBACK".to_string()));
}

#[test]
fn static_data_suppresses_two_read_only_singletons() {
    let dir = setup_test_dir(
        "static_data_read_only_singleton_pair",
        &[(
            "src/lib.rs",
            r#"
use std::sync::OnceLock;

struct Config;

static LEFT: OnceLock<Config> = OnceLock::new();
static RIGHT: OnceLock<Config> = OnceLock::new();

pub fn read_both() {
    let _ = LEFT.get();
    let _ = RIGHT.get();
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);
    assert!(
        report
            .findings
            .iter()
            .all(|finding| finding.candidate_kind != "static_data")
    );
}

#[test]
fn static_data_ignores_cache_padded_hot_singleton_statics() {
    let dir = setup_test_dir(
        "static_data_padded_static_singletons",
        &[(
            "src/lib.rs",
            r#"
use std::sync::{LazyLock, OnceLock};

#[repr(align(64))]
struct CachePadded<T>(T);
struct Harness;

static HARNESS: CachePadded<OnceLock<Harness>> = CachePadded(OnceLock::new());
static NOOP_HARNESS: CachePadded<LazyLock<Harness>> = CachePadded(LazyLock::new(|| Harness));
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "static_data"),
        "CachePadded singleton statics should not trigger static_data"
    );
}

#[test]
fn static_data_ignores_single_ordinary_once_lock_static() {
    let dir = setup_test_dir(
        "static_data_single_once_lock",
        &[(
            "src/lib.rs",
            r#"
use std::sync::OnceLock;

struct Config;

static CONFIG: OnceLock<Config> = OnceLock::new();
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "static_data"),
        "a single ordinary OnceLock static is too broad to report"
    );
}

#[test]
fn object_instances_ignores_cfg_attr_repr_align_object() {
    let dir = setup_test_dir(
        "object_instances_repr_align",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicUsize;
use std::cell::UnsafeCell;
use std::sync::Mutex;

#[cfg_attr(target_arch = "x86_64", repr(align(128)))]
#[repr(C)]
struct ScheduledIo {
    linked_list_pointers: UnsafeCell<usize>,
    readiness: AtomicUsize,
    waiters: Mutex<usize>,
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "object_instances"),
        "cfg_attr repr(align) should be treated as cache-line protection"
    );
}

#[test]
fn object_instances_requires_recovered_contiguous_storage_not_cell_name() {
    let dir = setup_test_dir(
        "object_instances_recursive_cell",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicUsize;
use std::cell::UnsafeCell;

struct State(AtomicUsize);

struct Header {
    state: State,
}

struct Core {
    stage: UnsafeCell<usize>,
}

struct Trailer {
    owned: AtomicUsize,
}

pub struct Cell {
    header: Header,
    core: Core,
    trailer: Trailer,
}

impl Cell {
    pub fn poll(&self) {}
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| !(f.candidate_kind == "object_instances"
                && f.struct_name.as_deref() == Some("Cell"))),
        "a type name and nested hot payload do not prove adjacent object instances"
    );
}

#[test]
fn object_instances_detects_hot_type_used_as_contiguous_element() {
    let dir = setup_test_dir(
        "object_instances_contiguous_element",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct WorkerState {
    state: AtomicUsize,
    payload: usize,
}

impl WorkerState {
    pub fn advance(&self) {
        self.state.fetch_add(1, Ordering::Relaxed);
    }
}

struct Pool {
    workers: Vec<WorkerState>,
}

fn schedule(worker: Arc<WorkerState>) {
    std::thread::spawn(move || worker.advance());
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|finding| {
            finding.candidate_kind == "object_instances"
                && finding.struct_name.as_deref() == Some("WorkerState")
        })
        .expect("Vec<WorkerState> should establish the adjacent-object topology");
    let pattern = finding.static_pattern.as_ref().expect("pattern witness");
    assert_eq!(
        pattern.colocation_pattern,
        ColocationPattern::AdjacentObjects
    );
    assert_eq!(pattern.access_pattern, AccessPattern::WriteWrite);
}

#[test]
fn object_instances_lifts_nested_hot_access_for_type_erased_allocator_objects() {
    let dir = setup_test_dir(
        "object_instances_type_erased_nested_hot_access",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicUsize, Ordering};

struct Header {
    epoch: AtomicUsize,
}

impl Header {
    fn advance(&self) {
        self.epoch.fetch_add(1, Ordering::Relaxed);
    }
}

struct Payload {
    value: usize,
}

struct Allocation {
    header: Header,
    payload: Payload,
}

fn allocate() -> *mut Allocation {
    Box::into_raw(Box::new(Allocation {
        header: Header { epoch: AtomicUsize::new(0) },
        payload: Payload { value: 0 },
    }))
}

unsafe fn update(pointer: *mut Allocation) {
    unsafe { (*pointer).header.advance() };
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|finding| {
            finding.candidate_kind == "object_instances"
                && finding.struct_name.as_deref() == Some("Allocation")
        })
        .expect("allocator escape should lift nested write evidence to its parent object");
    let pattern = finding.static_pattern.as_ref().expect("pattern witness");
    assert_eq!(
        pattern.colocation_pattern,
        ColocationPattern::AllocatorObjects
    );
    assert!(finding.field_list.contains(&"header".to_string()));
}

#[test]
fn object_instances_ignores_cell_when_nested_hot_types_are_aligned() {
    let dir = setup_test_dir(
        "object_instances_recursive_aligned",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicUsize;
use std::cell::UnsafeCell;

#[repr(align(64))]
struct Header {
    state: AtomicUsize,
}

#[repr(align(64))]
struct Core {
    stage: UnsafeCell<usize>,
}

#[repr(align(64))]
struct Trailer {
    owned: AtomicUsize,
}

struct Cell {
    header: Header,
    core: Core,
    trailer: Trailer,
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| !(f.candidate_kind == "object_instances"
                && f.struct_name.as_deref() == Some("Cell"))),
        "aligned nested types should not be propagated as unisolated hot payload"
    );
}

// --- File-level and hotness rules ---

#[test]
fn object_instances_suppresses_single_write_once_static_mut() {
    let dir = setup_test_dir(
        "object_instances_single_static_mut",
        &[(
            "src/lib.rs",
            r#"
static mut COUNTER: usize = 0;
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "object_instances"),
        "a single static mut is true-sharing/data-race shaped, not enough for false-sharing"
    );
}

#[test]
fn object_instances_does_not_report_adjacent_static_mut_items() {
    let dir = setup_test_dir(
        "object_instances_adjacent_static_mut",
        &[(
            "src/lib.rs",
            r#"
static mut READ_COUNT: usize = 0;
static mut WRITE_COUNT: usize = 0;
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "object_instances"),
        "old static mut adjacency rule is deleted; static arrays/singletons are handled by static_data"
    );
}

#[test]
fn sibling_arrays_single_atomic_loop_does_not_emit_standalone_finding() {
    let dir = setup_test_dir(
        "sibling_arrays_cold_or_conditional",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicU64, Ordering};

struct Counter {
    value: AtomicU64,
}

impl Counter {
    fn spin(&self) {
        for _ in 0..1000001 {
            self.value.fetch_add(1, Ordering::Relaxed);
        }
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::all_rules();
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "sibling_arrays"),
        "loop hotness should only strengthen other layout findings, not emit standalone sibling_arrays"
    );
}

#[test]
fn sibling_arrays_hot_loop_without_layout_pair_does_not_emit_standalone_finding() {
    let dir = setup_test_dir(
        "sibling_arrays_no_layout_pair",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicU64, Ordering};

struct Counter {
    value: AtomicU64,
}

impl Counter {
    fn spin(&self) {
        std::thread::spawn(|| {});
        for _ in 0..1000001 {
            self.value.fetch_add(1, Ordering::Relaxed);
        }
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::all_rules();
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "sibling_arrays"),
        "sibling_arrays loop hotness evidence should not become a standalone finding"
    );
}

// --- Access path / alias evidence ---

#[test]
fn access_path_detects_parameter_variable_atomic_ops() {
    let dir = setup_test_dir(
        "access_path_param",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

struct SharedCounters {
    reads: AtomicU64,
    writes: AtomicU64,
}

pub fn update_reads(shared: Arc<SharedCounters>) {
    shared.reads.fetch_add(1, Ordering::Relaxed);
}

pub fn update_writes(shared: Arc<SharedCounters>) {
    shared.writes.fetch_add(1, Ordering::Relaxed);
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|f| {
            f.candidate_kind == "field_group" && f.struct_name.as_deref() == Some("SharedCounters")
        })
        .expect("parameter access should attach writes to SharedCounters");

    assert!(
        finding
            .concurrency_evidence
            .iter()
            .any(|e| e.contains("shared.reads")),
        "evidence should include concrete parameter access path"
    );
}

#[test]
fn access_path_detects_arc_clone_and_reference_aliases() {
    let dir = setup_test_dir(
        "access_path_aliases",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

struct SharedCounters {
    reads: AtomicU64,
    writes: AtomicU64,
}

pub fn update_reads(shared: Arc<SharedCounters>) {
    let cloned = Arc::clone(&shared);
    let alias = &cloned;
    alias.reads.fetch_add(1, Ordering::Relaxed);
}

pub fn update_writes(shared: Arc<SharedCounters>) {
    let cloned = Arc::clone(&shared);
    cloned.writes.fetch_add(1, Ordering::Relaxed);
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|f| {
            f.candidate_kind == "field_group" && f.struct_name.as_deref() == Some("SharedCounters")
        })
        .expect("alias access should attach writes to SharedCounters");

    assert!(
        finding
            .concurrency_evidence
            .iter()
            .any(|e| e.contains("alias.reads")),
        "reference alias should be resolved in evidence"
    );
    assert!(
        finding
            .concurrency_evidence
            .iter()
            .any(|e| e.contains("cloned.writes")),
        "Arc clone alias should be resolved in evidence"
    );
}

#[test]
fn points_to_alias_unwraps_option_arc_in_if_let() {
    let dir = setup_test_dir(
        "points_to_option_arc_if_let",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

struct SharedCounters {
    left: AtomicU64,
    right: AtomicU64,
}

struct Worker {
    counters: Option<Arc<SharedCounters>>,
}

fn update_left(worker: &Worker) {
    if let Some(ref counters) = worker.counters {
        counters.left.fetch_add(1, Ordering::Relaxed);
    }
}

fn update_right(worker: &Worker) {
    if let Some(ref counters) = worker.counters {
        counters.right.fetch_add(1, Ordering::Relaxed);
    }
}
"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("SharedCounters"))
        .expect("Option<Arc<T>> destructuring should preserve the points-to target");
    assert!(finding.field_list.iter().any(|field| field == "left"));
    assert!(finding.field_list.iter().any(|field| field == "right"));
    assert!(finding.access_evidence.iter().any(|evidence| {
        evidence.field_name.as_deref() == Some("left") && evidence.through_shared_indirection
    }));
}

#[test]
fn access_path_detects_nested_and_indexed_atomic_ops() {
    let dir = setup_test_dir(
        "access_path_nested_indexed",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

struct Inner {
    a: AtomicU64,
    b: AtomicU64,
}

struct Outer {
    inner: Inner,
    counters: Vec<AtomicU64>,
}

pub fn update_a(outer: Arc<Outer>) {
    outer.inner.a.fetch_add(1, Ordering::Relaxed);
}

pub fn update_b(outer: Arc<Outer>) {
    outer.inner.b.fetch_add(1, Ordering::Relaxed);
}

pub fn update_counter(outer: Arc<Outer>, index: usize) {
    outer.counters[index].fetch_add(1, Ordering::Relaxed);
}
"#,
        )],
    );

    let options =
        AnalysisOptions::with_rules(&[RuleId::SameObjectFields, RuleId::ContiguousElements]);
    let report = analyze_path_with_options(dir.path(), &options);
    let inner = report
        .findings
        .iter()
        .find(|f| f.candidate_kind == "field_group" && f.struct_name.as_deref() == Some("Inner"))
        .expect("nested access should resolve to Inner");

    assert!(
        inner
            .concurrency_evidence
            .iter()
            .any(|e| e.contains("outer.inner.a")),
        "nested evidence should include full access path"
    );
    assert!(
        report.findings.iter().any(|f| {
            f.concurrency_evidence
                .iter()
                .any(|e| e.contains("outer.counters"))
        }),
        "indexed atomic access should be recorded on the container field"
    );
}

#[test]
fn access_path_detects_wrapper_field_chain_atomic_ops() {
    let dir = setup_test_dir(
        "access_path_wrapper_field_chain",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

struct HotState {
    active_connections: AtomicU64,
    active_requests: AtomicU64,
}

struct ConnectionGuard {
    state: Arc<HotState>,
}

struct RequestGuard {
    state: Arc<HotState>,
}

impl ConnectionGuard {
    fn open(&self) {
        self.state.active_connections.fetch_add(1, Ordering::Relaxed);
    }
}

impl RequestGuard {
    fn open(&self) {
        self.state.active_requests.fetch_add(1, Ordering::Relaxed);
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|f| f.candidate_kind == "field_group" && f.struct_name.as_deref() == Some("HotState"))
        .expect("Arc<T> field chain should attach guard writes to HotState");

    assert!(
        finding
            .concurrency_evidence
            .iter()
            .any(|e| e.contains("self.state.active_connections")),
        "evidence should include wrapper field access path"
    );
}

#[test]
fn field_group_detects_atomic_run_before_unknown_sized_field() {
    let dir = setup_test_dir(
        "field_group_atomic_run_unknown_field",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

mod tokio {
    pub mod sync {
        pub struct Notify;
    }
}

pub struct RuntimeState {
    reject_new_requests: AtomicBool,
    active_connections: AtomicU64,
    active_requests: AtomicU64,
    drain_complete: tokio::sync::Notify,
    rare_snapshot: AtomicU64,
}

pub struct ConnectionGuard {
    state: Arc<RuntimeState>,
}

pub struct RequestGuard {
    state: Arc<RuntimeState>,
}

impl ConnectionGuard {
    fn new(state: &Arc<RuntimeState>) -> Self {
        state.active_connections.fetch_add(1, Ordering::Relaxed);
        Self { state: Arc::clone(state) }
    }
}

impl Drop for ConnectionGuard {
    fn drop(&mut self) {
        self.state.active_connections.fetch_sub(1, Ordering::Relaxed);
    }
}

impl RequestGuard {
    fn new(state: &Arc<RuntimeState>) -> Self {
        state.active_requests.fetch_add(1, Ordering::Relaxed);
        Self { state: Arc::clone(state) }
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report.findings.iter().any(|f| {
            f.candidate_kind == "field_group" && f.struct_name.as_deref() == Some("RuntimeState")
        }),
        "a contiguous hot atomic run should be layout evidence even when a later field has unknown size"
    );
}

#[test]
fn field_group_ignores_cold_remainder_after_hot_fields_are_cache_padded() {
    let dir = setup_test_dir(
        "field_group_padded_hot_state_cold_remainder",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

#[repr(align(64))]
struct CachePadded<T>(T);

pub struct RuntimeState {
    reject_new_requests: CachePadded<AtomicBool>,
    active_connections: CachePadded<AtomicU64>,
    active_requests: CachePadded<AtomicU64>,
    draining: AtomicBool,
    fd_current: AtomicU64,
    fd_max: AtomicU64,
    conn_current: AtomicU64,
    conn_max: AtomicU64,
    req_current: AtomicU64,
    req_max: AtomicU64,
    loop_latency_us: AtomicU64,
    port_exhaustion_events: AtomicU64,
}

impl RuntimeState {
    pub fn snapshot(&self) {
        let _ = self.fd_current.load(Ordering::Relaxed);
        let _ = self.fd_max.load(Ordering::Relaxed);
        let _ = self.conn_current.load(Ordering::Relaxed);
        let _ = self.conn_max.load(Ordering::Relaxed);
        let _ = self.req_current.load(Ordering::Relaxed);
        let _ = self.req_max.load(Ordering::Relaxed);
        let _ = self.loop_latency_us.load(Ordering::Relaxed);
        let _ = self.port_exhaustion_events.load(Ordering::Relaxed);
    }
}

pub fn monitor(state: Arc<RuntimeState>) {
    std::thread::spawn(move || {
        state.fd_current.store(1, Ordering::Relaxed);
        state.conn_current.store(1, Ordering::Relaxed);
        state.req_current.store(1, Ordering::Relaxed);
        state.loop_latency_us.store(1, Ordering::Relaxed);
    });
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report.findings.iter().all(|finding| {
            finding.candidate_kind != "field_group"
                || finding.struct_name.as_deref() != Some("RuntimeState")
        }),
        "the remaining fields are jointly touched by the same monitor/snapshot roles, so they do not establish independently addressable false sharing"
    );
}

#[test]
fn access_path_suppresses_exclusive_compound_assignment_writes() {
    let dir = setup_test_dir(
        "access_path_compound",
        &[(
            "src/lib.rs",
            r#"
struct HotCounters {
    hit_count: u64,
    miss_count: u64,
}

impl HotCounters {
    pub fn update_hit(&mut self) {
        self.hit_count += 1;
    }
    pub fn update_miss(&mut self) {
        self.miss_count += 1;
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| !(f.candidate_kind == "field_group"
                && f.struct_name.as_deref() == Some("HotCounters"))),
        "exclusive compound assignments should be treated like &mut-only value state, not false sharing"
    );
}

#[test]
fn access_path_local_struct_without_known_type_is_not_misattributed() {
    let dir = setup_test_dir(
        "access_path_local_negative",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicU64, Ordering};

struct SharedCounters {
    reads: AtomicU64,
    writes: AtomicU64,
}

fn update() {
    let local = SharedCounters {
        reads: AtomicU64::new(0),
        writes: AtomicU64::new(0),
    };
    local.reads.fetch_add(1, Ordering::Relaxed);
    local.writes.fetch_add(1, Ordering::Relaxed);
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);
    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "field_group"),
        "untyped local struct literal should not create shared access evidence or a layout-only finding"
    );
}

#[test]
fn finding_contains_symbol_and_risk_factors() {
    let dir = setup_test_dir(
        "finding_symbol",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicU64;

pub struct Counters {
    a: AtomicU64,
    b: AtomicU64,
}

impl Counters {
    pub fn increment_a(&self) {
        self.a.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    pub fn read_b(&self) -> u64 {
        self.b.load(std::sync::atomic::Ordering::Relaxed)
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);
    let finding = report
        .findings
        .iter()
        .find(|f| f.candidate_kind == "field_group")
        .expect("field_group finding");

    assert_eq!(finding.symbol.as_deref(), Some("Counters"));
    let layout_context = finding
        .layout_context
        .as_ref()
        .expect("struct findings should include layout_context");
    assert_eq!(layout_context.language, "rust");
    assert_eq!(layout_context.struct_name, "Counters");
    assert!(
        layout_context
            .cache_line_groups
            .iter()
            .any(|group| group.contains(&"a".to_string()) && group.contains(&"b".to_string())),
        "layout_context should expose cache-line groups"
    );
    assert!(
        layout_context
            .fields
            .iter()
            .any(|field| field.name == "a" && field.offset.is_none() && field.cache_line.is_none()),
        "repr(Rust) source estimates must not invent compiler-controlled field offsets"
    );
    assert!(!layout_context.cache_line_groups_precise);
    assert!(
        finding
            .risk_factors
            .iter()
            .any(|factor| factor.contains("布局证据")),
        "findings should explain the evidence dimensions behind the risk"
    );
    assert!(
        finding.access_evidence.iter().any(|evidence| {
            evidence.field_name.as_deref() == Some("a")
                && evidence.access_kind.as_deref() == Some("read_modify_write")
        }),
        "findings should expose structured access evidence for runtime adapters"
    );
    assert_eq!(
        report.schema_version,
        false_sharing_detector::types::REPORT_SCHEMA_VERSION
    );
}

#[test]
fn thread_local_cell_does_not_emit_atomic_array_or_info() {
    let dir = setup_test_dir(
        "atomic_array",
        &[(
            "src/lib.rs",
            r#"
use std::cell::Cell;

thread_local! {
    static COUNTER: Cell<u64> = Cell::new(0);
}
"#,
        )],
    );

    let options = AnalysisOptions::all_rules();
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "atomic_array"),
        "atomic_array was removed and TLS + Cell should not emit info findings"
    );
}

#[test]
fn interprocedural_summary_propagates_cross_file_spawn_accesses() {
    let dir = setup_test_dir(
        "interprocedural_cross_file_spawn",
        &[
            (
                "src/lib.rs",
                r#"
mod counters;
mod workers;
"#,
            ),
            (
                "src/counters.rs",
                r#"
use std::sync::atomic::{AtomicU64, Ordering};

pub struct Counters {
    left: AtomicU64,
    right: AtomicU64,
}

impl Counters {
    pub(crate) fn inc_left(&self) {
        self.left.fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn inc_right(&self) {
        self.right.fetch_add(1, Ordering::Relaxed);
    }
}
"#,
            ),
            (
                "src/workers.rs",
                r#"
use std::sync::Arc;
use crate::counters::Counters;

fn leaf_left(state: &Counters) { state.inc_left(); }
fn leaf_right(state: &Counters) { state.inc_right(); }
fn middle_left(state: &Counters) { leaf_left(state); }
fn middle_right(state: &Counters) { leaf_right(state); }

pub fn dispatch(left: Arc<Counters>, right: Arc<Counters>) {
    std::thread::spawn(move || middle_left(&left));
    std::thread::spawn(move || middle_right(&right));
}
"#,
            ),
        ],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("Counters"))
        .expect("cross-file function summaries should reach the candidate struct");

    for field in ["left", "right"] {
        assert!(finding.access_evidence.iter().any(|evidence| {
            evidence.field_name.as_deref() == Some(field)
                && evidence.in_concurrent_context
                && evidence.propagation_depth == 3
                && evidence
                    .call_path
                    .iter()
                    .any(|item| item.contains("dispatch"))
        }));
    }
    assert_eq!(finding.category, RiskCategory::HotInProject);

    let mut intraprocedural = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    intraprocedural.use_interprocedural_evidence = false;
    let intraprocedural_report = analyze_path_with_options(dir.path(), &intraprocedural);
    assert!(intraprocedural_report.findings.iter().all(|finding| {
        finding
            .access_evidence
            .iter()
            .all(|evidence| evidence.propagation_depth == 0)
    }));
}

#[test]
fn lifecycle_trait_generic_delegation_reaches_shared_inner_state() {
    let dir = setup_test_dir(
        "lifecycle_trait_generic",
        &[(
            "src/lib.rs",
            r#"
use std::marker::PhantomData;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct Shared {
    sender_count: AtomicUsize,
    receiver_count: AtomicUsize,
}

impl Shared {
    fn add_sender(&self) { self.sender_count.fetch_add(1, Ordering::Relaxed); }
    fn remove_sender(&self) { self.sender_count.fetch_sub(1, Ordering::Relaxed); }
    fn add_receiver(&self) { self.receiver_count.fetch_add(1, Ordering::Relaxed); }
    fn remove_receiver(&self) { self.receiver_count.fetch_sub(1, Ordering::Relaxed); }
}

pub struct Sender<T> { shared: Arc<Shared>, marker: PhantomData<T> }
pub struct Receiver<T> { shared: Arc<Shared>, marker: PhantomData<T> }

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        self.shared.add_sender();
        Self { shared: Arc::clone(&self.shared), marker: PhantomData }
    }
}
impl<T> Drop for Sender<T> {
    fn drop(&mut self) { self.shared.remove_sender(); }
}
impl<T> Clone for Receiver<T> {
    fn clone(&self) -> Self {
        self.shared.add_receiver();
        Self { shared: Arc::clone(&self.shared), marker: PhantomData }
    }
}
impl<T> Drop for Receiver<T> {
    fn drop(&mut self) { self.shared.remove_receiver(); }
}
"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("Shared"))
        .expect("Clone/Drop delegation should expose shared lifecycle writes");

    assert!(finding.access_evidence.iter().any(|evidence| {
        evidence.propagation_depth == 1
            && evidence.through_shared_indirection
            && evidence.in_concurrent_context
            && evidence
                .semantic_contexts
                .iter()
                .any(|item| item == "trait_impl")
            && evidence
                .semantic_contexts
                .iter()
                .any(|item| item == "generic")
            && evidence
                .semantic_contexts
                .iter()
                .any(|item| item == "clone_impl")
            && evidence
                .semantic_contexts
                .iter()
                .any(|item| item == "handle_lifecycle")
    }));
    assert!(finding.access_evidence.iter().any(|evidence| {
        evidence.propagation_depth == 1
            && evidence
                .semantic_contexts
                .iter()
                .any(|item| item == "drop_impl")
    }));
}

#[test]
fn async_spawn_propagates_helper_access_but_plain_async_is_not_parallel_by_itself() {
    let dir = setup_test_dir(
        "async_interprocedural",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

mod tokio { pub fn spawn<T>(_task: T) {} }

pub struct AsyncCounters {
    left: AtomicU64,
    right: AtomicU64,
}

fn left_leaf(state: &AsyncCounters) { state.left.fetch_add(1, Ordering::Relaxed); }
fn right_leaf(state: &AsyncCounters) { state.right.fetch_add(1, Ordering::Relaxed); }
async fn left_task(state: Arc<AsyncCounters>) { left_leaf(&state); }
async fn right_task(state: Arc<AsyncCounters>) { right_leaf(&state); }

pub fn launch(left: Arc<AsyncCounters>, right: Arc<AsyncCounters>) {
    tokio::spawn(async move { left_task(left).await; });
    tokio::spawn(async move { right_task(right).await; });
}

struct ExclusiveCounters {
    first: AtomicU64,
    second: AtomicU64,
}

async fn configure_exclusively(value: &mut ExclusiveCounters) {
    value.first.fetch_add(1, Ordering::Relaxed);
    value.second.fetch_add(1, Ordering::Relaxed);
}
"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("AsyncCounters"))
        .expect("spawned async helper chain should be propagated");
    assert!(finding.access_evidence.iter().any(|evidence| {
        evidence.in_concurrent_context
            && evidence.propagation_depth == 2
            && evidence
                .semantic_contexts
                .iter()
                .any(|item| item == "async_fn")
            && evidence
                .semantic_contexts
                .iter()
                .any(|item| item == "async_block")
    }));
    assert!(
        report
            .findings
            .iter()
            .all(|finding| { finding.struct_name.as_deref() != Some("ExclusiveCounters") })
    );
}

#[test]
fn unsafe_raw_pointer_access_is_structured_without_claiming_exclusive_ownership() {
    let dir = setup_test_dir(
        "unsafe_raw_pointer",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicU64, Ordering};

pub struct RawCounters {
    left: AtomicU64,
    right: AtomicU64,
}

pub unsafe fn bump_left(ptr: *const RawCounters) {
    unsafe { (*ptr).left.fetch_add(1, Ordering::Relaxed); }
}

pub unsafe fn bump_right(ptr: *mut RawCounters) {
    unsafe { (*ptr).right.fetch_add(1, Ordering::Relaxed); }
}
"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("RawCounters"))
        .expect("raw-pointer writes should remain visible as uncertain shared accesses");

    for field in ["left", "right"] {
        assert!(finding.access_evidence.iter().any(|evidence| {
            evidence.field_name.as_deref() == Some(field)
                && evidence.through_raw_pointer
                && evidence.access_mode == "unknown"
                && evidence
                    .semantic_contexts
                    .iter()
                    .any(|item| item == "unsafe_fn")
                && evidence
                    .semantic_contexts
                    .iter()
                    .any(|item| item == "unsafe_block")
                && evidence
                    .semantic_contexts
                    .iter()
                    .any(|item| item == "raw_pointer")
        }));
    }
}

#[test]
fn public_struct_without_api_usage_semantics_is_not_api_usage_latent() {
    let dir = setup_test_dir(
        "api_public_only",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicU64;

pub struct PlainCounters {
    a: AtomicU64,
    b: AtomicU64,
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report.findings.iter().all(|f| {
            !(f.candidate_kind == "field_group" && f.category == RiskCategory::ApiUsageLatent)
        }),
        "public exposure alone should not be enough for api_usage_latent"
    );
}

#[test]
fn public_api_usage_semantics_create_api_usage_latent() {
    let dir = setup_test_dir(
        "api_usage_latent",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicU64;

pub struct RuntimeCounters {
    submitted: AtomicU64,
    completed: AtomicU64,
}

impl RuntimeCounters {
    pub fn record_submitted(&self) {
        self.submitted.fetch_add(1, Ordering::Relaxed);
    }
    pub fn completed(&self) -> u64 {
        self.completed.load(Ordering::Relaxed)
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    let finding = report
        .findings
        .iter()
        .find(|f| {
            f.candidate_kind == "field_group" && f.struct_name.as_deref() == Some("RuntimeCounters")
        })
        .expect("API usage semantics should create field_group finding");
    assert_eq!(finding.category, RiskCategory::ApiUsageLatent);
    assert!(
        finding
            .risk_factors
            .iter()
            .any(|factor| factor.contains("API 使用启发")),
        "api_usage_latent should explain the API usage heuristic"
    );
}

#[test]
fn mutex_wrapped_object_is_suppressed() {
    let dir = setup_test_dir(
        "lock_serialized",
        &[(
            "src/lib.rs",
            r#"
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicU64, Ordering};

struct SharedCounters {
    a: AtomicU64,
    b: AtomicU64,
}

fn use_locked(_: Arc<Mutex<SharedCounters>>) {}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "field_group"),
        "Mutex/RwLock wrapped objects without direct field writes should be suppressed"
    );
}

#[test]
fn exclusive_mut_self_writes_are_suppressed_without_api_usage() {
    let dir = setup_test_dir(
        "ownership_partitioned",
        &[(
            "src/lib.rs",
            r#"
struct HotCounters {
    hit_count: u64,
    miss_count: u64,
}

impl HotCounters {
    fn update_hit(&mut self) {
        self.hit_count += 1;
    }
    fn update_miss(&mut self) {
        self.miss_count += 1;
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| f.candidate_kind != "field_group"),
        "owned/&mut-only writes without API usage or sharing should be suppressed"
    );
}

#[test]
fn container_elements_suppresses_mut_self_builder_options() {
    let dir = setup_test_dir(
        "container_elements_builder_options",
        &[(
            "src/lib.rs",
            r#"
pub struct OpenOptions {
    read: bool,
    write: bool,
    append: bool,
}

impl OpenOptions {
    pub fn read(&mut self, enabled: bool) -> &mut Self {
        self.read = enabled;
        self
    }
    pub fn write(&mut self, enabled: bool) -> &mut Self {
        self.write = enabled;
        self
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| !(f.candidate_kind == "field_group"
                && f.struct_name.as_deref() == Some("OpenOptions"))),
        "&mut self builder setters named read/write should not create an api_usage_latent container_elements"
    );
}

#[test]
fn container_elements_suppresses_request_or_config_payload_read_only_fields() {
    let dir = setup_test_dir(
        "container_elements_request_payload",
        &[(
            "src/lib.rs",
            r#"
pub struct SearchQuery {
    show_ranking_score_details: bool,
    show_performance_details: bool,
}

pub fn execute(query: &SearchQuery) -> bool {
    query.show_ranking_score_details || query.show_performance_details
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| !(f.candidate_kind == "field_group"
                && f.struct_name.as_deref() == Some("SearchQuery"))),
        "request/config payload fields that are only read should stay suppressed"
    );
}

#[test]
fn container_elements_suppresses_exclusive_mut_value_state_even_with_api_hint() {
    let dir = setup_test_dir(
        "container_elements_exclusive_api_hint",
        &[(
            "src/lib.rs",
            r#"
pub struct OldValueCache {
    access_count: usize,
    miss_count: usize,
}

impl OldValueCache {
    pub fn get_old_value(&mut self) {
        self.access_count += 1;
        self.miss_count += 1;
    }
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .all(|f| !(f.candidate_kind == "field_group"
                && f.struct_name.as_deref() == Some("OldValueCache"))),
        "exclusive plain writes should suppress container_elements even when method names look hot"
    );
}

#[test]
fn container_elements_reports_plain_scalar_writes_in_concurrent_context() {
    let dir = setup_test_dir(
        "container_elements_concurrent_plain_writes",
        &[(
            "src/lib.rs",
            r#"
struct RuntimeStats {
    read_count: usize,
    write_count: usize,
}

fn update(shared: *mut RuntimeStats) {
    std::thread::scope(|scope| {
        scope.spawn(move || unsafe {
            (*shared).read_count += 1;
        });
        scope.spawn(move || unsafe {
            (*shared).write_count += 1;
        });
    });
}
"#,
        )],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(
        report
            .findings
            .iter()
            .any(|f| f.candidate_kind == "field_group"
                && f.struct_name.as_deref() == Some("RuntimeStats")),
        "concurrent raw-pointer scalar writes should remain reportable as field_group"
    );
}

// --- Category filter ---

#[test]
fn category_filter_hot_in_project_only() {
    let dir = setup_test_dir(
        "filter",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

struct SharedCounters {
    a: AtomicU64,
    b: AtomicU64,
}

pub fn update(shared: Arc<SharedCounters>) {
    shared.a.fetch_add(1, Ordering::Relaxed);
    shared.b.fetch_add(1, Ordering::Relaxed);
}
"#,
        )],
    );

    let mut options = AnalysisOptions::all_rules();
    options.category_filter = Some(RiskCategory::HotInProject);
    let report = analyze_path_with_options(dir.path(), &options);

    for f in &report.findings {
        assert_eq!(
            f.category,
            RiskCategory::HotInProject,
            "with hot_in_project filter, all findings should be hot_in_project"
        );
    }
}

// --- Workspace support ---

#[test]
fn workspace_discovery_multiple_crates() {
    let dir = setup_test_dir(
        "workspace",
        &[
            (
                "Cargo.toml",
                r#"
[workspace]
members = ["crate-a", "crate-b"]
"#,
            ),
            (
                "crate-a/Cargo.toml",
                r#"
[package]
name = "crate-a"
version = "0.1.0"
edition = "2021"
"#,
            ),
            (
                "crate-a/src/lib.rs",
                r#"
use std::sync::atomic::AtomicU64;
pub struct SharedState {
    counter: AtomicU64,
    total: AtomicU64,
}

impl SharedState {
    pub fn record(&self) {}
}
"#,
            ),
            (
                "crate-b/Cargo.toml",
                r#"
[package]
name = "crate-b"
version = "0.1.0"
edition = "2021"
"#,
            ),
            (
                "crate-b/src/lib.rs",
                r#"
use std::sync::Arc;
fn usage() {
    let x: Arc<SharedState> = todo!();
}
struct SharedState;
"#,
            ),
        ],
    );

    let options = AnalysisOptions::all_rules();
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(report.scanned_crates.contains(&"crate-a".to_string()));
    assert!(report.scanned_crates.contains(&"crate-b".to_string()));
    assert!(report.scanned_files >= 2);
}

#[test]
fn workspace_with_root_package_scans_root_src() {
    let dir = setup_test_dir(
        "workspace_root_package",
        &[
            (
                "Cargo.toml",
                r#"
[package]
name = "root-crate"
version = "0.1.0"
edition = "2021"

[workspace]
members = ["member"]
"#,
            ),
            (
                "src/lib.rs",
                r#"
use std::sync::atomic::AtomicU64;
pub struct RootHot {
    a: AtomicU64,
    b: AtomicU64,
}

impl RootHot {
    pub fn increment_a(&self) {
        self.a.fetch_add(1, Ordering::Relaxed);
    }

    pub fn read_b(&self) -> u64 {
        self.b.load(Ordering::Relaxed)
    }
}
"#,
            ),
            (
                "member/Cargo.toml",
                r#"
[package]
name = "member"
version = "0.1.0"
edition = "2021"
"#,
            ),
            (
                "member/src/lib.rs",
                r#"
pub fn member() {}
"#,
            ),
        ],
    );

    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_path_with_options(dir.path(), &options);

    assert!(report.scanned_crates.contains(&"root-crate".to_string()));
    assert!(report.scanned_crates.contains(&"member".to_string()));
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.struct_name.as_deref() == Some("RootHot")),
        "root package src should be scanned even when Cargo.toml also has [workspace]"
    );
}

// --- Report summary ---

#[test]
fn report_summary_counts() {
    let dir = setup_test_dir(
        "summary",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicU64;
use std::cell::Cell;

pub struct NoConcurrent {
    a: AtomicU64,
    b: AtomicU64,
}

impl NoConcurrent {
    pub fn record(&self) {}
}
"#,
        )],
    );

    let options = AnalysisOptions::all_rules();
    let report = analyze_path_with_options(dir.path(), &options);

    assert_eq!(
        report.summary.hot_in_project
            + report.summary.api_usage_latent
            + report.summary.cold_or_conditional,
        report.findings.len(),
        "summary counts should match total findings"
    );
}

#[test]
fn rust_root_cause_identity_is_stable_for_one_theory_pattern() {
    let files = [
        (
            "Cargo.toml",
            r#"
[package]
name = "root-cause-fixture"
version = "0.1.0"
edition = "2024"
"#,
        ),
        (
            "src/lib.rs",
            r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

pub struct Cell {
    header: AtomicU64,
    core: AtomicU64,
    trailer: AtomicU64,
}

impl Cell {
    pub fn update_header(&self) {
        self.header.fetch_add(1, Ordering::Relaxed);
    }

    pub fn update_trailer(&self) {
        self.trailer.fetch_add(1, Ordering::Relaxed);
    }
}

pub fn run(state: Arc<Cell>) {
    let worker = Arc::clone(&state);
    std::thread::spawn(move || worker.update_header());
    state.update_trailer();
}
"#,
        ),
    ];
    let first = setup_test_dir("root_cause_first", &files);
    let second = setup_test_dir("root_cause_second", &files);

    let first_report = analyze_path_with_options(first.path(), &AnalysisOptions::all_rules());
    let second_report = analyze_path_with_options(second.path(), &AnalysisOptions::all_rules());
    let first_group = first_report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("Cell"))
        .expect("Cell should produce one clustered root cause");
    let second_group = second_report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("Cell"))
        .expect("the identical second checkout should produce the same root cause");

    assert_eq!(
        first_report
            .findings
            .iter()
            .filter(|finding| finding.struct_name.as_deref() == Some("Cell"))
            .count(),
        1,
        "one semantic pattern should produce one review unit: {first_report:#?}"
    );
    assert_eq!(first_group.finding_occurrence_count, 1, "{first_group:#?}");
    assert!(first_group.related_candidate_kinds.is_empty());
    assert_eq!(
        first_group
            .static_pattern
            .as_ref()
            .map(|pattern| pattern.colocation_pattern),
        Some(ColocationPattern::SameObjectFields)
    );
    assert!(first_group.field_list.contains(&"header".to_string()));
    assert!(first_group.field_list.contains(&"trailer".to_string()));
    assert!(
        first_group
            .access_evidence
            .iter()
            .any(|evidence| evidence.function_name.as_deref() == Some("Cell::update_header"))
    );
    assert!(
        first_group
            .access_evidence
            .iter()
            .any(|evidence| evidence.function_name.as_deref() == Some("Cell::update_trailer"))
    );
    assert_eq!(
        first_group.finding_group_id, second_group.finding_group_id,
        "temporary checkout paths must not affect the stable group ID"
    );
    assert_eq!(
        first_report.summary.finding_occurrence_count,
        first_report
            .findings
            .iter()
            .map(|finding| finding.finding_occurrence_count)
            .sum::<usize>()
    );
    assert_eq!(
        first_report.summary.finding_group_count,
        first_report.findings.len()
    );
}

// --- Cache line estimation ---

#[test]
fn struct_layout_cache_line_groups() {
    use false_sharing_detector::struct_layout::estimate_type_size;

    assert_eq!(estimate_type_size("u8"), Some(1));
    assert_eq!(estimate_type_size("u64"), Some(8));
    assert_eq!(estimate_type_size("AtomicU64"), Some(8));
    assert_eq!(estimate_type_size("usize"), Some(8));
    assert_eq!(estimate_type_size("bool"), Some(1));
    assert_eq!(estimate_type_size("SomeUnknownType"), None);
}

#[test]
fn inline_module_structs_are_scanned() {
    let dir = setup_test_dir(
        "inline_module_structs",
        &[(
            "src/lib.rs",
            r#"
pub mod runtime {
    use std::sync::atomic::{AtomicU64, Ordering};

    pub struct RuntimeStats {
        hit: AtomicU64,
        miss: AtomicU64,
    }

    impl RuntimeStats {
        pub fn track_hit(&self) {
            self.hit.fetch_add(1, Ordering::Relaxed);
        }

        pub fn track_miss(&self) {
            self.miss.fetch_add(1, Ordering::Relaxed);
        }
    }
}

"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );

    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.candidate_kind == "field_group"
                && finding.struct_name.as_deref() == Some("RuntimeStats")),
        "structs inside inline modules should be analyzed"
    );
}

#[test]
fn cfg_test_only_structs_are_not_scanned() {
    let dir = setup_test_dir(
        "cfg_test_only_structs",
        &[(
            "src/lib.rs",
            r#"
#[cfg(all(test, not(loom)))]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    pub struct TestCounters {
        first: AtomicU64,
        second: AtomicU64,
    }

    impl TestCounters {
        pub fn record_first(&self) { self.first.fetch_add(1, Ordering::Relaxed); }
        pub fn record_second(&self) { self.second.fetch_add(1, Ordering::Relaxed); }
    }
}
"#,
        )],
    );

    let report = analyze_path_with_options(dir.path(), &AnalysisOptions::all_rules());
    assert!(
        report
            .findings
            .iter()
            .all(|finding| finding.struct_name.as_deref() != Some("TestCounters"))
    );
}

#[test]
fn cfg_test_only_call_graph_does_not_upgrade_production_risk() {
    let dir = setup_test_dir(
        "cfg_test_only_call_graph",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicU64, Ordering};

pub struct ProductionCounters {
    first: AtomicU64,
    second: AtomicU64,
}

impl ProductionCounters {
    pub fn record_first(&self) { self.first.fetch_add(1, Ordering::Relaxed); }
    pub fn record_second(&self) { self.second.fetch_add(1, Ordering::Relaxed); }
}

#[cfg(test)]
mod tests {
    use super::ProductionCounters;
    use std::sync::Arc;

    fn run_first(value: &ProductionCounters) { value.record_first(); }
    fn run_second(value: &ProductionCounters) { value.record_second(); }

    #[test]
    fn concurrent_smoke_test() {
        let value = Arc::new(ProductionCounters {
            first: 0.into(),
            second: 0.into(),
        });
        let left = Arc::clone(&value);
        let right = Arc::clone(&value);
        std::thread::spawn(move || run_first(&left));
        std::thread::spawn(move || run_second(&right));
    }
}
"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("ProductionCounters"))
        .expect("public counter API remains an api-usage-latent candidate");

    assert_eq!(finding.category, RiskCategory::ApiUsageLatent);
    assert!(
        finding
            .access_evidence
            .iter()
            .all(|evidence| evidence.propagation_depth == 0 && !evidence.in_concurrent_context)
    );
}

#[test]
fn same_named_structs_in_different_modules_keep_evidence_separate() {
    let dir = setup_test_dir(
        "module_name_collision",
        &[
            (
                "src/lib.rs",
                r#"
pub mod cold;
pub mod hot;
"#,
            ),
            (
                "src/cold.rs",
                r#"
use std::sync::atomic::AtomicU64;

struct State {
    a: AtomicU64,
    b: AtomicU64,
}
"#,
            ),
            (
                "src/hot.rs",
                r#"
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

pub struct State {
    read_count: AtomicU64,
    write_count: AtomicU64,
}

impl State {
    pub fn read(&self) {
        self.read_count.fetch_add(1, Ordering::Relaxed);
    }

    pub fn write(&self) {
        self.write_count.fetch_add(1, Ordering::Relaxed);
    }
}

pub fn run(state: Arc<State>) {
    let cloned = Arc::clone(&state);
    std::thread::spawn(move || cloned.write());
    state.read();
}
"#,
            ),
        ],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let field_group_states: Vec<_> = report
        .findings
        .iter()
        .filter(|finding| {
            finding.candidate_kind == "field_group"
                && finding.struct_name.as_deref() == Some("State")
        })
        .collect();

    assert_eq!(
        field_group_states.len(),
        1,
        "only hot::State should receive evidence; cold::State must not inherit it"
    );
    assert_eq!(field_group_states[0].category, RiskCategory::HotInProject);
}

#[test]
fn root_cause_groups_keep_same_named_inline_module_types_separate() {
    let dir = setup_test_dir(
        "inline_root_cause_identity",
        &[(
            "src/lib.rs",
            r#"
pub mod first {
    use std::sync::atomic::{AtomicU64, Ordering};
    pub struct State { left: AtomicU64, right: AtomicU64 }
    impl State {
        pub fn update_left(&self) {
            self.left.fetch_add(1, Ordering::Relaxed);
        }
        pub fn update_right(&self) {
            self.right.fetch_add(1, Ordering::Relaxed);
        }
    }
}

pub mod second {
    use std::sync::atomic::{AtomicU64, Ordering};
    pub struct State { left: AtomicU64, right: AtomicU64 }
    impl State {
        pub fn update_left(&self) {
            self.left.fetch_add(1, Ordering::Relaxed);
        }
        pub fn update_right(&self) {
            self.right.fetch_add(1, Ordering::Relaxed);
        }
    }
}
"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let groups: Vec<_> = report
        .findings
        .iter()
        .filter(|finding| finding.struct_name.as_deref() == Some("State"))
        .collect();
    let group_ids: std::collections::HashSet<_> = groups
        .iter()
        .map(|finding| finding.finding_group_id.as_str())
        .collect();
    let canonical_types: std::collections::HashSet<_> = groups
        .iter()
        .filter_map(|finding| finding.layout_context.as_ref())
        .map(|layout| layout.canonical_type.as_str())
        .collect();

    assert_eq!(groups.len(), 2, "report: {report:#?}");
    assert_eq!(group_ids.len(), 2);
    assert_eq!(
        canonical_types,
        std::collections::HashSet::from(["first::State", "second::State"])
    );
}

#[test]
fn comment_only_wrapper_mentions_do_not_create_concurrency_evidence() {
    let dir = setup_test_dir(
        "comment_wrapper_mentions",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::AtomicU64;

// Documentation example: Arc<CommentOnly> would be shared by callers.
pub struct CommentOnly {
    read_count: AtomicU64,
    write_count: AtomicU64,
}
"#,
        )],
    );

    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );

    assert!(
        report
            .findings
            .iter()
            .all(|finding| finding.struct_name.as_deref() != Some("CommentOnly")),
        "comment text should not be treated as Arc<T> evidence"
    );
}

#[test]
fn macro_expansion_summary_detects_indexed_lock_and_respects_padded_elements() {
    let vulnerable = setup_test_dir(
        "macro_indexed_lock_vulnerable",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Mutex;
macro_rules! indexed_guard {
    ($container:expr, $index:expr) => {
        unsafe { $container.get_unchecked($index).lock().unwrap() }
    };
}
pub struct Scheduler { slots: Vec<Mutex<u64>> }
impl Scheduler {
    pub fn update(&self, index: usize) {
        let mut guard = indexed_guard!(self.slots, index);
        *guard += 1;
    }
}
"#,
        )],
    );
    let vulnerable_report = analyze_path_with_options(
        vulnerable.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    let finding = vulnerable_report
        .findings
        .iter()
        .find(|finding| finding.field_list.iter().any(|field| field == "slots"))
        .unwrap_or_else(|| {
            panic!(
                "declarative macro summary should expose the indexed lock access: {vulnerable_report:#?}"
            )
        });
    assert!(finding.access_evidence.iter().any(|evidence| {
        evidence
            .semantic_contexts
            .iter()
            .any(|context| context == "macro_expansion_summary")
    }));

    let fixed = setup_test_dir(
        "macro_indexed_lock_fixed",
        &[(
            "src/lib.rs",
            r#"
use std::sync::Mutex;
#[repr(align(64))]
struct CachePadded<T>(T);
macro_rules! indexed_guard {
    ($container:expr, $index:expr) => {
        unsafe { $container.get_unchecked($index).0.lock().unwrap() }
    };
}
pub struct Scheduler { slots: Vec<CachePadded<Mutex<u64>>> }
impl Scheduler {
    pub fn update(&self, index: usize) {
        let mut guard = indexed_guard!(self.slots, index);
        *guard += 1;
    }
}
"#,
        )],
    );
    let fixed_report = analyze_path_with_options(
        fixed.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(
        fixed_report
            .findings
            .iter()
            .all(|finding| !finding.field_list.iter().any(|field| field == "slots"))
    );
}

#[test]
fn per_agent_storage_follows_raw_allocation_into_symbolic_keyed_storage() {
    let vulnerable = setup_test_dir(
        "per_agent_storage_vulnerable",
        &[(
            "src/lib.rs",
            r#"
struct AgentSlot { state: u64 }
impl AgentSlot { fn update(&mut self) { self.state += 1; } }
fn install(agent_key: usize) {
    let boxed = Box::new(AgentSlot { state: agent_key as u64 });
    let raw = Box::into_raw(boxed);
    unsafe { REGISTRY.insert(agent_key, &(*raw)); }
}
fn install_all() {
    for agent_key in 0..8 { install(agent_key); }
}
"#,
        )],
    );
    let report = analyze_path_with_options(
        vulnerable.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("AgentSlot"))
        .expect("raw allocation stored by symbolic agent key should establish object_instances topology");
    assert_eq!(
        finding
            .static_pattern
            .as_ref()
            .map(|pattern| pattern.colocation_pattern),
        Some(ColocationPattern::AllocatorObjects)
    );

    let fixed = setup_test_dir(
        "per_agent_storage_fixed",
        &[(
            "src/lib.rs",
            r#"
#[repr(align(64))]
struct AgentSlot { state: u64 }
impl AgentSlot { fn update(&mut self) { self.state += 1; } }
fn install(agent_key: usize) {
    let boxed = Box::new(AgentSlot { state: agent_key as u64 });
    let raw = Box::into_raw(boxed);
    unsafe { REGISTRY.insert(agent_key, &(*raw)); }
}
fn install_all() {
    for agent_key in 0..8 { install(agent_key); }
}
"#,
        )],
    );
    let fixed_report = analyze_path_with_options(
        fixed.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]),
    );
    assert!(
        fixed_report
            .findings
            .iter()
            .all(|finding| finding.struct_name.as_deref() != Some("AgentSlot"))
    );
}

#[test]
fn symbolic_partition_tracks_raw_slice_alias_and_cache_line_partition_protection() {
    let vulnerable = setup_test_dir(
        "raw_slice_symbolic_partition_vulnerable",
        &[(
            "src/lib.rs",
            r#"
fn run(workers: usize, len: usize) {
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

"#,
        )],
    );
    let report = analyze_path_with_options(
        vulnerable.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.field_list.iter().any(|field| field == "groups"))
        .expect("raw-slice alias plus agent partition should establish indexed_writes");
    assert_eq!(finding.candidate_kind, "indexed_writes");

    let fixed = setup_test_dir(
        "raw_slice_symbolic_partition_fixed",
        &[(
            "src/lib.rs",
            r#"
fn run(workers: usize, len: usize) {
    let mut groups = unsafe { aligned_vec(len) };
    let chunk = round_upto_multiple_of_64(len / workers);
    let mut cache_line_offsets = Vec::with_capacity(workers + 1);
    cache_line_offsets.push(0);
    let groups_ptr = unsafe { SyncPtr::new(groups.as_mut_ptr()) };
    (0..workers).into_par_iter().for_each(|agent| {
        let start = cache_line_offsets[agent];
        let end = start + chunk;
        let groups = unsafe { std::slice::from_raw_parts_mut(groups_ptr.get(), len) };
        for index in start..end {
            if index < len {
                unsafe { *groups.get_unchecked_mut(index) = agent; }
            }
        }
    });
}

"#,
        )],
    );
    let fixed_report = analyze_path_with_options(
        fixed.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(
        fixed_report
            .findings
            .iter()
            .all(|finding| !finding.field_list.iter().any(|field| field == "groups"))
    );
}

#[test]
fn missing_input_is_a_fatal_incomplete_analysis() {
    let dir = tempfile::tempdir().unwrap();
    let missing = dir.path().join("does-not-exist");
    let report = analyze_path_with_options(&missing, &AnalysisOptions::all_rules());

    assert!(report.analysis_incomplete);
    assert!(report.has_fatal_diagnostics());
    assert_eq!(report.scanned_files, 0);
    assert!(report.findings.is_empty());
}

#[test]
fn private_module_does_not_turn_pub_items_into_external_api_evidence() {
    let dir = setup_test_dir(
        "private_module_visibility",
        &[(
            "src/lib.rs",
            r#"
mod internal {
    use std::sync::atomic::{AtomicU64, Ordering};

    pub struct Counters {
        pub left: AtomicU64,
        pub right: AtomicU64,
    }

    impl Counters {
        pub fn increment_left(&self) { self.left.fetch_add(1, Ordering::Relaxed); }
        pub fn increment_right(&self) { self.right.fetch_add(1, Ordering::Relaxed); }
    }
}
"#,
        )],
    );
    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );

    assert!(report.findings.iter().all(|finding| {
        !(finding.struct_name.as_deref() == Some("Counters")
            && finding.category == RiskCategory::ApiUsageLatent)
    }));
}

#[test]
fn public_reexport_restores_external_type_reachability() {
    let dir = setup_test_dir(
        "public_reexport_visibility",
        &[(
            "src/lib.rs",
            r#"
mod internal {
    use std::sync::atomic::{AtomicU64, Ordering};

    pub struct Counters {
        pub left: AtomicU64,
        pub right: AtomicU64,
    }

    impl Counters {
        pub fn increment_left(&self) { self.left.fetch_add(1, Ordering::Relaxed); }
        pub fn increment_right(&self) { self.right.fetch_add(1, Ordering::Relaxed); }
    }
}
pub use internal::Counters;
"#,
        )],
    );
    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );

    assert!(report.findings.iter().any(|finding| {
        finding.struct_name.as_deref() == Some("Counters")
            && finding.category == RiskCategory::ApiUsageLatent
    }));
}

#[test]
fn tuple_struct_fields_participate_in_layout_and_access_analysis() {
    let dir = setup_test_dir(
        "tuple_struct_layout",
        &[(
            "src/lib.rs",
            r#"
use std::sync::atomic::{AtomicU64, Ordering};

pub struct Counters(pub AtomicU64, pub AtomicU64);

impl Counters {
    pub fn increment_left(&self) { self.0.fetch_add(1, Ordering::Relaxed); }
    pub fn increment_right(&self) { self.1.fetch_add(1, Ordering::Relaxed); }
}
"#,
        )],
    );
    let report = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("Counters"))
        .expect("tuple atomic fields should be modeled");

    assert!(finding.field_list.contains(&"0".to_string()));
    assert!(finding.field_list.contains(&"1".to_string()));
}
