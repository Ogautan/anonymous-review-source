use false_sharing_detector::analyzer::analyze_path_with_options;
use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
use false_sharing_detector::types::RuleId;
use false_sharing_detector::types::{AblationComponent, AnalysisOptions, CandidateKind};
use std::fs;

fn setup_dir(files: &[(&str, &str)]) -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    for (name, source) in files {
        let path = dir.path().join(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, source).unwrap();
    }
    dir
}

fn ablated_options(rule: CandidateKind, component: AblationComponent) -> AnalysisOptions {
    let mut options = AnalysisOptions::with_rules(
        &false_sharing_detector::types::ALL_RULES
            .into_iter()
            .filter(|relation| rule.supports(*relation))
            .collect::<Vec<_>>(),
    );
    options.ablated_components.insert(component);
    options
}

#[test]
fn rust_layout_ablation_removes_struct_channel_but_records_configuration() {
    let dir = setup_dir(&[(
        "src/lib.rs",
        r#"
use std::sync::{Arc, atomic::{AtomicU64, Ordering}};
struct Counters { left: AtomicU64, right: AtomicU64 }
fn update_left(c: Arc<Counters>) {
    c.left.fetch_add(1, Ordering::Relaxed);
}
fn update_right(c: Arc<Counters>) {
    c.right.fetch_add(1, Ordering::Relaxed);
}
"#,
    )]);
    let baseline = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(
        baseline
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup))
    );

    let ablated = analyze_path_with_options(
        dir.path(),
        &ablated_options(CandidateKind::FieldGroup, AblationComponent::Layout),
    );
    assert!(ablated.findings.is_empty());
    assert_eq!(ablated.ablated_components, vec!["layout"]);
}

#[test]
fn rust_write_and_parallel_ablations_remove_indexed_writes_channel() {
    let dir = setup_dir(&[(
        "src/lib.rs",
        r#"
fn update(values: &mut [u64], indexes: &[usize]) {
    indexes.par_iter().for_each(|idx| { values[*idx] = 1; });
}
"#,
    )]);
    let baseline = analyze_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(
        baseline
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::IndexedWrites))
    );
    for component in [AblationComponent::Write, AblationComponent::MayParallel] {
        let report = analyze_path_with_options(
            dir.path(),
            &ablated_options(CandidateKind::IndexedWrites, component),
        );
        assert!(report.findings.is_empty(), "component={component:?}");
    }
}

#[test]
fn cpp_protection_ablation_exposes_the_synthetically_unprotected_record() {
    let dir = setup_dir(&[(
        "counter.cpp",
        r#"
#include <atomic>
#include <thread>
struct Counters {
  alignas(64) std::atomic<unsigned long> left;
  alignas(64) std::atomic<unsigned long> right;
};
// A separate observer supplies an independent access role. Co-updating both
// fields in update alone does not establish a false-sharing witness.
unsigned long observe_left(Counters* c) {
  return c->left.load();
}
void update(Counters* c) {
  std::thread t([&] {
    c->left.fetch_add(1);
    c->right.fetch_add(1);
  });
  t.join();
}
"#,
    )]);
    let baseline = analyze_cpp_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(baseline.findings.is_empty());

    let ablated = analyze_cpp_path_with_options(
        dir.path(),
        &ablated_options(CandidateKind::FieldGroup, AblationComponent::Protection),
    );
    assert!(
        ablated
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup)),
        "{ablated:#?}"
    );
}

#[test]
fn cpp_api_ablation_removes_public_visibility_as_api_evidence() {
    let dir = setup_dir(&[(
        "counter.hpp",
        r#"
#include <atomic>
struct PublicCounters {
  std::atomic<unsigned long> left;
  std::atomic<unsigned long> right;
};
void update(PublicCounters* counters) {
  counters->left.fetch_add(1);
}
void update_peer(PublicCounters* counters) {
  counters->right.fetch_add(1);
}
"#,
    )]);
    let baseline = analyze_cpp_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(
        baseline
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup))
    );

    let ablated = analyze_cpp_path_with_options(
        dir.path(),
        &ablated_options(CandidateKind::FieldGroup, AblationComponent::Api),
    );
    assert!(
        ablated.findings.is_empty(),
        "without the external field-capability witness, writes co-located in one ordinary function do not establish independent agents"
    );
}
