use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
use false_sharing_detector::types::RuleId;
use false_sharing_detector::types::{AnalysisOptions, CandidateKind, ColocationPattern};
use std::fs;
use tempfile::tempdir;

fn scan(source: &str, b: usize) -> false_sharing_detector::types::Report {
    let tmp = tempdir().unwrap();
    fs::write(tmp.path().join("sample.cpp"), source).unwrap();
    let mut options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    options.cache_line_size = b;
    analyze_cpp_path_with_options(tmp.path(), &options)
}

const HISTOGRAM: &str = r#"
struct Sample {
    long metadata[3];
    int first[256];
    int middle[256];
    int last[256];
};
Sample records[8];
void *work(void *opaque) {
    Sample *local = (Sample *)opaque;
    int *front = local->first;
    int *center = local->middle;
    int *back = local->last;
    for (int k = 0; k < 256; ++k) {
        front[k]++;
        center[k]++;
        back[k]++;
    }
    return nullptr;
}
void run() {
    pthread_t threads[8];
    for (int worker = 0; worker < 8; worker++) {
        pthread_create(&threads[worker], nullptr, work, &records[worker]);
    }
    for (int worker = 0; worker < 8; worker++) {
        pthread_join(threads[worker], nullptr);
    }
}
"#;

#[test]
fn inline_worker_arrays_report_cross_record_boundary_not_private_buckets() {
    for b in [32, 64, 128] {
        let report = scan(HISTOGRAM, b);
        let finding = report
            .findings
            .iter()
            .find(|f| f.has_candidate(CandidateKind::ObjectInstances))
            .unwrap_or_else(|| panic!("{report:#?}"));
        assert_eq!(finding.field_list, vec!["first", "last"]);
        let pattern = finding.static_pattern.as_ref().unwrap();
        assert_eq!(
            pattern.colocation_pattern,
            ColocationPattern::AdjacentObjects
        );
        assert!(
            pattern
                .witness_locations
                .contains(&"Sample[0].last".to_owned())
        );
        assert!(
            pattern
                .witness_locations
                .contains(&"Sample[1].first".to_owned())
        );
        assert!(
            finding
                .access_evidence
                .iter()
                .any(|e| e.field_name.as_deref() == Some("first"))
        );
        assert!(
            report
                .findings
                .iter()
                .all(|f| !f.field_list.contains(&"middle".to_owned()))
        );
    }
}

#[test]
fn inline_worker_boundary_respects_alignment_gap_read_only_and_common_lock() {
    for source in [
        HISTOGRAM.replace("struct Sample", "struct alignas(128) Sample"),
        HISTOGRAM.replace("metadata[3]", "metadata[32]"),
        HISTOGRAM
            .replace("front[k]++;", "consume(front[k]);")
            .replace("center[k]++;", "consume(center[k]);")
            .replace("back[k]++;", "consume(back[k]);"),
        HISTOGRAM
            .replace("front[k]++;", "pthread_mutex_lock(&mu);\nfront[k]++;")
            .replace("back[k]++;", "back[k]++;\npthread_mutex_unlock(&mu);")
            .replace(
                "Sample records[8];",
                "Sample records[8];\npthread_mutex_t mu;",
            ),
    ] {
        let report = scan(&source, 64);
        assert!(
            report
                .findings
                .iter()
                .all(|f| !f.has_candidate(CandidateKind::ObjectInstances)),
            "{source}\n{report:#?}"
        );
    }
    let source = HISTOGRAM.replace("struct Sample", "struct alignas(64) Sample");
    assert!(
        scan(&source, 64)
            .findings
            .iter()
            .all(|f| !f.has_candidate(CandidateKind::ObjectInstances))
    );
    assert!(
        scan(&source, 128)
            .findings
            .iter()
            .any(|f| f.has_candidate(CandidateKind::ObjectInstances))
    );
}

#[test]
fn same_worker_argument_or_immediate_join_is_not_distinct_concurrent_records() {
    for source in [
        HISTOGRAM.replace("&records[worker]", "&records[0]"),
        HISTOGRAM.replace("(Sample *)opaque", "(Sample *)unrelated"),
        HISTOGRAM.replace("back[k]++;", "back = unrelated;\nback[k]++;"),
        HISTOGRAM.replace(
            "&records[worker]);",
            "&records[worker]);\npthread_join(threads[worker], nullptr);",
        ),
    ] {
        let report = scan(&source, 64);
        assert!(
            report
                .findings
                .iter()
                .all(|f| !f.has_candidate(CandidateKind::ObjectInstances)),
            "{report:#?}"
        );
    }
}

const SCALAR_LAUNCH: &str = r#"
long counters[16];
void change(int declared_coordinate);
void change(int coordinate) {
    counters[coordinate]++;
}
void *entry(void *opaque) {
    int coordinate = (int)opaque;
    change(coordinate);
    return nullptr;
}
void launch() {
    pthread_t threads[16];
    for (int ordinal = 0; ordinal < 16; ordinal++) {
        pthread_create(&threads[ordinal], nullptr, entry, (void*)ordinal);
    }
    for (int ordinal = 0; ordinal < 16; ordinal++) {
        pthread_join(threads[ordinal], nullptr);
    }
}
"#;

#[test]
fn pthread_scalar_identity_propagates_through_declared_helper_without_name_heuristic() {
    let report = scan(SCALAR_LAUNCH, 64);
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.field_list.contains(&"counters".to_owned())
                && f.static_pattern
                    .as_ref()
                    .is_some_and(|p| p.parallelism_evidence
                        == false_sharing_detector::types::ParallelismEvidence::ConcurrentContext)),
        "{report:#?}"
    );
    for source in [
        SCALAR_LAUNCH.replace("(void*)ordinal", "(void*)0"),
        SCALAR_LAUNCH.replace(
            "change(coordinate);",
            "coordinate = 0;\nchange(coordinate);",
        ),
        SCALAR_LAUNCH.replace("change(coordinate);", "change(0);"),
        SCALAR_LAUNCH.replace(
            "(void*)ordinal);",
            "(void*)ordinal);\npthread_join(threads[ordinal], nullptr);",
        ),
        SCALAR_LAUNCH.replace(
            "void launch() {",
            "void ordinary() { entry(nullptr); }\nvoid launch() {",
        ),
    ] {
        let report = scan(&source, 64);
        assert!(report.findings.is_empty(), "{source}\n{report:#?}");
    }
}

#[test]
fn fresh_worker_descriptor_binds_scalar_member_but_reused_or_rebound_one_does_not() {
    let source = SCALAR_LAUNCH.replace("long counters[16];", "long counters[16];\nstruct Dispatch { int coordinate; };")
        .replace("int coordinate = (int)opaque;", "Dispatch *item = (Dispatch*)opaque;\nint coordinate = item->coordinate;")
        .replace("pthread_create(&threads[ordinal], nullptr, entry, (void*)ordinal);",
            "Dispatch *packet = (Dispatch*)malloc(sizeof(Dispatch));\npacket->coordinate = ordinal;\npthread_create(&threads[ordinal], nullptr, entry, (void*)packet);");
    assert!(
        scan(&source, 64)
            .findings
            .iter()
            .any(|f| f.field_list.contains(&"counters".to_owned())),
        "{:#?}",
        scan(&source, 64)
    );
    for input in [
        source.replace("packet->coordinate = ordinal", "packet->coordinate = 0"),
        source.replace(
            "int coordinate = item->coordinate",
            "item->coordinate = 0;\nint coordinate = item->coordinate",
        ),
        source.replace(
            "int coordinate = item->coordinate",
            "item = unknown;\nint coordinate = item->coordinate",
        ),
        source.replace(
            "Dispatch *packet = (Dispatch*)malloc(sizeof(Dispatch));",
            "Dispatch *packet = shared;",
        ),
    ] {
        assert!(
            scan(&input, 64)
                .findings
                .iter()
                .all(|f| !f.field_list.contains(&"counters".to_owned())),
            "{input}\n{:#?}",
            scan(&input, 64)
        );
    }
}

#[test]
fn parenthesized_indexed_lvalues_preserve_mutation_without_crossing_calls_or_pointees() {
    for expr in [
        "(counters[coordinate])++",
        "++((counters[coordinate]))",
        "(counters[coordinate]) += 2",
    ] {
        let source = SCALAR_LAUNCH.replace("counters[coordinate]++", expr);
        assert!(
            scan(&source, 64)
                .findings
                .iter()
                .any(|f| f.field_list.contains(&"counters".to_owned())),
            "{expr}"
        );
    }
    for expr in [
        "get(counters[coordinate])++",
        "sizeof(counters[coordinate])",
        "consume((counters[coordinate]))",
        "(counters[coordinate], other)++",
    ] {
        let source = SCALAR_LAUNCH.replace("counters[coordinate]++", expr);
        assert!(
            scan(&source, 64).findings.is_empty(),
            "{expr}\n{:#?}",
            scan(&source, 64)
        );
    }
}
