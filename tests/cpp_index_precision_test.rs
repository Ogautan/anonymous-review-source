use false_sharing_detector::types::RuleId;
use std::fs;

use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
use false_sharing_detector::types::{AnalysisOptions, CandidateKind, ParallelismEvidence, Report};
use tempfile::tempdir;

#[test]
fn indexed_members_require_their_own_contiguous_storage() {
    for size in [32, 64, 128] {
        for (declaration, expected) in [
            ("Proxy values;", false),
            ("Opaque<int *> values;", false),
            ("int *values;", true),
            ("int values[32];", true),
            ("std::vector<int> values;", true),
            ("using Slots = std::array<int, 32>; Slots values;", true),
        ] {
            for expression in ["values", "this->values"] {
                let root = tempdir().unwrap();
                fs::write(root.path().join("sample.cpp"), format!(
                    "struct Proxy {{ int &operator[](int); }};\ntemplate<class T> struct Opaque {{ int &operator[](int); }};\nstruct Unrelated {{ int *values; }};\nstruct Owner {{ {declaration}\nvoid update(int worker_id) {{\n{expression}[worker_id]++;\n}}\n}};\n"
                )).unwrap();
                let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
                options.cache_line_size = size;
                let report = analyze_cpp_path_with_options(root.path(), &options);
                assert_eq!(
                    !report.findings.is_empty(),
                    expected,
                    "B={size} {declaration} {expression}: {report:#?}"
                );
            }
        }
    }
}

#[test]
fn indexed_member_layout_follows_typed_receivers_across_files() {
    for (declaration, expected) in [("Proxy values;", false), ("int *values;", true)] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("storage.hpp"),
            format!(
                "struct Proxy {{ int &operator[](int); }};\nstruct Owner {{ {declaration} }};\n"
            ),
        )
        .unwrap();
        fs::write(
            root.path().join("unrelated.cpp"),
            "struct Other { int *values; };\n",
        )
        .unwrap();
        fs::write(root.path().join("sample.cpp"), "#include \"storage.hpp\"\nvoid update(Owner &object, int worker_id) {\nobject.values[worker_id]++;\n}\n").unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{declaration}: {report:#?}"
        );
    }
}

#[test]
fn indexed_member_veto_keeps_contiguous_and_unresolved_same_line_uses() {
    for (other, expression) in [
        ("int *values", "values"),
        ("Unknown &other", "other.values"),
    ] {
        let source = format!(
            "struct Proxy {{ int &operator[](int); }};\nstruct Owner {{ Proxy values; }};\nint *values;\nvoid update(Owner &object, {other}, int worker_id) {{\nobject.values[worker_id]++; {expression}[worker_id]++;\n}}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        // An unresolved receiver cannot supply a member exclusion proof.
        assert!(!report.findings.is_empty(), "{other}: {report:#?}");
    }
}

#[test]
fn indexed_summaries_bind_the_method_receiver_not_just_its_name() {
    let declarations = "struct Slots { int data[32];\nvoid fetch_min(int coordinate) {\ndata[coordinate]++;\n}\n};\n";
    for (receiver, expected) in [
        ("Slots", true),
        ("Other", false),
        ("std::atomic_ref<int>", false),
    ] {
        let source = format!(
            "{declarations}\nvoid invoke({receiver}& object, int worker_id) {{\nobject.fetch_min(worker_id);\n}}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        let propagated = report
            .findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .any(|e| {
                e.function_name.as_deref() == Some("invoke")
                    && e.field_name.as_deref() == Some("data")
            });
        assert_eq!(propagated, expected, "{receiver}: {report:#?}");
    }
}

#[test]
fn indexed_summaries_follow_typed_member_receivers_and_respect_shadowing() {
    let declarations =
        "struct Slots { int data[32];\nvoid change(int coordinate) {\ndata[coordinate]++;\n}\n};\n";
    for (body, expected) in [
        ("target->change(worker_id);", true),
        ("this->target->change(worker_id);", true),
        ("(*target).change(worker_id);", true),
        ("Unknown target;\ntarget.change(worker_id);", false),
        (
            "std::atomic_ref<int> target;\ntarget.change(worker_id);",
            false,
        ),
    ] {
        let source = format!(
            "{declarations}\nstruct Owner {{ Slots* target;\nvoid invoke(int worker_id) {{\n{body}\n}}\n}};\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        let propagated = report
            .findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .any(|e| {
                e.function_name.as_deref() == Some("invoke")
                    && e.field_name.as_deref() == Some("data")
            });
        assert_eq!(propagated, expected, "{body}: {report:#?}");
    }
}

#[test]
fn indexed_summaries_follow_included_member_type_aliases_without_namespace_capture() {
    for (extra, expected) in [("", true), ("using Handle = Other;", false)] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("storage.hpp"),
            "namespace storage {\ntemplate<class T> struct Slots { int data[32];\nvoid change(int coordinate) {\ndata[coordinate]++;\n}\n};\nusing Handle = Slots<int>;\n}\n").unwrap();
        fs::write(root.path().join("owner.cpp"), format!(
            "#include \"storage.hpp\"\nnamespace unrelated {{ using Handle = std::atomic<int>; }}\nnamespace storage {{ struct Other {{ void change(int); }};\nnamespace detail {{\n{extra}\nstruct Owner {{ Handle *target;\nvoid invoke(int worker_id) {{\ntarget->change(worker_id);\n}}\n}};\n}}\n}}\n"
        )).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        let propagated = report
            .findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .any(|e| {
                e.function_name.as_deref() == Some("invoke")
                    && e.field_name.as_deref() == Some("data")
            });
        assert_eq!(propagated, expected, "{extra}: {report:#?}");
    }
}

#[test]
fn thread_handle_assignment_does_not_run_in_its_own_callback() {
    let prefix = "std::thread handles[8];\nint values[8];\n";
    for (setup, expected_handle) in [
        ("void setup() {\nint worker_id = 0;", false),
        ("void setup(int worker_id) {", true),
        (
            "void setup() {\n#pragma omp parallel for\nfor(int worker_id=0;worker_id<8;++worker_id)",
            true,
        ),
    ] {
        let source = format!(
            "{prefix}{setup}\nhandles[worker_id] = std::thread([](int worker_id) {{\nvalues[worker_id]++;\n}}, worker_id);\n}}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|s| s == "handles")),
            expected_handle,
            "{source}\n{report:#?}"
        );
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|s| s == "values")),
            "worker payload lost: {source}\n{report:#?}"
        );
    }
    let nested = format!(
        "{prefix}\nvoid setup() {{\nstd::thread outer([](int worker_id) {{\nhandles[worker_id] = std::thread([\n](int inner_id) {{\nvalues[inner_id]++;\n}}, worker_id);\n}}, 0);\n}}\n"
    );
    let report = analyze(&nested, &[CandidateKind::IndexedWrites]);
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.field_list.iter().any(|s| s == "handles")),
        "the outer worker still owns a concurrent handle assignment: {report:#?}"
    );
}

#[test]
fn indexed_call_return_is_not_the_outer_contiguous_storage() {
    for block in [32, 64, 128] {
        for (declaration, expression, expected) in [
            (
                "struct Table { int* at(int); }; Table slots;",
                "slots.at(0)[worker_id]",
                false,
            ),
            ("int slots[32];", "slots[worker_id]", true),
        ] {
            let root = tempdir().unwrap();
            fs::write(root.path().join("storage.hpp"), format!("{declaration}\nvoid update(int worker_id) {{\nstd::atomic_ref<int> alias({expression});\nalias.fetch_add(1);\n}}\n")).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
            options.cache_line_size = block;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "B={block} {expression}: {report:#?}"
            );
        }
    }
}

#[test]
fn returned_index_callback_has_bound_external_integer_input() {
    let base = "int values[32];\nauto make_callback() {\n return [](int coordinate) {\n values[coordinate]++;\n };\n}\n";
    let report = analyze(base, &[CandidateKind::IndexedWrites]);
    assert!(!report.findings.is_empty(), "{report:#?}");
    assert!(report.findings.iter().all(|f| {
        f.static_pattern
            .as_ref()
            .is_some_and(|p| p.parallelism_evidence == ParallelismEvidence::ExternalApiPotential)
    }));
    for input in [
        base.replace("auto make_callback", "static auto make_callback"),
        format!("namespace {{\n{base}\n}}"),
        base.replace("values[coordinate]", "values[0]"),
        base.replace("int coordinate", "Opaque coordinate"),
        base.replace("return []", "auto callback = []"),
        base.replace("int coordinate", "int *coordinate"),
    ] {
        assert!(
            analyze(&input, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{input}"
        );
    }
    for (definition, expected) in [
        ("using Coordinate = int64_t;", true),
        ("using Inner = int; using Coordinate = Inner;", true),
        (
            "using Coordinate = int; namespace Other { using Coordinate = double; }",
            true,
        ),
        (
            "using Coordinate = int; struct Other { using Coordinate = double; };",
            true,
        ),
        ("using Coordinate = double;", false),
        (
            "#if MODE\nusing Coordinate = int;\n#else\nusing Coordinate = double;\n#endif",
            false,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("types.hpp"), definition).unwrap();
        fs::write(
            root.path().join("callback.hpp"),
            base.replace("int coordinate", "Coordinate coordinate"),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{definition}\n{report:#?}"
        );
    }
}

#[test]
fn indexed_atomic_reference_api_requires_bound_parameter_and_rmw() {
    let source = r#"
std::vector<int> values;
void increment(unsigned coordinate) {
    std::atomic_ref<int> element{values[coordinate]};
    element.fetch_add(1);
}
"#;
    for namespace in ["std", "sycl", "cl::sycl"] {
        let input = source.replace("std::atomic_ref", &format!("{namespace}::atomic_ref"));
        let report = analyze(&input, &[CandidateKind::IndexedWrites]);
        assert!(!report.findings.is_empty(), "{input}\n{report:#?}");
        assert!(
            report.findings.iter().all(|finding| finding
                .static_pattern
                .as_ref()
                .is_some_and(|pattern| pattern.parallelism_evidence
                    == ParallelismEvidence::ExternalApiPotential))
        );
    }
    for input in [
        source.replace("[coordinate]", "[0]"),
        source.replace("element.fetch_add(1)", "element.load()"),
        source.replace("element.fetch_add(1)", "sizeof(element.fetch_add(1))"),
        source.replace(
            "element.fetch_add(1);",
            "auto deferred = [&] { element.fetch_add(1); };",
        ),
        source.replace(
            "    std::atomic_ref<int>",
            "    coordinate = 0;\n    std::atomic_ref<int>",
        ),
        source.replace("std::atomic_ref", "custom::atomic_ref"),
        source.replace("[coordinate]", "[transform(coordinate)]"),
        source.replace(
            "element.fetch_add(1);",
            "escape(element);\n    element.fetch_add(1);",
        ),
        source
            .replace("unsigned coordinate", "unsigned ignored")
            .replace(
                "std::atomic_ref<int>",
                "const unsigned coordinate = 0;\n    std::atomic_ref<int>",
            ),
    ] {
        assert!(
            analyze(&input, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{input}"
        );
    }
}

fn analyze(source: &str, rules: &[CandidateKind]) -> Report {
    // Project a discovery method for these focused regressions; public selection uses relations.
    let mut report = {
        let root = tempdir().unwrap();
        fs::write(root.path().join("candidate.cpp"), source).unwrap();
        analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(
                &false_sharing_detector::types::ALL_RULES
                    .into_iter()
                    .filter(|relation| rules.iter().any(|kind| kind.supports(*relation)))
                    .collect::<Vec<_>>(),
            ),
        )
    };
    report.findings.retain(|finding| {
        rules.iter().any(|kind| {
            finding.candidate_kind == *kind || finding.related_candidate_kinds.contains(kind)
        })
    });
    report
}

#[test]
fn nested_indexing_binds_writes_to_the_actual_storage_layer() {
    for size in [32, 64, 128] {
        for (declaration, access, expected) in [
            (
                "std::vector<std::vector<int>> rows(8, std::vector<int>(8));",
                "rows[id][0]++;",
                false,
            ),
            ("std::vector<int*> rows;", "rows[id][0]++;", false),
            ("int *rows[8];", "rows[id][0]++;", false),
            ("int **rows;", "rows[id][0]++;", false),
            (
                "std::array<std::vector<int>, 8> rows;",
                "rows[id][0]++;",
                false,
            ),
            (
                "std::vector<std::array<int*, 4>> rows;",
                "rows[id][0][0]++;",
                false,
            ),
            ("int rows[8][8];", "rows[id][0]++;", true),
            (
                "std::array<std::array<int, 8>, 8> rows;",
                "rows[id][0]++;",
                true,
            ),
            (
                "std::vector<std::array<int, 8>> rows;",
                "rows[id][0]++;",
                true,
            ),
            ("std::vector<std::string> rows;", "rows[id][0]++;", true),
            (
                "std::vector<std::vector<int>> rows;",
                "rows[id] = std::vector<int>(8);",
                true,
            ),
            ("int *rows[8];", "rows[id] = nullptr;", true),
            ("std::vector<int> rows(8);", "rows[id]++;", true),
        ] {
            let root = tempdir().unwrap();
            let source = format!(
                "{declaration}\nvoid run() {{\n#pragma omp parallel for\nfor (int id = 0; id < 8; ++id) {{\n{access}\n}}\n}}\n"
            );
            fs::write(root.path().join("candidate.cpp"), &source).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
            options.cache_line_size = size;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "B={size}: {source}\n{report:#?}"
            );
            assert!(!report.analysis_incomplete, "{report:#?}");
        }
    }
}

#[test]
fn nested_storage_proofs_do_not_cross_shadowed_bindings_or_hide_slot_writes() {
    for (source, expected) in [
        (
            "std::vector<std::vector<int>> rows;\nvoid update(int id) {\nrows[id][0]++;\n}\n",
            false,
        ),
        (
            "std::vector<std::vector<int>> rows;\nvoid update(int rows[8][8]) {\n#pragma omp parallel for\nfor (int id=0; id<8; ++id) { rows[id][0]++; }\n}\n",
            true,
        ),
        (
            "std::vector<std::vector<int>> rows;\nvoid update(Opaque& rows, int id) {\nrows[id][0]++;\n}\n",
            false,
        ),
        (
            "std::vector<std::vector<int>> rows;\nvoid update(int id) {\n\n#pragma omp parallel for\nfor(int worker=0; worker<8; ++worker) { rows[worker][0]++; rows[worker] = std::vector<int>(8); }\n}\n",
            true,
        ),
        (
            "std::vector<std::vector<int>> rows;\nvoid update(int id) {\n\n#pragma omp parallel for\nfor(int worker=0; worker<8; ++worker) {\nrows[worker][0]++;\nrows[worker] = std::vector<int>(8);\n}\n}\n",
            true,
        ),
    ] {
        let report = analyze(source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{source}\n{report:#?}"
        );
    }
}

#[test]
fn template_arguments_do_not_supply_the_outer_receivers_storage_layout() {
    for declaration in [
        "Opaque<std::vector<int>> rows;",
        "Other<std::array<int, 8>> rows;",
        "using Storage = Opaque<std::vector<int>>;\nStorage rows;",
        "using Storage = std::conditional_t<true, Opaque<int>, std::vector<int>>;\nStorage rows;",
        "using Storage = std::conditional<false, std::vector<int>, Opaque<int>>::type;\nStorage rows;",
        "std::conditional<Flag, std::vector<int>, Opaque<int>> rows;",
    ] {
        let source = format!(
            "{declaration}\nvoid run() {{\n#pragma omp parallel for\nfor (int id=0;id<8;++id) {{ rows[id]++; }}\n}}\n"
        );
        assert!(
            analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{source}"
        );
    }
    for declaration in [
        "std::vector<int> rows;",
        "using Storage = std::vector<int>;\nStorage rows;",
        "::std::vector<int> rows;",
        "using Storage = std::conditional_t<true, std::vector<int>, Opaque<int>>;\nStorage rows;",
        "using Storage = std::conditional<false, Opaque<int>, std::vector<int>>::type;\nStorage rows;",
    ] {
        let source = format!(
            "{declaration}\nvoid run() {{\n#pragma omp parallel for\nfor (int id=0;id<8;++id) {{ rows[id]++; }}\n}}\n"
        );
        assert!(
            !analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{source}"
        );
    }
}

#[test]
fn speculative_occurrences_do_not_borrow_another_occurrences_partition_witness() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("candidate.cpp"),
        r#"
int slots[32];
void update(int worker_id) { slots[worker_id]++; }
void run() {
    std::thread worker([] { slots[0] = 7; });
    worker.join();
}
"#,
    )
    .unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    options.max_findings = None;
    let reviewable = analyze_cpp_path_with_options(root.path(), &options);
    options.cpp_include_speculative = true;
    let broad = analyze_cpp_path_with_options(root.path(), &options);
    assert_eq!(reviewable.findings.len(), 1, "{reviewable:#?}");
    assert_eq!(broad.findings.len(), 1, "{broad:#?}");
    assert!(
        reviewable.summary.finding_occurrence_count < broad.summary.finding_occurrence_count,
        "reviewable={reviewable:#?}\nbroad={broad:#?}"
    );
    assert_eq!(
        reviewable.summary.cpp_speculative_candidates, 0,
        "a rejected occurrence inside a supported group is not another speculative group"
    );
    assert!(
        reviewable.findings[0]
            .access_evidence
            .iter()
            .all(|a| a.function_name.as_deref() != Some("run"))
    );
    options.cpp_include_speculative = false;
    options.max_findings = Some(0);
    let capped = analyze_cpp_path_with_options(root.path(), &options);
    assert!(capped.findings.is_empty());
    assert_eq!(capped.summary.candidate_findings, 1);
    assert_eq!(capped.summary.cpp_speculative_candidates, 0);
    assert_eq!(capped.summary.suppressed_candidates, 1);
    assert_eq!(
        capped.summary.finding_occurrence_count,
        reviewable.summary.finding_occurrence_count
    );
}

#[test]
fn global_array_requires_concurrency_or_partition_not_just_a_mutation() {
    for (argument, expected) in [("period", false), ("worker_id", true)] {
        let report = analyze(
            &format!(
                "static long counters[16];\nvoid update(int {argument}) {{\n counters[{argument}] += 1;\n}}"
            ),
            &[CandidateKind::StaticData],
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{:#?}",
            report.findings
        );
        if expected {
            assert!(
                report
                    .findings
                    .iter()
                    .flat_map(|f| &f.access_evidence)
                    .any(|a| {
                        a.semantic_contexts
                            .iter()
                            .any(|c| c == "cpp_conditional_partition_api")
                            && a.description.contains("尚未证明具体调用者同时执行")
                    })
            );
            assert!(
                report
                    .findings
                    .iter()
                    .flat_map(|f| &f.access_evidence)
                    .all(|access| !access.in_concurrent_context),
                "an externally supplied index is an API hypothesis, not a runtime thread witness"
            );
        }
    }
    let report = analyze(
        r#"
        static long counters[16];
        void update() {
            #pragma omp parallel for
            for (int i = 0; i < 16; ++i) {
                counters[i] += 1;
            }
        }
    "#,
        &[CandidateKind::StaticData],
    );
    assert!(
        !report.findings.is_empty(),
        "real parallel loop must remain eligible"
    );
    assert!(
        report
            .findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .any(|a| {
                a.in_concurrent_context
                    && !a
                        .semantic_contexts
                        .iter()
                        .any(|c| c == "cpp_conditional_partition_api")
                    && a.description.contains("存在并发上下文或运行时分区来源")
            })
    );
    let report = analyze(
        r#"
        static long counters[16];
        void sequential(int period) { counters[period]++; }
        void worker(int worker_id) { counters[worker_id] = 1; }
    "#,
        &[CandidateKind::StaticData],
    );
    assert!(
        !report.findings.is_empty(),
        "a sequential RMW must not hide the weaker but partitioned store"
    );
}

#[test]
fn generic_file_scope_sibling_arrays_share_a_proven_index_partition() {
    let report = analyze(
        r#"
        #define LOCAL static
        LOCAL int payload[16];
        LOCAL int counters[16];

        void update(int worker_id) {
            payload[worker_id] = 1;
            counters[worker_id]++;
        }
        "#,
        &[CandidateKind::StaticData],
    );
    let finding = report.findings.iter().find(|finding| {
        finding.has_candidate(CandidateKind::StaticData)
            && finding.field_list.iter().any(|field| field == "payload")
            && finding.field_list.iter().any(|field| field == "counters")
    });
    assert!(
        finding.is_some(),
        "same-index global arrays should form one reviewable finding: {:#?}",
        report.findings
    );
    let finding = finding.unwrap();
    assert!(
        finding
            .access_evidence
            .iter()
            .any(|access| access.field_name.as_deref() == Some("counters")
                && matches!(
                    access.access_kind.as_deref(),
                    Some("write" | "read_modify_write")
                )),
        "the sibling group must retain a write witness: {finding:#?}"
    );
}

#[test]
fn header_element_alignment_needs_visible_unshadowed_array_declaration() {
    for (include, alignment, body, expected) in [
        (true, "alignas(64)", "entries[worker_id].count++;", false),
        (true, "", "entries[worker_id].count++;", true),
        (false, "alignas(64)", "entries[worker_id].count++;", true),
        (
            true,
            "alignas(64)",
            "long *entries = acquire(); entries[worker_id]++;",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("storage.h"),
            format!("struct {alignment} Entry {{ long count; }};\nextern Entry entries[16];\n"),
        )
        .unwrap();
        fs::write(
            root.path().join("caller.cpp"),
            format!(
                "{}\nvoid update(int worker_id) {{\n {body}\n}}",
                if include {
                    "#include \"storage.h\""
                } else {
                    ""
                }
            ),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{body}\n{:#?}",
            report.findings
        );
    }
}

#[test]
fn static_macro_effects_require_visible_source_and_exact_target_storage() {
    for (include, definition, operation, expected) in [
        (
            true,
            "#define CHANGE(target, delta) __sync_fetch_and_add(&(target), delta)",
            "CHANGE(\n counters[position], 1);",
            true,
        ),
        (
            true,
            "#define CHANGE(target, delta) __sync_fetch_and_add(&(target), delta)",
            "// CHANGE(counters[position], 1);",
            false,
        ),
        (
            true,
            "#define CHANGE(target, delta) __sync_fetch_and_add(&(target), delta)",
            "const char *message = \"CHANGE(counters[position], 1)\";",
            false,
        ),
        (
            true,
            "#define CHANGE(target, delta) __sync_fetch_and_add(&(target), delta)",
            "CHANGE(counters[position], incoming[position]);",
            true,
        ),
        (
            true,
            "#define CHANGE(target, delta) unknown(target, delta)",
            "CHANGE(counters[position], incoming[position]);",
            false,
        ),
        (
            false,
            "#define CHANGE(target, delta) __sync_fetch_and_add(&(target), delta)",
            "CHANGE(counters[position], incoming[position]);",
            false,
        ),
        (
            true,
            "#define CHANGE(target, delta) __sync_fetch_and_add(&(target), delta)",
            "CHANGE(batch->counters[position], counters[position]);",
            false,
        ),
        (
            true,
            "#define CHANGE(target, delta) __sync_fetch_and_add(&(target), delta)\n#undef CHANGE",
            "CHANGE(counters[position], incoming[position]);",
            false,
        ),
        (
            true,
            "#define LOCK(target) pthread_mutex_lock(&target##_mutex)",
            "LOCK(counters[position].guard);",
            true,
        ),
        (
            true,
            "#define LOCK(target) pthread_mutex_lock(&target##_mutex)",
            "LOCK(counters[position]->guard);",
            false,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("effects.h"), definition).unwrap();
        let storage = if operation.contains("LOCK") {
            if operation.contains("->guard") {
                "Gate *"
            } else {
                "Gate"
            }
        } else {
            "long"
        };
        fs::write(
            root.path().join("caller.cpp"),
            format!(
                "{}\nstruct Gate {{ pthread_mutex_t guard_mutex; }};\nstatic {storage} counters[16];\nlong incoming[16];\nstruct Batch {{ long counters[16]; }};\nBatch *batch;\nvoid update(int position) {{\n {operation}\n}}",
                if include {
                    "#include \"effects.h\""
                } else {
                    ""
                },
            ),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{definition}\n{operation}\n{:#?}",
            report.findings
        );
        assert!(
            report
                .findings
                .iter()
                .flat_map(|f| &f.access_evidence)
                .all(|a| !a.in_concurrent_context)
        );
    }
}

#[test]
fn atomic_global_element_rmw_is_a_conditional_partition_api_not_a_thread_id() {
    for (ty, operation, expected) in [
        ("std::atomic<long>", "fetch_add(1)", true),
        ("std::atomic<long>", "store(0)", false),
        ("Counter", "fetch_add(1)", false),
    ] {
        let report = analyze(
            &format!(
                "static {ty} counters[16];\nvoid update(int metric) {{\n counters[metric].{operation};\n}}"
            ),
            &[CandidateKind::StaticData],
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{:#?}",
            report.findings
        );
        assert!(
            report
                .findings
                .iter()
                .flat_map(|f| &f.access_evidence)
                .all(|a| !a.in_concurrent_context)
        );
    }
    let pointers = analyze(
        "static std::atomic<long> *counters[16];\nvoid update(int metric) {\n counters[metric]++;\n}",
        &[CandidateKind::StaticData],
    );
    assert!(
        pointers.findings.is_empty(),
        "pointer-slot arithmetic is not an atomic-element RMW: {:#?}",
        pointers.findings
    );
}

#[test]
fn cross_file_write_summary_preserves_element_alignment_not_array_base_alignment() {
    for (element_alignment, array_alignment, pointer, mutation, expected) in [
        ("alignas(64)", "", "", ".count++", false),
        ("", "", "", ".count++", true),
        ("", "alignas(64)", "", ".count++", true),
        ("alignas(64)", "", "*", "++", true),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("storage.cpp"),
            format!(
                r#"
            struct {element_alignment} Entry {{ long count; }};
            {array_alignment} Entry {pointer} entries[16];
            void update(int position) {{
                entries[position]{mutation};
            }}
        "#
            ),
        )
        .unwrap();
        fs::write(
            root.path().join("caller.cpp"),
            r#"
            void update(int position);
            void use(int worker_id) {
                update(worker_id);
            }
        "#,
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.file.ends_with("caller.cpp")
                    && f.field_list.iter().any(|s| s == "entries")),
            expected,
            "{:#?}",
            report.findings
        );
    }
}

#[test]
fn static_array_helper_retains_real_worker_execution_without_parameter_name_hints() {
    for (entry, expected) in [
        ("pthread_create(&handle, nullptr, entry, nullptr);", true),
        ("entry(nullptr);", false),
    ] {
        let source = format!(
            r#"
            static long counters[16];
            static void assign(int position, long value) {{
                counters[position] = value;
            }}
            static void forward(int position) {{
                assign(position, 0);
            }}
            void *entry(void *opaque) {{
                int position = (long)opaque;
                while (keep_running()) {{
                    forward(position);
                }}
                return nullptr;
            }}
            void start() {{ {entry} }}
        "#
        );
        let report = analyze(&source, &[CandidateKind::StaticData]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{:#?}",
            report.findings
        );
    }
    for body in [
        "forward(2);",
        "auto later = [] { forward(2); }; save(later);",
        "auto forward = [](int) {}; while (keep_running()) { forward(2); }",
    ] {
        let source = format!(
            r#"
            static long counters[16];
            static void forward(int position) {{ counters[position] = 0; }}
            void *entry(void *) {{
                {body}
                return nullptr;
            }}
            void start() {{ pthread_create(&handle, nullptr, entry, nullptr); }}
        "#
        );
        assert!(
            analyze(&source, &[CandidateKind::StaticData])
                .findings
                .is_empty(),
            "{body}"
        );
    }
}

#[test]
fn thread_exit_store_is_not_a_recurrent_worker_write() {
    for (body, extra_call, expected) in [
        (
            "while (true) {\n if (done()) {\n slots[thread] = 0;\n break;\n }\n }",
            "",
            false,
        ),
        (
            "while (true) {\n slots[thread] = 0;\n if (done()) break;\n }",
            "",
            true,
        ),
        (
            "while (true) {\n while (true) {\n slots[thread] = 0;\n break;\n }\n if (done()) break;\n }",
            "",
            true,
        ),
        ("slots[thread] = 0;", "worker(nullptr);", true),
        (
            "slots[thread] = 0;",
            "auto alias = worker; alias(nullptr);",
            true,
        ),
    ] {
        let source = format!(
            "int slots[16];\nvoid *worker(void *opaque) {{\n int thread = omp_get_thread_num();\n {body}\n return nullptr;\n}}\nvoid start() {{ pthread_create(&handle, nullptr, worker, nullptr); {extra_call} }}"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "body={body}, extra_call={extra_call}, findings={:#?}",
            report.findings
        );
        if !expected {
            let root = tempdir().unwrap();
            fs::write(root.path().join("candidate.cpp"), &source).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
            options.cpp_include_speculative = true;
            let speculative = analyze_cpp_path_with_options(root.path(), &options);
            assert!(
                speculative
                    .findings
                    .iter()
                    .flat_map(|f| &f.access_evidence)
                    .any(|access| access.in_concurrent_context
                        && access
                            .semantic_contexts
                            .iter()
                            .any(|c| c == "cpp_terminal_thread_store")),
                "terminal execution facts must remain auditable in speculative output"
            );
        }
    }
    let root = tempdir().unwrap();
    fs::write(root.path().join("entry.cpp"), "int slots[16];\nvoid *worker(void *opaque) {\n int thread = omp_get_thread_num();\n slots[thread] = 0;\n return nullptr;\n}\nvoid start() { pthread_create(&handle, nullptr, worker, nullptr); }").unwrap();
    fs::write(
        root.path().join("caller.cpp"),
        "void run() { while (more()) worker(nullptr); }",
    )
    .unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(
        !report.findings.is_empty(),
        "a visible ordinary caller in another file prevents the exit-only assumption"
    );
}

#[test]
fn local_callback_data_index_is_not_an_external_partition_parameter() {
    let local = analyze(
        r#"
        void decode() {
            std::function<void(size_t, int*)> fill;
            fill = [](size_t col_idx, int* values) { values[col_idx] += 1; };
            int values[16];
            for (size_t col = 0; col < 16; ++col) fill(col, values);
        }
    "#,
        &[CandidateKind::IndexedWrites],
    );
    assert!(local.findings.is_empty(), "{:#?}", local.findings);
    let escaped = analyze(
        r#"
        auto make_callback() {
            auto fill = [](size_t worker_id, int* values) { values[worker_id] += 1; };
            return fill;
        }
    "#,
        &[CandidateKind::IndexedWrites],
    );
    assert!(
        !escaped.findings.is_empty(),
        "escaping callback must retain API hypothesis"
    );
    let partition_call = analyze(
        r#"
        void update(size_t worker_id, int* values) {
            auto fill = [](size_t col_idx, int* data) { data[col_idx] += 1; };
            fill(worker_id, values);
        }
    "#,
        &[CandidateKind::IndexedWrites],
    );
    assert!(
        !partition_call.findings.is_empty(),
        "actual partition argument must remain eligible"
    );
    let asynchronous = analyze(
        r#"
        void launch(int* values) {
            auto fill = [](size_t worker_id, int* data) { data[worker_id] += 1; };
            std::thread worker([&] { fill(0, values); });
            worker.join();
        }
    "#,
        &[CandidateKind::IndexedWrites],
    );
    assert!(
        !asynchronous.findings.is_empty(),
        "a nested asynchronous caller is not a sequential local use"
    );
}

#[test]
fn callback_partition_follows_actual_argument_not_formal_spelling() {
    let report = analyze(
        "void update(int worker_id, int* values) {\n auto apply = [](int position, int* data) {\n data[position] += 1;\n };\n apply(worker_id, values);\n}",
        &[CandidateKind::IndexedWrites],
    );
    assert!(!report.findings.is_empty(), "{report:#?}");
    let ordinary = analyze(
        "void update(int column, int* values) {\n auto apply = [](int position, int* data) {\n data[position] += 1;\n };\n apply(column, values);\n}",
        &[CandidateKind::IndexedWrites],
    );
    assert!(ordinary.findings.is_empty(), "{ordinary:#?}");
    let before_binding = analyze(
        "void apply(int, int*);\nvoid update(int worker_id, int column, int* values) {\n apply(worker_id, values);\n auto apply = [](int position, int* data) {\n data[position] += 1;\n };\n apply(column, values);\n}",
        &[CandidateKind::IndexedWrites],
    );
    assert!(before_binding.findings.is_empty(), "{before_binding:#?}");
    let unrelated_argument = analyze(
        "void update(int worker_id, int column, int* values) {\n auto apply = [](int col_idx, int worker_id, int* data) {\n data[col_idx] += 1;\n };\n apply(column, worker_id, values);\n}",
        &[CandidateKind::IndexedWrites],
    );
    assert!(
        unrelated_argument.findings.is_empty(),
        "{unrelated_argument:#?}"
    );
}

#[test]
fn nonvirtual_base_name_does_not_expose_private_index_helper() {
    for (qualifier, expected) in [("", false), ("virtual", true)] {
        let source = format!(
            "struct Base {{ {qualifier} void update(int worker_id) {{}} }};\nclass State : public Base {{\n int values[16];\n void update(int worker_id) {{\n values[worker_id] += 1;\n }}\npublic:\n void consume() {{ for (int col = 0; col < 16; ++col) update(col); }}\n}};"
        );
        assert_eq!(
            !analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            expected,
            "{qualifier}"
        );
    }
}

#[test]
fn bounded_annotation_declaration_does_not_create_private_api_entry() {
    let source = "class Reader {\n int values[16];\n ANNOTATION inline void update(int worker_id);\npublic:\n void consume() { for (int col = 0; col < 16; ++col) update(col); }\n};\nvoid Reader::update(int worker_id) {\n values[worker_id]++;\n}";
    assert!(
        analyze(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    let exposed = source.replace("ANNOTATION inline", "public: ANNOTATION inline");
    assert!(
        !analyze(&exposed, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
}

#[test]
fn same_call_keeps_distinct_indexed_storage_witnesses() {
    let report = analyze(
        r#"
        int first[16];
        int second[16];
        void update(int index) {
            first[index] += 1;
            second[index] += 1;
        }
        void worker(int worker_id) {
            update(worker_id);
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    for field in ["first", "second"] {
        assert!(
            report.findings.iter().any(|finding| {
                finding.field_list.iter().any(|name| name == field)
                    && finding
                        .access_evidence
                        .iter()
                        .any(|access| access.function_name.as_deref() == Some("worker"))
            }),
            "missing call-site witness for {field}: {:#?}",
            report.findings
        );
    }
    let hashes = report
        .findings
        .iter()
        .map(|finding| &finding.finding_hash)
        .collect::<std::collections::HashSet<_>>();
    assert_eq!(hashes.len(), report.findings.len());
}

#[test]
fn static_data_const_fallback_and_array_initializers_are_not_shared_writes() {
    let report = analyze(
        r#"
        #define METRIC_STATS_PREFIX 1, 2, 3
        using MetricId = unsigned long;
        static const MetricId descriptor[] = { METRIC_STATS_PREFIX, 4 };
        static MetricId counters[16] = {0};
        int read() { return counters[0] + descriptor[0]; }
        "#,
        &[CandidateKind::StaticData, CandidateKind::IndexedWrites],
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn static_data_initializer_does_not_hide_a_later_mutation() {
    let report = analyze(
        r#"
        static int counters[16] = {0};
        void update(int worker_id) {
            counters[worker_id] += 1;
        }
        "#,
        &[CandidateKind::StaticData],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
    assert!(
        report.findings[0]
            .access_evidence
            .iter()
            .all(|access| access.line != 2)
    );
}

#[test]
fn indexed_writes_array_extents_and_string_keys_are_not_worker_indices() {
    let report = analyze(
        r#"
        int settings[16];
        void configure() {
            int scratch[WORKER_SLOTS] = {0};
            settings["contributing_workers"] = 4;
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn indexed_writes_opaque_call_arguments_are_not_return_value_partition_provenance() {
    for expression in [
        "opaque(worker)",
        "snprintf(buffer, sizeof(buffer), format, worker)",
        "opaque(omp_get_thread_num())",
        "table[worker]",
    ] {
        let source = format!(
            "int values[64];\nvoid update(int worker) {{\nint selected = {expression};\nvalues[selected] = 1;\nvalues[{expression}] = 2;\n}}"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert!(
            report.findings.is_empty(),
            "{expression}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn indexed_writes_transparent_arithmetic_retains_partition_origin_outside_an_opaque_call() {
    for expression in [
        "worker + stride",
        "(worker * 2) + 1",
        "worker + opaque(value)",
        "omp_get_thread_num() + 1",
    ] {
        let source = format!(
            "int values[64];\nvoid update(int worker, int stride, int value) {{\nint selected = {expression};\nvalues[selected] += 1;\n}}"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            report.findings.len(),
            1,
            "{expression}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn indexed_writes_spelling_and_local_loop_indices_do_not_establish_partition() {
    for index in [
        "DstIdx",
        "bucketIdx",
        "NextIdx",
        "ResetIdx",
        "slot",
        "scenario",
    ] {
        let source = format!(
            "int values[16];\nvoid initialize() {{\nfor (int {index} = 0; {index} < 16; ++{index}) {{\nvalues[{index}] = 0;\n}}\n}}"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert!(
            report.findings.is_empty(),
            "{index}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn indexed_writes_runtime_identity_propagates_through_renamed_local_variables() {
    let report = analyze(
        r#"
        int values[16];
        void update() {
            int identity = omp_get_thread_num();
            int selected = identity + 1;
            values[selected] += 1;
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
    assert!(
        report.findings[0]
            .access_evidence
            .iter()
            .all(|access| access.in_concurrent_context)
    );
    assert_eq!(
        report.findings[0]
            .static_pattern
            .as_ref()
            .unwrap()
            .parallelism_evidence,
        ParallelismEvidence::ConcurrentContext
    );
}

#[test]
fn indexed_writes_partition_provenance_is_scoped_and_killed_by_reassignment() {
    let report = analyze(
        r#"
        int values[16];
        void choose(int worker_id) {
            int selected = worker_id;
        }
        void initialize() {
            int selected = 0;
            values[selected] = 0;
        }
        void reset(int worker_id) {
            worker_id = 0;
            values[worker_id] = 0;
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn indexed_writes_retains_explicit_partition_api_and_returned_callback() {
    let report = analyze(
        r#"
        int values[16];
        struct Stage {
            void update(unsigned worker_id) {
                values[worker_id] += 1;
            }
        };
        auto callback() {
            return [](int scenario_idx) {
                values[scenario_idx] += 1;
            };
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
    assert_eq!(report.findings[0].access_evidence.len(), 2);
    assert!(report.findings[0].access_evidence.iter().all(|access| {
        !access.in_concurrent_context && access.evidence_kind == "api_index_partition"
    }));
    assert_eq!(
        report.findings[0]
            .static_pattern
            .as_ref()
            .unwrap()
            .parallelism_evidence,
        ParallelismEvidence::ExternalApiPotential
    );
}

#[test]
fn indexed_writes_retains_atomic_ticket_assigned_to_thread_local_identity() {
    let report = analyze(
        r#"
        static thread_local int identity = -1;
        int tickets;
        int values[16];
        void register_thread() {
            identity = atomic_fetch_add(&tickets, 1);
        }
        void update() {
            values[identity] += 1;
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
}

#[test]
fn tls_saved_api_partitions_remain_conditional_and_require_provenance() {
    for (declaration, registration, update, expected) in [
        (
            "static thread_local int role = -1;",
            "void attach(int worker_id) {\nrole = worker_id;\n}",
            "values[role] = input;",
            true,
        ),
        (
            "static __thread int role = -1;",
            "void attach(int worker_id) {\nrole = worker_id;\n}",
            "values[role] = input;",
            true,
        ),
        (
            "#ifndef ENABLED\nvoid unused() {}\n#else\n#define LOCAL static\nLOCAL __thread int role = -1;\n#endif",
            "void attach(int worker_id) {\nrole = worker_id;\n}",
            "int copy = role;\nvalues[copy] = input;",
            true,
        ),
        (
            "// thread_local int role;",
            "void attach(int worker_id) {\nrole = worker_id;\n}",
            "values[role] = input;",
            false,
        ),
        (
            "static thread_local int role = -1;",
            "class Owner {\nvoid attach(int worker_id) {\nrole = worker_id;\n}\n};",
            "values[role] = input;",
            false,
        ),
        (
            "static thread_local int role = -1;",
            "void attach(int coordinate) {\nrole = coordinate;\n}",
            "values[role] = input;",
            false,
        ),
        (
            "static int role = -1;",
            "void attach(int worker_id) {\nrole = worker_id;\n}",
            "values[role] = input;",
            false,
        ),
        (
            "static thread_local int role = -1;",
            "void attach(int worker_id) {\nint role = worker_id;\n}",
            "values[role] = input;",
            false,
        ),
        (
            "static thread_local int role = -1;",
            "void attach(int worker_id, int role) {\nrole = worker_id;\n}",
            "values[role] = input;",
            false,
        ),
        (
            "static thread_local int role = -1;",
            "void attach(int worker_id) {\nrole = worker_id;\n}",
            "role = 0;\nvalues[role] = input;",
            false,
        ),
        (
            "static thread_local int role = -1;",
            "void attach(int worker_id) {\nrole = worker_id;\nunknown(&role);\n}",
            "values[role] = input;",
            false,
        ),
    ] {
        let source = format!(
            "{declaration}\nint values[16];\n{registration}\nvoid update(int input) {{\n{update}\n}}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{source}: {report:#?}"
        );
        for finding in &report.findings {
            assert!(
                finding
                    .access_evidence
                    .iter()
                    .all(|e| !e.in_concurrent_context)
            );
            assert_eq!(
                finding
                    .static_pattern
                    .as_ref()
                    .unwrap()
                    .parallelism_evidence,
                ParallelismEvidence::ExternalApiPotential
            );
        }
    }
}

#[test]
fn tls_registration_write_survives_serialized_cleanup_of_the_same_slots() {
    for size in [32, 64, 128] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("slots.cpp"),
            r#"
            #define TAKE(x) pthread_mutex_lock(&x)
            #define GIVE(x) pthread_mutex_unlock(&x)
            pthread_mutex_t gate;
            thread_local int identity = -1;
            int values[16];
            void attach(int worker_id) {
                identity = worker_id;
            }
            void publish(int input) {
                TAKE(gate);
                prepare();
                GIVE(gate);
                values[identity] = input;
            }
            void cleanup(int coordinate) {
                TAKE(gate);
                values[coordinate] = 0;
                GIVE(gate);
            }
            void finish(int worker_id) {
                cleanup(worker_id);
            }
        "#,
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions {
                cache_line_size: size,
                ..AnalysisOptions::with_rules(&[RuleId::ContiguousElements])
            },
        );
        assert_eq!(report.findings.len(), 1, "B={size}: {report:#?}");
        assert!(
            report.findings[0].access_evidence.iter().all(|e| {
                e.function_name.as_deref() == Some("publish") && !e.in_concurrent_context
            }),
            "B={size}: {report:#?}"
        );
    }
}

#[test]
fn indexed_writes_retains_source_routing_into_thread_count() {
    let report = analyze(
        r#"
        int values[16];
        struct Configuration { int numWorkers; } config;
        void dispatch(unsigned hash) {
            int selected = hash % config.numWorkers;
            values[selected] += 1;
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
}

#[test]
fn indexed_writes_distinguishes_pointer_pointees_from_inline_array_members() {
    let report = analyze(
        r#"
        struct Value { int count; };
        Value* pointers[16];
        Value inline_values[16];
        void update(int worker_id) {
            pointers[worker_id]->count += 1;
            inline_values[worker_id].count += 1;
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
    assert!(
        report.findings[0]
            .field_list
            .contains(&"inline_values".to_string())
    );
}

#[test]
fn indexed_writes_retains_indexed_view_mutation_from_partition_descriptor() {
    let report = analyze(
        r#"
        struct Ticket { const int state_idx_; int value; };
        struct Pool {
            Kokkos::View<int*> state_;
            void release(const Ticket & ticket) {
                state_(ticket.state_idx_) = ticket.value;
            }
        };
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
}

#[test]
fn immutable_descriptor_api_binds_type_and_selectable_constructor_input() {
    let source = r#"
struct Ticket {
    int payload;
    const int coordinate;
    Ticket(int value, int selected) : payload(value), coordinate(selected) {}
};
struct Pool {
    std::vector<int> values;
    void release(const Ticket & ticket) {
        values[ticket.coordinate] = ticket.payload;
    }
};
"#;
    let report = analyze(source, &[CandidateKind::IndexedWrites]);
    assert!(!report.findings.is_empty(), "{report:#?}");
    for input in [
        source.replace("coordinate(selected)", "coordinate(0)"),
        source.replace("const int coordinate", "int coordinate"),
        source.replace("    Ticket(int", "private:\n    Ticket(int"),
        source
            .replace(
                "struct Pool",
                "struct Other { int payload; const int coordinate = 0; Other() {} };\nstruct Pool",
            )
            .replace("const Ticket &", "const Other &"),
    ] {
        assert!(
            analyze(&input, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{input}"
        );
    }
}

#[test]
fn descriptor_constructor_annotations_require_all_macro_definitions() {
    let source = r#"
class Ticket {
public:
    const int coordinate;
    DECLARE_INLINE
    Ticket(int selected) : coordinate(selected) {}
};
std::vector<int> values;
void release(const Ticket & ticket) {
    values[ticket.coordinate]++;
}
"#;
    for (definitions, expected) in [
        ("#define DECLARE_INLINE inline\n", true),
        (
            "#define INNER __host__ __device__ inline\n#define DECLARE_INLINE INNER\n",
            true,
        ),
        (
            "#if MODE\n#define DECLARE_INLINE inline __attribute__((annotate(\"marker\")))\n#else\n#define DECLARE_INLINE inline\n#endif\n",
            true,
        ),
        ("#define DECLARE_INLINE unknown\n", false),
        (
            "#if MODE\n#define DECLARE_INLINE inline\n#else\n#define DECLARE_INLINE unknown\n#endif\n",
            false,
        ),
        (
            "#define DECLARE_INLINE inline\n#undef DECLARE_INLINE\n",
            false,
        ),
        (
            "#define DECLARE_INLINE inline\n# undef DECLARE_INLINE\n",
            false,
        ),
        ("#define DECLARE_INLINE(x) inline\n", false),
        (
            "#define DECLARE_INLINE INNER\n#define INNER DECLARE_INLINE\n",
            false,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("annotations.hpp"), definitions).unwrap();
        fs::write(
            root.path().join("candidate.hpp"),
            format!("#include \"annotations.hpp\"\n{source}"),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{definitions}\n{report:#?}"
        );
    }
}

#[test]
fn indexed_writes_binds_a_partitioned_span_back_to_its_vector_storage() {
    let report = analyze(
        r#"
        template <typename T>
        class span {
        public:
            span(T *, unsigned long);
            span slice(unsigned long, unsigned long) const;
            T &operator[](unsigned long) const;
        };
        void ppc(unsigned alphabet_size, unsigned levels) {
            std::vector<unsigned> initial_hist_v(alphabet_size * levels, 0);
            span<unsigned> initial_hist{initial_hist_v.data(), initial_hist_v.size()};
        #pragma omp parallel
            {
                unsigned omp_rank = omp_get_thread_num();
                auto initial_hist_ptr = initial_hist.slice(
                    alphabet_size * omp_rank,
                    alphabet_size * (omp_rank + 1));
                unsigned c = 0;
                initial_hist_ptr[c]++;
            }
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.field_list.contains(&"initial_hist_v".to_string())),
        "span backing storage was not retained: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_keeps_opaque_glib_worker_indices_in_speculative_output() {
    let report = analyze_speculative(
        r#"
        long values[16];
        void *worker(void *opaque) {
            int slot = (long)opaque;
            // Exercise the actual worker region, not a one-shot exit store.
            while (keep_working()) {
                values[slot] = 1;
            }
            return 0;
        }
        void start() {
            g_thread_new("worker", &worker, (void *)1);
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
    assert!(report.findings[0].access_evidence[0].in_concurrent_context);
}

#[test]
fn indexed_writes_tracks_backslash_continued_openmp_loop_body() {
    let report = analyze(
        r#"
        void update(int count) {
            int *const counters = malloc(16 * sizeof(int));
        #ifdef _OPENMP
        #pragma omp parallel for default(none) \
            shared(counters, count)
        #endif
            for (int i = 0; i < count; ++i)
            {
                int bucket = i % 16;
        #ifdef _OPENMP
        #pragma omp atomic
        #endif
                counters[bucket]++;
            }
        }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
    assert_eq!(report.findings[0].field_list, vec!["counters"]);
    assert!(report.findings[0].access_evidence[0].in_concurrent_context);
}

#[test]
fn indexed_writes_resolves_multiline_alias_to_contiguous_container() {
    let report = analyze(
        r#"
        using ValuesPerWorker =
            typename std::conditional<UseDeque, std::deque<int>, std::vector<int>>::type;
        struct Stage {
            ValuesPerWorker values;
            void update(unsigned worker_id) {
                values[worker_id] += 1;
            }
        };
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert_eq!(report.findings.len(), 1, "{:#?}", report.findings);
    assert_eq!(report.findings[0].field_list, vec!["values"]);

    let report = analyze(
        r#"
        using ValuesByKey = std::map<int, int>;
        ValuesByKey values;
        void update(unsigned worker_id) { values[worker_id] += 1; }
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}
#[test]
fn private_sequential_helper_index_is_not_an_external_partition_api() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("state.h"),
        r#"
        class Reader {
            unsigned values[16];
            void update(unsigned column_index);
        public:
            void read();
        };
    "#,
    )
    .unwrap();
    std::fs::write(
        dir.path().join("state.cpp"),
        r#"
        #include "state.h"
        void Reader::update(unsigned column_index) {
            values[column_index]++;
        }
        void Reader::read() {
            for (unsigned column_index = 0; column_index < 16; ++column_index)
                update(column_index);
        }
    "#,
    )
    .unwrap();
    let report = false_sharing_detector::cpp_detection::analyze_cpp_path_with_options(
        dir.path(),
        &false_sharing_detector::types::AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(report.findings.is_empty(), "private helper: {report:#?}");
    let header = std::fs::read_to_string(dir.path().join("state.h")).unwrap();
    std::fs::write(
        dir.path().join("state.h"),
        header.replace("void read();", "void read(unsigned worker_id);"),
    )
    .unwrap();
    std::fs::write(
        dir.path().join("state.cpp"),
        r#"
        #include "state.h"
        void Reader::update(unsigned column_index) {
            values[column_index]++;
        }
        void Reader::read(unsigned worker_id) {
            update(worker_id);
        }
    "#,
    )
    .unwrap();
    let report = false_sharing_detector::cpp_detection::analyze_cpp_path_with_options(
        dir.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(
        !report.findings.is_empty(),
        "caller partition must propagate: {report:#?}"
    );
    for access in ["public:", "protected:", "private: virtual"] {
        let report = analyze(
            &format!(
                "class State {{\n unsigned values[16];\n {access}\n void update(unsigned worker_id) {{\n values[worker_id]++;\n }}\n }};"
            ),
            &[CandidateKind::IndexedWrites],
        );
        assert!(
            !report.findings.is_empty(),
            "exposed/virtual API {access}: {report:#?}"
        );
    }
}

#[test]
fn private_implicit_virtual_override_keeps_partition_api_evidence() {
    for base in [
        "struct Base { virtual void update(unsigned worker_id) = 0; };",
        "class Base;",
    ] {
        let report = analyze(
            &format!(
                "{base}\nclass State : public Base {{\n unsigned values[16];\n void update(unsigned worker_id) {{\n values[worker_id]++;\n }}\n}};"
            ),
            &[CandidateKind::IndexedWrites],
        );
        assert!(
            !report.findings.is_empty(),
            "base exposure unresolved: {report:#?}"
        );
    }
    let report = analyze(
        "struct Base { virtual void unrelated() = 0; };\nclass Reader : public Base {\nunsigned values[16];\nvoid update(unsigned column_index) {\nvalues[column_index]++;\n}\npublic:\nvoid read() {\nfor (unsigned i=0; i<16; ++i) update(i);\n}\n};",
        &[CandidateKind::IndexedWrites],
    );
    assert!(
        report.findings.is_empty(),
        "known non-overriding helper: {report:#?}"
    );
}

#[test]
fn unrelated_member_parse_error_does_not_expose_private_index_helper() {
    let source = r#"
        class Reader {
            unsigned values[16];
            ANNOTATION inline bool other(int value);
        private:
            void update(unsigned worker_id) {
                values[worker_id]++;
            }
        public:
            void read() {
                for (unsigned i=0; i<16; ++i) update(i);
            }
        };
        "#;
    let report = analyze(source, &[CandidateKind::IndexedWrites]);
    assert!(report.findings.is_empty(), "unrelated syntax: {report:#?}");
    let bounded = analyze(
        &source.replace("private:", ""),
        &[CandidateKind::IndexedWrites],
    );
    assert!(
        bounded.findings.is_empty(),
        "bounded declaration: {bounded:#?}"
    );
    let unresolved = analyze(
        &source
            .replace("private:", "")
            .replace("ANNOTATION inline bool other(int value);", "???;"),
        &[CandidateKind::IndexedWrites],
    );
    assert!(
        !unresolved.findings.is_empty(),
        "unbounded syntax without access reset: {unresolved:#?}"
    );
}
#[test]
fn callback_signature_normalizes_only_uniquely_bound_record_types() {
    let consumer = r#"
        namespace API {
            struct Context {};
            void invoke(Context & context, const std::function<void(unsigned)> & action);
        }
        class Worker {
            unsigned values[16];
            void update(unsigned worker_id) { values[worker_id]++; }
        public:
            void parse(API::Context & context) {
                auto apply = [this](unsigned position) { update(position); };
                API::invoke(context, apply);
            }
        };
    "#;
    for (definition, expected) in [
        (
            "namespace API { void invoke(API::Context & context, const std::function<void(unsigned)> & action) { action(0); } }",
            false,
        ),
        (
            "namespace Other { struct Context {}; } namespace API { void invoke(Other::Context & context, const std::function<void(unsigned)> & action) { action(0); } }",
            true,
        ),
        (
            "namespace Other { struct Context {}; } namespace API { using Context = Other::Context; void invoke(Other::Context & context, const std::function<void(unsigned)> & action) { action(0); } }",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("consumer.cpp"), consumer).unwrap();
        fs::write(root.path().join("wrapper.cpp"), definition).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{definition}: {report:#?}"
        );
    }
}

#[test]
fn inline_callback_argument_requires_a_bound_synchronous_contract() {
    for (definition, expected) in [
        (
            "template<class F> void invoke(unsigned value, F && action) { action(value); }",
            false,
        ),
        (
            "void invoke(unsigned value, const std::function<void(unsigned)> & action) { action(value); }",
            false,
        ),
        (
            "template<class F> void invoke(unsigned value, F && action) { save(action); }",
            true,
        ),
        (
            "template<class F> void invoke(unsigned value, F && action) { queue([&] { action(value); }); }",
            true,
        ),
        (
            "void invoke(unsigned value, Callback action) { action(value); }",
            true,
        ),
        (
            "template<class F> void invoke(unsigned value, F && action) { action(value); } void invoke(unsigned, Callback);",
            true,
        ),
    ] {
        for target in ["API::invoke", "::API::invoke", "Unknown::invoke"] {
            let root = tempdir().unwrap();
            fs::write(
                root.path().join("wrapper.hpp"),
                format!("namespace API {{ {definition} }}"),
            )
            .unwrap();
            fs::write(
                root.path().join("consumer.cpp"),
                format!(
                    r#"
class Worker {{
    unsigned values[16];
    void update(unsigned worker_id) {{ values[worker_id]++; }}
public:
    void parse() {{
        {target}(0, [this](unsigned position) {{ update(position); }});
    }}
}};
"#
                ),
            )
            .unwrap();
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
            );
            assert_eq!(
                !report.findings.is_empty(),
                expected || target == "Unknown::invoke",
                "target={target}, definition={definition}: {report:#?}"
            );
        }
    }
}

#[test]
fn inline_synchronous_callback_retains_capture_and_parallel_escapes() {
    for invocation in [
        "API::invoke(0, [this, token = publish(this)](unsigned position) { update(position); });",
        "API::invoke(0, [this](unsigned position) { co_await suspend(); update(position); });",
        "#pragma omp parallel for\n for (unsigned i=0; i<16; ++i) { API::invoke(i, [this](unsigned position) { update(position); }); }",
    ] {
        let source = format!(
            r#"
namespace API {{ template<class F> void invoke(unsigned value, F && action) {{ action(value); }} }}
class Worker {{
    unsigned values[16];
    void update(unsigned worker_id) {{ values[worker_id]++; }}
public:
    void parse() {{
        {invocation}
    }}
}};
"#
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert!(!report.findings.is_empty(), "{invocation}: {report:#?}");
    }
}

#[test]
fn qualified_template_callback_contract_preserves_the_deduced_closure() {
    let consumer = r#"
        class Worker {
            unsigned values[16];
            void update(unsigned worker_id) { values[worker_id]++; }
        public:
            void parse() {
                auto apply = [this](unsigned position) { update(position); };
                API::invoke(0, apply);
            }
        };
    "#;
    for (body, extra, variable_type, expected) in [
        ("action(value);", "", "auto", false),
        ("save(action);", "", "auto", true),
        ("queue([&] { action(value); });", "", "auto", true),
        (
            "action(value);",
            "void invoke(unsigned, Callback &);",
            "auto",
            true,
        ),
        ("action(value);", "", "Callback", true),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("consumer.cpp"),
            consumer.replace("auto apply", &format!("{variable_type} apply")),
        )
        .unwrap();
        fs::write(root.path().join("wrapper.hpp"), format!(
            "namespace API {{ template<class F> void invoke(unsigned value, F && action) {{ {body} }} {extra} }}"
        )).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "body={body}, extra={extra}, type={variable_type}: {report:#?}"
        );
    }
}

#[test]
fn cross_file_callback_contract_requires_matching_declaration_and_body() {
    let consumer = r#"
        namespace API { void invoke(unsigned value, Callback & action); }
        class Worker {
            unsigned values[16];
            void update(unsigned worker_id) { values[worker_id]++; }
        public:
            void parse() {
                auto apply = [this](unsigned position) { update(position); };
                for (unsigned column=0; column<16; ++column) ::API::invoke(column, apply);
            }
        };
    "#;
    for (definition, expected) in [
        (
            "namespace API { template<class F> static void leaf(F && cb) { cb(0); } void invoke(unsigned value, Callback & action) { leaf([&](unsigned) { action(value); }); } }",
            false,
        ),
        (
            "namespace API { template<class F> static void leaf(F && cb) { save(cb); } void invoke(unsigned value, Callback & action) { leaf([&](unsigned) { action(value); }); } }",
            true,
        ),
        (
            "namespace API { void invoke(unsigned value, Callback & action) { action(value); } }",
            false,
        ),
        (
            "namespace API { void invoke(unsigned value, Callback & action) { save(action); } }",
            true,
        ),
        (
            "namespace Other { void invoke(unsigned value, Callback & action) { action(value); } }",
            true,
        ),
        (
            "namespace API { void invoke(unsigned value, Callback & action) { queue([&]{action(value);}); } }",
            true,
        ),
        (
            "namespace API { void invoke(int value, Callback & action) { action(value); } }",
            true,
        ),
    ] {
        for (callback_type, unknown_conversion) in [
            ("const std::function<void(unsigned)> &", false),
            ("Callback &", true),
        ] {
            for (call_name, shadow) in [
                ("::API::invoke", ""),
                ("API::invoke", ""),
                ("API::invoke", "using API = Shadow;"),
                ("API::invoke", "typedef Shadow API;"),
            ] {
                let root = tempdir().unwrap();
                fs::write(
                    root.path().join("consumer.cpp"),
                    consumer
                        .replace("Callback &", callback_type)
                        .replace("::API::invoke", call_name)
                        .replace("class Worker {", &format!("class Worker {{ {shadow}")),
                )
                .unwrap();
                fs::write(
                    root.path().join("wrapper.cpp"),
                    definition.replace("Callback &", callback_type),
                )
                .unwrap();
                let report = analyze_cpp_path_with_options(
                    root.path(),
                    &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
                );
                assert_eq!(
                    !report.findings.is_empty(),
                    expected || unknown_conversion || !shadow.is_empty(),
                    "{definition}, {call_name}, {shadow}, {callback_type}: {report:#?}"
                );
            }
        }
    }
}

#[test]
fn private_callback_summary_composes_forwarding_and_inline_wrappers() {
    let source = r#"
        template <typename F> static void leaf(F && action) { action(); }
        template <typename F> static void bridge(F && action) { leaf([&] { action(); }); }
        template <typename F> static void forward(F && action) { bridge(action); }
        class Worker {
            unsigned values[16];
            void update(unsigned worker_id) { values[worker_id]++; }
        public:
            void parse() {
                auto apply = [this] { for (unsigned i=0; i<16; ++i) update(i); };
                forward(apply);
            }
        };
    "#;
    assert!(
        analyze(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    let explicit_result = source
        .replace(
            "template <typename F> static void leaf",
            "template <typename Result, typename F> static void leaf",
        )
        .replace("leaf([&]", "leaf<void>([&]");
    assert!(
        analyze(&explicit_result, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    let explicit_callback = explicit_result.replace("leaf<void>(", "leaf<void, Callback>(");
    assert!(
        !analyze(&explicit_callback, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    for variant in [
        source.replace("{ action(); }", "{ save(action); }"),
        source.replace("bridge(action);", "forward(action);"),
        source.replace("leaf([&] { action(); });", "unknown([&] { action(); });"),
        source.replace(
            "leaf([&] { action(); });",
            "leaf([&] { action(); co_await event(); });",
        ),
    ] {
        assert!(
            !analyze(&variant, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{variant}"
        );
    }
}

#[test]
fn private_callback_static_wrapper_uses_selected_parameter_body() {
    let source = r#"
        static void invoke(unsigned value, const std::function<void(unsigned)> & action) { action(value); }
        class Worker {
            unsigned values[16];
            void update(unsigned worker_id) { values[worker_id]++; }
        public:
            void parse() {
                auto apply = [this](unsigned position) { update(position); };
                for (unsigned column = 0; column < 16; ++column) invoke(column, apply);
            }
        };
    "#;
    assert!(
        analyze(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    for body in [
        "save(action);",
        "auto copy = action; copy(value);",
        "queue([&] { action(value); });",
        "action = replacement; action(value);",
    ] {
        let variant = source.replace("action(value);", body);
        assert!(
            !analyze(&variant, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{variant}"
        );
    }
    let overloaded = format!("void invoke(int, Callback&);\n{source}");
    assert!(
        !analyze(&overloaded, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    let namespaced = format!("namespace Hidden {{ {source} }}");
    assert!(
        analyze(&namespaced, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    let unrelated = format!(
        "namespace Other {{ static void invoke(unsigned value, Callback & action) {{ save(action); }} }}\n{namespaced}"
    );
    assert!(
        analyze(&unrelated, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    let unsafe_target = format!(
        "namespace Other {{ static void invoke(unsigned value, Callback & action) {{ action(value); }} }}\n{}",
        namespaced.replace("action(value);", "save(action);")
    );
    assert!(
        !analyze(&unsafe_target, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    for variant in [
        source.replace("const std::function<void(unsigned)>", "Callback"),
        source.replace("class Worker {", "class Worker : UnknownBase {"),
        source.replace("void parse() {", "void parse() { Callback invoke;"),
        source.replace("class Worker {", "class Worker { Callback invoke;"),
        format!("namespace {{ {source} }}"),
        source.replace(
            "static void invoke(unsigned value, const std::function<void(unsigned)> & action) { action(value); }",
            "static void invoke(Callback & first, Callback & action) { first(0); save(action); }",
        ).replace("invoke(column, apply)", "invoke(other, apply)"),
    ] {
        assert!(!analyze(&variant, &[CandidateKind::IndexedWrites]).findings.is_empty(), "{variant}");
    }
}

#[test]
fn local_this_callback_direct_calls_do_not_expose_private_index_api() {
    let source = r#"
        class Worker {
            unsigned values[16];
            void update(unsigned worker_id) { values[worker_id]++; }
        public:
            void parse() {
                auto apply = [this](unsigned position) { update(position); };
                for (unsigned column = 0; column < 16; ++column) apply(column);
            }
        };
    "#;
    assert!(
        analyze(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    for invocation in [
        "save(apply);",
        "auto copy = apply; copy(0);",
        "auto later = [&] { apply(0); }; save(later);",
        "apply = factory(); apply(0);",
        "#pragma omp parallel for\nfor (unsigned column = 0; column < 16; ++column) apply(column);",
    ] {
        let variant = source.replace(
            "for (unsigned column = 0; column < 16; ++column) apply(column);",
            invocation,
        );
        assert!(
            !analyze(&variant, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{variant}"
        );
    }
}

#[test]
fn private_helper_reachable_from_escaping_this_callback_keeps_partition_evidence() {
    let report = analyze(
        r#"
        class Worker {
            unsigned values[16];
            void update(unsigned worker_id) {
                values[worker_id]++;
            }
        public:
            void start() {
                for (unsigned i = 0; i < 16; ++i)
                    executor.submit([this, i] { update(i); });
            }
        };
        "#,
        &[CandidateKind::IndexedWrites],
    );
    assert!(
        !report.findings.is_empty(),
        "escaped receiver callback: {report:#?}"
    );
}

#[test]
fn immediately_invoked_coroutine_does_not_prove_private_receiver_synchronous() {
    let source = r#"
        class Worker {
            unsigned values[16];
            void update(unsigned worker_id) { values[worker_id]++; }
        public:
            void start() {
                auto pending = [this]() -> Task {
                    co_await next_event();
                    for (unsigned i=0; i<16; ++i) update(i);
                }();
                executor.submit(pending);
            }
        };
    "#;
    let report = analyze(source, &[CandidateKind::IndexedWrites]);
    assert!(!report.findings.is_empty(), "coroutine escape: {report:#?}");

    let synchronous = source
        .replace("auto pending =", "")
        .replace("-> Task", "")
        .replace("co_await next_event();", "")
        .replace("executor.submit(pending);", "");
    let report = analyze(&synchronous, &[CandidateKind::IndexedWrites]);
    assert!(report.findings.is_empty(), "ordinary IIFE: {report:#?}");
}

fn analyze_private_array(source: &str) -> Report {
    let root = tempdir().unwrap();
    fs::write(root.path().join("candidate.cpp"), source).unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    options.cpp_include_speculative = true;
    analyze_cpp_path_with_options(root.path(), &options)
}

#[test]
fn cpp_scalar_copy_from_private_array_preserves_ownership() {
    for (copy, expected) in [
        ("int value = local[worker_id]; consume(value);", false),
        (
            "const float value = (local[worker_id]); consume(value);",
            false,
        ),
        ("int &value = local[worker_id]; consume(value);", true),
        ("const int &value = local[worker_id]; consume(value);", true),
        ("int *value = &local[worker_id]; consume(value);", true),
        ("Wrapper value = local[worker_id]; consume(value);", true),
        (
            "auto value = [&] { int item = local[worker_id]; return item; }; consume(value);",
            true,
        ),
    ] {
        let source = format!(
            "void run(int worker_id) {{\nint local[8] = {{}};\nfor (int n=0; n<100; ++n) {{\nlocal[worker_id]++;\n{copy}\n}}\n}}\n"
        );
        assert_eq!(
            !analyze_private_array(&source).findings.is_empty(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn cpp_multidimensional_private_array_requires_complete_value_indexing() {
    for (read, expected) in [
        ("int value = local[worker_id][0]; consume(value);", false),
        ("consume(local[worker_id][0] + 1);", false),
        ("consume(local[worker_id] + 1);", true),
        ("int *value = local[worker_id]; consume(value);", true),
        ("consume(local[worker_id][0]);", true),
    ] {
        let source = format!(
            "void run(int worker_id) {{\nint local[8][4] = {{}};\nfor (int n=0; n<100; ++n) {{\nlocal[worker_id][0]++;\n{read}\n}}\n}}\n"
        );
        assert_eq!(
            !analyze_private_array(&source).findings.is_empty(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn worksharing_keeps_automatic_storage_in_the_encountering_thread() {
    for (directive, expected) in [
        ("omp for", false),
        ("omp for collapse(1) schedule(static) nowait", false),
        ("omp for simd", false),
        ("omp parallel for", true),
        ("omp taskloop", true),
        ("omp target teams distribute parallel for", true),
        ("omp for reduction(+:scratch)", true),
        ("omp for \\\n schedule(static)", true),
    ] {
        let source = format!(
            "void run() {{\n#pragma omp parallel\n{{\nint scratch[16] = {{}};\n#pragma {directive}\nfor (int i=0; i<16; ++i) {{\nscratch[i]++;\n}}\n#pragma omp critical(merge)\n{{\nint value = scratch[0];\nconsume(value);\n}}\n#pragma omp barrier\n#pragma omp single\n{{ int value = scratch[1]; consume(value); }}\n}}\n}}\n"
        );
        assert_eq!(
            !analyze_private_array(&source).findings.is_empty(),
            expected,
            "{source}"
        );
    }
    // A publication in the same team still invalidates exclusive ownership.
    let escaped = "void run() {\n#pragma omp parallel\n{\nint scratch[16];\npublish(scratch);\n#pragma omp for\nfor(int i=0;i<16;++i) scratch[i]++;\n}\n}";
    assert!(!analyze_private_array(escaped).findings.is_empty());
}

#[test]
fn scalar_macro_body_can_preserve_private_array_ownership() {
    for (definition, expected) in [
        (
            "#define APPLY(a,b) { const float tmp=(b); (b)=(a); (a)=tmp; }",
            false,
        ),
        (
            "#define APPLY(a,b) do { int tmp=(a); (a)=(b); (b)=tmp; } while(0)",
            false,
        ),
        ("#define APPLY(a,b) publish(&(a))", true),
        ("#define APPLY(a,b) { saved=&(a); }", true),
        ("#define APPLY(a,b) { Wrapper tmp(a); (b)=tmp; }", true),
        ("#define APPLY(a,b) { int &tmp=(a); consume(tmp); }", true),
        (
            "#define APPLY(a,b) { const float tmp=(b); (b)=(a); (a)=tmp; }\n#undef APPLY",
            true,
        ),
        ("#ifdef MODE\n#define APPLY(a,b) { (a)=(b); }\n#endif", true),
        (
            "#define APPLY(a,b) { (a)=(b); }\n#define APPLY(a,b) publish(&(a))",
            true,
        ),
    ] {
        let source = format!(
            "{definition}\nfloat scratch[32];\nvoid run(int worker_id) {{\nfloat local[16]={{}};\nfor(int i=0;i<16;++i) {{\nlocal[worker_id]++;\nAPPLY(local[worker_id],local[i]);\n}}\n}}"
        );
        assert_eq!(
            !analyze_private_array(&source).findings.is_empty(),
            expected,
            "{source}"
        );
    }
    // The other macro operand may overload assignment/conversion and retain
    // the first argument's address; only known scalar operands are admitted.
    let source = "#define APPLY(a,b) { (b)=(a); }\nvoid run(int worker_id, Wrapper &sink) {\nint local[16]={};\nfor(int i=0;i<16;++i) {\nlocal[worker_id]++;\nAPPLY(local[worker_id],sink);\n}\n}";
    assert!(!analyze_private_array(source).findings.is_empty());
}

#[test]
fn scalar_macro_contract_does_not_erase_outer_escape_contexts() {
    for (use_site, expected) in [
        (
            "int value=IDENTITY(local[worker_id]); consume(value);",
            false,
        ),
        ("consume(IDENTITY(local[worker_id]));", true),
        (
            "int &value=IDENTITY(local[worker_id]); consume(value);",
            true,
        ),
        ("consume([&] { IDENTITY(local[worker_id])++; });", true),
    ] {
        let source = format!(
            "#define IDENTITY(x) (x)\nvoid run(int worker_id) {{\nint local[16]={{}};\nfor(int i=0;i<16;++i) {{\nlocal[worker_id]++;\n{use_site}\n}}\n}}"
        );
        assert_eq!(
            !analyze_private_array(&source).findings.is_empty(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn later_macro_undef_does_not_retroactively_publish_local_arrays() {
    let source = "#define APPLY(a,b) { float temp=(a); (a)=(b); (b)=temp; }\nvoid run(int worker_id) {\nfloat local[16]={};\nfor(int i=0;i<16;++i) {\nlocal[worker_id]++;\nAPPLY(local[worker_id],local[i]);\n}\n}\n#undef APPLY\n";
    assert!(analyze_private_array(source).findings.is_empty());
    let later = "void later(int worker_id) {\nfloat local[16]={};\nfor(int i=0;i<16;++i) {\nlocal[worker_id]++;\nAPPLY(local[worker_id],local[i]);\n}\n}\n";
    assert!(
        !analyze_private_array(&format!("{source}{later}"))
            .findings
            .is_empty()
    );
}

#[test]
fn builtin_array_arithmetic_consumes_values_without_publishing_storage() {
    for (declaration, expression, expected) in [
        ("", "local[worker_id] * worker_id", false),
        ("", "local[worker_id] * i", false),
        (
            "int other[16]={};",
            "local[worker_id] - other[worker_id]",
            false,
        ),
        (
            "float other[2][16]={};",
            "other[0][worker_id] - local[worker_id]",
            false,
        ),
        ("int scale=2;", "local[worker_id] * scale", false),
        (
            "Wrapper other[16];",
            "local[worker_id] - other[worker_id]",
            true,
        ),
        ("Wrapper scale;", "local[worker_id] * scale", true),
    ] {
        let source = format!(
            "void run(int worker_id) {{\nint local[16]={{}};\n{declaration}\nfor(int i=0;i<16;++i) {{\nlocal[worker_id]++;\nconsume({expression});\n}}\n}}"
        );
        assert_eq!(
            !analyze_private_array(&source).findings.is_empty(),
            expected,
            "{source}"
        );
    }
    let shadowed = "void run(int worker_id) {\nint local[16]={};\nint scale=2;\n{\nWrapper scale;\nfor(int i=0;i<16;++i) {\nlocal[worker_id]++;\nconsume(local[worker_id]*scale);\n}\n}\n}";
    assert!(!analyze_private_array(shadowed).findings.is_empty());
}

#[test]
fn overloaded_operand_may_escape_before_a_later_scalar_copy() {
    for operation in [
        "int value=local[worker_id]*scale; consume(value);",
        "consume((int)(local[worker_id]*scale));",
    ] {
        let source = format!(
            "void run(int worker_id) {{\nint local[16]={{}};\nWrapper scale;\nfor(int i=0;i<16;++i) {{\nlocal[worker_id]++;\n{operation}\n}}\n}}"
        );
        assert!(
            !analyze_private_array(&source).findings.is_empty(),
            "{source}"
        );
    }
    let source = "void run(int worker_id) {\nint local[16]={};\nint scale=2;\nfor(Wrapper scale; keep_going(); step()) {\nlocal[worker_id]++;\nconsume(local[worker_id]*scale);\n}\n}";
    assert!(!analyze_private_array(source).findings.is_empty());
}

#[test]
fn value_references_in_control_headers_do_not_shadow_outer_bindings() {
    let source = "void run(int worker_id) {\nint local[16]={};\nint other[16]={};\nfor(int row=0;row<16;++row) {\nfor(int col=row;col<16;++col) {\nlocal[worker_id]++;\nif(other[worker_id]>0) {\nconsume((local[worker_id]-other[worker_id])*row);\n}\n}\n}\n}";
    assert!(analyze_private_array(source).findings.is_empty());
}

#[test]
fn static_scalar_parameters_receive_copies_of_array_elements() {
    for (parameter, expected) in [
        ("float value", false),
        ("const float &value", true),
        ("Wrapper value", true),
    ] {
        let source = format!(
            "static void accept({parameter}) {{ consume(value); }}\nvoid run(int worker_id) {{\nfloat local[16]={{}};\nfor(int n=0;n<16;++n) {{\nlocal[worker_id]++;\naccept(local[worker_id]);\n}}\n}}"
        );
        assert_eq!(
            !analyze_private_array(&source).findings.is_empty(),
            expected,
            "{source}"
        );
    }
    for extra in [
        "static void accept(float &value) { publish(&value); }",
        "#define accept(value) publish(&(value))",
    ] {
        let source = format!(
            "static void accept(float value) {{ consume(value); }}\n{extra}\nvoid run(int worker_id) {{\nfloat local[16]={{}};\nfor(int n=0;n<16;++n) {{\nlocal[worker_id]++;\naccept(local[worker_id]);\n}}\n}}"
        );
        assert!(
            !analyze_private_array(&source).findings.is_empty(),
            "{source}"
        );
    }
}

#[test]
fn scalar_parameter_contract_keeps_callable_binding_boundaries() {
    for body in [
        "auto accept = [&](const float &x) { publish(&x); };\nfor(int n=0;n<16;++n) {\nlocal[worker_id]++;\n accept(local[worker_id]);\n}",
        "for(int n=0;n<16;++n) {\nlocal[worker_id]++;\n consume([&] { accept(local[worker_id]);\n}); }",
    ] {
        let source = format!(
            "static void accept(float value) {{ consume(value); }}\nvoid run(int worker_id) {{\nfloat local[16]={{}};\n{body}\n}}"
        );
        assert!(
            !analyze_private_array(&source).findings.is_empty(),
            "{source}"
        );
    }
    let source = "void run(int worker_id) {\nfloat local[16]={};\nfor(int n=0;n<16;++n) {\nlocal[worker_id]++;\n accept(local[worker_id]);\n}\n}\nstatic void accept(float value) { consume(value); }";
    assert!(!analyze_private_array(source).findings.is_empty());
}

#[test]
fn c_arithmetic_is_builtin_unless_compile_commands_select_cpp() {
    for (extension, commands, expected) in [
        ("c", vec![], false),
        ("C", vec![], true),
        ("c", vec![vec!["gcc-13"]], false),
        ("c", vec![vec!["clang-18"]], false),
        ("c", vec![vec!["gcc-wrapper"]], true),
        ("c", vec![vec!["clang", "@flags"]], true),
        ("c", vec![vec!["clang", "-xc++", "SOURCE", "-xc"]], true),
        ("c", vec![vec!["clang", "-xc", "SOURCE", "-xc++"]], false),
        ("cpp", vec![], true),
        ("c", vec![vec!["clang", "-x", "c++"]], true),
        ("cpp", vec![vec!["clang++", "-x", "c"]], false),
        ("c", vec![vec!["clang++"]], true),
        (
            "c",
            vec![vec!["clang", "-xc"], vec!["clang", "-xc++"]],
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        let path = root.path().join(format!("candidate.{extension}"));
        fs::write(&path,"void run(int worker_id, Number value) {\nint local[16]={};\nfor(int i=0;i<16;++i) {\nlocal[worker_id]++;\nconsume(local[worker_id]+value);\n}\n}").unwrap();
        if !commands.is_empty() {
            let entries = commands
                .iter()
                .map(|command| {
                    let mut arguments = command
                        .iter()
                        .map(|s| {
                            if *s == "SOURCE" {
                                path.display().to_string()
                            } else {
                                s.to_string()
                            }
                        })
                        .collect::<Vec<_>>();
                    if !command.contains(&"SOURCE") {
                        arguments.push(path.display().to_string());
                    }
                    serde_json::json!({"directory":root.path(),"file":path,"arguments":arguments})
                })
                .collect::<Vec<_>>();
            fs::write(
                root.path().join("compile_commands.json"),
                serde_json::to_string(&entries).unwrap(),
            )
            .unwrap();
        }
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cpp_include_speculative = true;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{extension} {commands:?}: {report:#?}"
        );
    }
}

#[test]
fn macro_substitution_can_change_scalar_expression_value_category() {
    let source = "#define KEEP(x) remember(&x)\nvoid run(int worker_id) {\nint local[16]={};\nfor(int i=0;i<16;++i) {\nlocal[worker_id]++;\nKEEP(local[worker_id]+1);\n}\n}";
    assert!(!analyze_private_array(source).findings.is_empty());
}

#[test]
fn imported_cpp_overloads_preclude_local_scalar_parameter_proof() {
    let source = "#include \"extra_overloads.hpp\"\nstatic void accept(double value) { consume(value); }\nvoid run(int worker_id) {\nfloat local[16]={};\nfor(int i=0;i<16;++i) {\nlocal[worker_id]++;\naccept(local[worker_id]);\n}\n}";
    // The header may declare accept(float&), which wins over double conversion.
    assert!(!analyze_private_array(source).findings.is_empty());
}

#[test]
fn pointer_partition_witness_names_storage_not_stride() {
    let report = analyze(
        "float storage[1024];\nvoid update(int stride) {\nint worker = omp_get_thread_num();\nfloat *part = storage + worker * stride;\nfor(int i=0;i<stride;++i) {\npart[i] += 1;\n}\n}",
        &[CandidateKind::IndexedWrites],
    );
    assert!(!report.findings.is_empty(), "{report:#?}");
    let accesses = report
        .findings
        .iter()
        .flat_map(|f| &f.access_evidence)
        .collect::<Vec<_>>();
    assert!(
        accesses
            .iter()
            .any(|a| a.field_name.as_deref() == Some("storage")),
        "{report:#?}"
    );
    assert!(
        accesses
            .iter()
            .all(|a| a.field_name.as_deref() != Some("stride")),
        "{report:#?}"
    );
    assert!(
        report
            .findings
            .iter()
            .all(|f| !f.field_list.iter().any(|field| field == "stride")),
        "{report:#?}"
    );
}

#[test]
fn c_pointer_slice_and_backing_share_a_storage_identity() {
    let root = tempdir().unwrap();
    let path = root.path().join("candidate.c");
    let source = "float storage[1024];\nvoid update(int stride) {\nint worker = omp_get_thread_num();\nfloat *part = storage + worker * stride;\n#pragma omp parallel for\nfor(int i=0;i<stride;++i) {\npart[i] += 1;\n}\n}";
    fs::write(&path, source).unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert_eq!(report.findings.len(), 1, "{report:#?}");
    assert!(
        report.findings[0]
            .field_list
            .iter()
            .any(|field| field == "storage")
    );
    assert!(
        report.findings[0]
            .access_evidence
            .iter()
            .all(|access| access.field_name.as_deref() == Some("storage")),
        "{report:#?}"
    );

    fs::write(
        &path,
        source.replace("worker * stride", "omp_get_thread_num() * stride"),
    )
    .unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert_eq!(report.findings.len(), 1, "{report:#?}");
    assert!(
        report.findings[0]
            .access_evidence
            .iter()
            .all(|access| access.field_name.as_deref() == Some("storage")),
        "{report:#?}"
    );

    // An intervening assignment kills the old binding, even in an inner block.
    fs::write(
        &path,
        source.replace(
            "#pragma omp parallel for",
            "if (stride > 8) { part = obtain(); }\n#pragma omp parallel for",
        ),
    )
    .unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(
        report
            .findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .any(|access| access.field_name.as_deref() == Some("part")),
        "{report:#?}"
    );

    // In C++ a user-defined operand may redirect an overloaded addition.
    fs::remove_file(&path).unwrap();
    fs::write(root.path().join("candidate.cpp"), source).unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(
        report
            .findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .any(|access| access.field_name.as_deref() == Some("part")),
        "{report:#?}"
    );
}

#[test]
fn fresh_primitive_buffers_need_a_handoff_before_cross_thread_index_risk() {
    for (body, expected) in [
        (
            "#pragma omp parallel\n{\nfloat *scratch = (float*)malloc(128);\nfor(int i=0;i<16;++i) {\nscratch[i]++;\n}\nfree(scratch);\n}",
            false,
        ),
        (
            "float *scratch = (float*)malloc(128);\n#pragma omp parallel for\nfor(int i=0;i<16;++i) {\nscratch[i]++;\n}",
            true,
        ),
        (
            "#pragma omp parallel\n{\nfloat *scratch = (float*)malloc(128);\npublish(scratch);\nfor(int i=0;i<16;++i) {\nscratch[i]++;\n}\n}",
            true,
        ),
        (
            "#pragma omp parallel\n{\nfloat *scratch = (float*)malloc(128);\nfor(int i=0;i<16;++i) {\nscratch[i]++;\npublish(scratch);\n}\n}",
            true,
        ),
        (
            "#pragma omp parallel\n{\nfloat *scratch = (float*)malloc(128);\nfor(int i=0;i<16;++i) {\nscratch[i] += custom;\n}\n}",
            true,
        ),
    ] {
        let report = analyze_speculative(
            &format!("void run() {{\n{body}\n}}"),
            &[CandidateKind::IndexedWrites],
        );
        assert_eq!(!report.findings.is_empty(), expected, "{body}: {report:#?}");
    }
}

#[test]
fn fresh_buffer_operator_and_conversion_can_publish_an_element_reference() {
    for expression in ["scratch[i] + custom;", "(Wrapper)scratch[i];"] {
        let source = format!(
            "void run() {{\n#pragma omp parallel\n{{\nfloat *scratch = (float*)malloc(128);\nfor(int i=0;i<16;++i) {{\nscratch[i]++;\n{expression}\n}}\n}}\n}}"
        );
        assert!(
            !analyze_speculative(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{source}"
        );
    }
}

#[test]
fn fresh_buffer_alias_family_shares_every_publication_boundary() {
    for (handoff, expected) in [
        ("", false),
        ("publish(scratch);", true),
        ("publish(work);", true),
        ("publish(part);", true),
        ("work = global_buffer;", true),
    ] {
        let source = format!(
            "void run() {{\n#pragma omp parallel\n{{\nfloat *scratch = (float*)malloc(128);\nfloat *work = scratch;\nfloat *part = work + 2;\n{handoff}\nfor(int i=0;i<16;++i) {{\npart[i]++;\n}}\n}}\n}}"
        );
        assert_eq!(
            !analyze_speculative(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            expected,
            "{source}"
        );
    }
    let source = "void run() {\nfloat *scratch = (float*)malloc(128);\n#pragma omp parallel\n{\nfloat *work = scratch;\nfor(int i=0;i<16;++i) {\nwork[i]++;\n}\n}\n}";
    assert!(
        !analyze_speculative(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
}

#[test]
fn fresh_buffer_aliases_require_native_pointer_arithmetic() {
    for (value, expected) in [
        ("(float *)((char *)scratch + 2 * sizeof(float))", false),
        ("(float (*))scratch", false),
        ("(float ** )scratch", true),
        ("(float (*)[4])scratch", true),
        ("(Widget *)scratch", true),
        ("(float (*))((char (*))scratch + 2 * sizeof(float))", false),
        ("scratch + custom", true),
        ("(float *)(uintptr_t(scratch) + 16)", true),
    ] {
        let source = format!(
            "void run() {{\n#pragma omp parallel\n{{\nfloat *scratch = (float*)malloc(128);\nfloat *work = {value};\nfor(int i=0;i<16;++i) {{\nwork[i]++;\n}}\n}}\n}}"
        );
        assert_eq!(
            !analyze_speculative(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn fresh_alignment_rounding_requires_proven_allocation_padding() {
    for (allocation, expression, expected) in [
        (
            "malloc(256 + 63)",
            "(float *)(((uintptr_t)raw + (uintptr_t)63) / 64 * 64)",
            false,
        ),
        (
            "calloc(256 + 63, 1)",
            "(float *)(((uintptr_t)raw + (uintptr_t)63) & ~((uintptr_t)63))",
            false,
        ),
        (
            "malloc(32)",
            "(float *)(((uintptr_t)raw + (uintptr_t)63) / 64 * 64)",
            true,
        ),
        (
            "malloc(256 + 63)",
            "(float *)(((uintptr_t)raw + alignment - 1) / alignment * alignment)",
            true,
        ),
        (
            "malloc(63)",
            "(float *)(((uintptr_t)raw + (uintptr_t)63) / 64 * 64)",
            true,
        ),
        (
            "malloc(18446744073709551615ULL + 63)",
            "(float *)(((uintptr_t)raw + (uintptr_t)63) / 64 * 64)",
            true,
        ),
        (
            "malloc(256 + 63)",
            "(float *)(((uint32_t)(uintptr_t)raw + (uint32_t)63) / 64 * 64)",
            true,
        ),
    ] {
        let source = format!(
            "#include <stdint.h>\n#include <stdlib.h>\nvoid run(int worker_id, uintptr_t alignment) {{\n#pragma omp parallel\n{{\nfloat *raw = (float *){allocation};\nfloat *data = {expression};\ndata[worker_id]++;\n}}\n}}"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{allocation} {expression}: {report:#?}"
        );
    }
}

#[test]
fn fresh_alignment_proof_is_independent_of_configured_cache_line() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("candidate.cpp"),
        "#include <stdint.h>\n#include <stdlib.h>\nvoid run(int worker_id) {\n#pragma omp parallel\n{\nfloat *raw = (float *)malloc(256 + 63);\nfloat *data = (float *)(((uintptr_t)raw + (uintptr_t)63) & ~((uintptr_t)63));\ndata[worker_id]++;\n}\n}\n",
    )
    .unwrap();
    for cache_line_size in [32, 64, 128] {
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cache_line_size = cache_line_size;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert!(
            report.findings.is_empty(),
            "cache_line_size={cache_line_size}: {report:#?}"
        );
    }
}

#[test]
fn fresh_workspace_bounded_aliases_keep_primitive_ranges_local() {
    for (alias, use_site, expected) in [
        (
            "float (*matrix)[4] = (float (*)[4])data;",
            "float observed = matrix[0][worker_id];",
            false,
        ),
        (
            "typedef struct { float x; float y; } Pair;\nPair *records = (Pair *)data;",
            "float observed = records[worker_id].x;",
            false,
        ),
        (
            "float (*matrix)[4] = (float (*)[4])data;\npublish(matrix);",
            "float observed = matrix[0][worker_id];",
            true,
        ),
        (
            "typedef struct { float *p; float y; } Pair;\nPair *records = (Pair *)data;",
            "records[worker_id].y++;",
            true,
        ),
    ] {
        let source = format!(
            "#include <stdlib.h>\nvoid publish(void *);\nvoid run(int worker_id) {{\n#pragma omp parallel\n{{\nfloat *data = (float *)malloc(256);\n{alias}\n{use_site}\nfloat *tail = data;\ntail[worker_id]++;\n}}\n}}"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{alias} {use_site}: {report:#?}"
        );
    }
}

#[test]
fn fresh_workspace_element_effects_require_visible_safe_helpers() {
    let safe = r#"
        #include <xmmintrin.h>
        #include <stdlib.h>
        #define LOAD_ELEMENT(x) _mm_loadu_ps(&(x))
        #define STORE_ELEMENT(x, value) _mm_storeu_ps(&(x), (value))
        static inline float load_element(float &value) {
            return _mm_cvtss_f32(_mm_load_ss(&value));
        }
        void run(int worker_id) {
        #pragma omp parallel
        {
            float *data = (float *)malloc(256);
            float observed = load_element(data[worker_id]);
            STORE_ELEMENT(data[worker_id], observed);
            data[worker_id] += observed;
        }
        }
    "#;
    assert!(
        analyze(safe, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty(),
        "{safe}"
    );

    let safe_bounded = r#"
        #include <xmmintrin.h>
        #include <stdlib.h>
        #define LOAD_ELEMENT(x) _mm_loadu_ps(&(x))
        #define STORE_ELEMENT(x, value) _mm_storeu_ps(&(x), (value))
        void run(int worker_id) {
        #pragma omp parallel
        {
            float *data = (float *)malloc(256);
            float (*matrix)[4] = (float (*)[4])data;
            float observed = 0.0f;
            LOAD_ELEMENT(matrix[0][worker_id]);
            STORE_ELEMENT(matrix[0][worker_id], observed);
            matrix[0][worker_id] += observed;
        }
        }
    "#;
    assert!(
        analyze(safe_bounded, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty(),
        "{safe_bounded}"
    );

    for source in [
        r#"
            #include <xmmintrin.h>
            #include <stdlib.h>
            #define PUBLISH_ELEMENT(x) retain(&(x))
            void run(int worker_id) {
            #pragma omp parallel
            {
                float *data = (float *)malloc(256);
                PUBLISH_ELEMENT(data[worker_id]);
                data[worker_id]++;
            }
            }
        "#,
        r#"
            #include <stdlib.h>
            #define LOAD_ELEMENT(x) _mm_loadu_ps(&(x))
            void run(int worker_id) {
            #pragma omp parallel
            {
                float *data = (float *)malloc(256);
                LOAD_ELEMENT(data[worker_id]);
                data[worker_id]++;
            }
            }
        "#,
        r#"
            #include <cmath>
            #include <stdlib.h>
            #define fabsf(x) retain(&(x))
            void run(int worker_id) {
            #pragma omp parallel
            {
                float *data = (float *)malloc(256);
                float observed = fabsf(data[worker_id]);
                data[worker_id] += observed;
            }
            }
        "#,
    ] {
        assert!(
            !analyze(source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{source}"
        );
    }
}

#[test]
fn bpf_partition_layout_requires_numeric_stride_and_aligned_backing() {
    for (width, block, flags, middle, expected) in [
        (8, 32, "BPF_F_MMAPABLE", "", false),
        (8, 64, "BPF_F_MMAPABLE", "", false),
        (8, 128, "BPF_F_MMAPABLE", "", true),
        (1, 64, "BPF_F_MMAPABLE", "", true),
        (
            1,
            64,
            "BPF_F_MMAPABLE",
            "idx = COUNTER_WIDTH * bpf_get_smp_processor_id();",
            true,
        ),
        // A native map helper with a single block-spaced scalar slot is
        // isolated for every legal eight-byte base phase, including non-mmap maps.
        (8, 64, "0", "", false),
        (
            8,
            64,
            "BPF_F_MMAPABLE",
            "if (flag) idx = bpf_get_smp_processor_id();",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("sample.bpf.c"),
            format!(
                r#"
#define COUNTER_WIDTH {width}
struct {{
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __uint(map_flags, {flags});
 __type(key, u32);
 __type(value, u64);
}} counters SEC(".maps");
int sample() {{
 u32 offset = COUNTER_WIDTH * bpf_get_smp_processor_id();
 u32 idx = offset;
 {middle}
 bpf_map_update_elem(&counters, &idx, &value, 0);
 return 0;
}}
"#
            ),
        )
        .unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cache_line_size = block;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|name| name == "counters")),
            expected,
            "width={width} block={block} flags={flags} middle={middle}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn bpf_guarded_offset_proof_is_limited_to_the_true_branch() {
    for (bound, block, expected) in [(4, 64, false), (16, 64, true), (4, 128, true)] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("sample.bpf.c"),
            format!(
                r#"
struct {{
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __uint(map_flags, BPF_F_MMAPABLE);
 __type(value, u64);
}} counters SEC(".maps");
int sample() {{
 u32 op = operation();
 u32 idx;
 if (op < {bound}) {{
  idx = 8 * bpf_get_smp_processor_id() + op;
  bpf_map_update_elem(&counters, &idx, &value, 0);
 }}
}}
"#
            ),
        )
        .unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cache_line_size = block;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|n| n == "counters")),
            expected,
            "bound={bound} block={block}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn fresh_heap_scalar_copies_do_not_publish_the_original_slot() {
    for (copy, expected) in [
        ("float value = scratch[i];", false),
        ("float value; value = scratch[i];", false),
        ("float value = scratch[i] + 1.0f;", false),
        ("float &value = scratch[i]; publish(&value);", true),
        ("Wrapper value = scratch[i];", true),
        ("Wrapper value; value = scratch[i];", true),
        ("float value = scratch[i] + custom;", true),
        ("float value = scratch[i]; publish(scratch);", true),
    ] {
        let source = format!(
            "void run() {{\n#pragma omp parallel\n{{\nfloat *scratch = (float*)malloc(128);\nfor(int i=0;i<16;++i) {{\n{copy}\nscratch[i]++;\n}}\n}}\n}}"
        );
        assert_eq!(
            !analyze_speculative(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn fresh_allocation_proof_stops_at_syntax_recovery_and_loop_backedges() {
    for (before, inside, after, expected) in [
        ("", "", "broken @ tokens;", false),
        ("broken @ tokens;", "", "", true),
        ("", "broken @ tokens;", "", true),
    ] {
        let source = format!(
            "void run() {{\n#pragma omp parallel\n{{\nfloat *scratch = (float*)malloc(128);\n{before}\nfor(int i=0;i<16;++i) {{\nscratch[i]++;\n{inside}\n}}\n{after}\n}}\n}}"
        );
        let report = analyze_speculative(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{source}: {report:#?}"
        );
    }
}

#[test]
fn ordinary_index_spelling_does_not_establish_worker_partition() {
    for name in [
        "idx",
        "dim_index",
        "column_idx",
        "entry_index",
        "slot_index",
    ] {
        let source = format!("void update(int {name}, int *values) {{\nvalues[{name}]++;\n}}");
        assert!(
            analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{name}"
        );
        let parallel = format!(
            "void update(int *values) {{\n#pragma omp parallel for\nfor(int {name}=0;{name}<16;++{name}) {{\nvalues[{name}]++;\n}}\n}}"
        );
        assert!(
            !analyze(&parallel, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{parallel}"
        );
    }
    for name in ["worker_id", "thread_index", "cpu_id"] {
        let source = format!("void update(int {name}, int *values) {{\nvalues[{name}]++;\n}}");
        assert!(
            !analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{name}"
        );
    }
    let callback = "void update(int worker_id, int *values) {\nauto apply = [](int dim_index, int *data) {\ndata[dim_index]++;\n};\napply(worker_id, values);\n}";
    assert!(
        !analyze(callback, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
}

#[test]
fn cross_function_partition_follows_parallel_induction_arithmetic() {
    let source = "int values[256];\nvoid record(int position) {\nvalues[position]++;\n}\nvoid run() {\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {\nint offset = row*16;\nrecord(offset);\n}\n}";
    assert!(
        !analyze(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    for variant in [
        source.replace("#pragma omp parallel for", ""),
        source.replace("row*16", "0"),
        source.replace("row*16", "row*0"),
        source.replace("int offset", "row = 0; int offset"),
    ] {
        assert!(
            analyze(&variant, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{variant}"
        );
    }
}

#[test]
fn parallel_induction_member_summary_requires_a_shared_bound_receiver() {
    for (outside, inside, expected) in [
        ("Storage object;", "", true),
        ("int count = 64; Storage object(count);", "", true),
        (
            "int count = 64; Storage object(count, capacity());",
            "",
            true,
        ),
        ("int count = 64; Storage object{count};", "", true),
        ("", "int count = 64; Storage object(count);", false),
        ("Storage object(int);", "", false),
        ("using count = int; Storage object(count);", "", false),
        ("Storage object(count);", "", false),
        (
            "int count = 64; { using count = int; Storage object(count); }",
            "",
            false,
        ),
        ("", "Storage object;", false),
        ("Storage *object;", "", false),
        ("Storage object;", "Storage object(int);", false),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("store.h"), "struct Storage {\nint values[64];\nvoid write(int position) {\nvalues[position]++;\n}\n};\n").unwrap();
        fs::write(root.path().join("main.cpp"), format!("#include \"store.h\"\nvoid run() {{\n{outside}\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {{\n{inside}\nobject.write(row);\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{outside} {inside}: {report:#?}"
        );
    }
}

#[test]
fn parallel_induction_does_not_borrow_a_shared_receiver_through_private_clauses() {
    for (clause, expected) in [
        ("shared(object)", true),
        ("firstprivate(object)", false),
        ("private(object)", false),
        ("lastprivate(object)", false),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("storage.h"), "struct Storage {\nint values[64];\nvoid write(int position) {\nvalues[position]++;\n}\n};\n").unwrap();
        fs::write(root.path().join("main.cpp"), format!("#include \"storage.h\"\nvoid run() {{\nint count = 64;\nStorage object(count);\n#pragma omp parallel for {clause}\nfor(int row=0;row<16;++row) {{\nobject.write(row);\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{clause}: {report:#?}"
        );
    }
}

#[test]
fn automatic_array_ownership_recovers_visible_alignment_macros() {
    for (definition, expected) in [
        ("#define DECORATE __attribute__((aligned(32)))", false),
        ("#define DECORATE static", true),
        ("#define DECORATE extern", true),
        ("", true),
        (
            "#define DECORATE __attribute__((aligned(32)))\n#undef DECORATE\n#define DECORATE static",
            true,
        ),
    ] {
        let source = format!(
            "{definition}\nfloat scratch[32];\nvoid run(int worker_id) {{\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {{\nfloat DECORATE scratch[32];\nscratch[worker_id] = row;\n}}\n}}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{definition}: {report:#?}"
        );
    }
}

#[test]
fn alignment_macro_ownership_requires_visible_include_and_preserves_handoff() {
    for guarded in [false, true] {
        for (header, include, handoff, expected) in [
            (
                "#define DECORATE __attribute__((aligned(32)))",
                "#include \"annotation.h\"",
                "",
                false,
            ),
            (
                "#define DECORATE __attribute__((aligned(32)))",
                "",
                "",
                true,
            ),
            (
                "#define DECORATE __attribute__((aligned(32)))",
                "#include \"annotation.h\"",
                "publish(scratch);",
                true,
            ),
            (
                "#if CONFIG\n#define DECORATE __attribute__((aligned(32)))\n#else\n#define DECORATE static\n#endif",
                "#include \"annotation.h\"",
                "",
                true,
            ),
        ] {
            let root = tempdir().unwrap();
            fs::write(
                root.path().join("annotation.h"),
                if guarded {
                    format!("#ifndef ANNOTATION_H\n#define ANNOTATION_H\n{header}\n#endif\n")
                } else {
                    header.to_owned()
                },
            )
            .unwrap();
            fs::write(root.path().join("main.cpp"), format!("{include}\nfloat scratch[32];\nvoid run(int worker_id) {{\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {{\nfloat DECORATE scratch[32];\n{handoff}\nscratch[worker_id] = row;\n}}\n}}\n")).unwrap();
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
            );
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "{header} {include} {handoff}: {report:#?}"
            );
        }
    }
}

#[test]
fn c_scalar_prototypes_preserve_automatic_storage_ownership() {
    for storage in [
        "float scratch[32];",
        "float *scratch = (float *)malloc(32 * sizeof(float));",
    ] {
        for (extension, declarations, call, expected) in [
            (
                "c",
                "void consume(float);",
                "consume(scratch[worker_id]);",
                false,
            ),
            (
                "c",
                "void consume(float);\nvoid consume(float value) {}",
                "consume(scratch[worker_id]);",
                false,
            ),
            (
                "c",
                "void consume(float, ...);",
                "consume(scratch[worker_id]);",
                true,
            ),
            (
                "c",
                "void consume(float *);",
                "consume(&scratch[worker_id]);",
                true,
            ),
            (
                "c",
                "#define consume(x) publish(&(x))",
                "consume(scratch[worker_id]);",
                true,
            ),
            (
                "cpp",
                "void consume(float);",
                "consume(scratch[worker_id]);",
                true,
            ),
            (
                "c",
                "float consume(float);\nfloat outer(float);",
                "outer(consume(scratch[worker_id]));",
                false,
            ),
            (
                "c",
                "float consume(float);\nvoid publish(float *);\n#define WRAP(x) (publish(&scratch[worker_id]), (x))",
                "WRAP(consume(scratch[worker_id]));",
                true,
            ),
        ] {
            let root = tempdir().unwrap();
            fs::write(root.path().join(format!("main.{extension}")), format!("{declarations}\nvoid run(int worker_id) {{\n#pragma omp parallel\n{{\n{storage}\n{call}\nscratch[worker_id] = worker_id;\n}}\n}}\n")).unwrap();
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
            );
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "{extension} {declarations}: {report:#?}"
            );
        }
    }
}

#[test]
fn pointer_parameter_names_do_not_seed_partition_identity() {
    for (parameter, access) in [
        ("Block *block", "block->values[i] = i;"),
        ("Block &block", "block.values[i] = i;"),
        ("int block[32]", "block[i] = i;"),
    ] {
        let source = format!(
            "struct Block {{ int size; int values[32]; }};\nvoid update({parameter}) {{\nfor(int i=0;i<32;++i) {{\n{access}\n}}\n}}\n"
        );
        assert!(
            analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{source}"
        );
        let parallel = source.replace("for(int i", "#pragma omp parallel for\nfor(int i");
        assert!(
            !analyze(&parallel, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{parallel}"
        );
    }
    let source = "struct Block { int size; int values[32]; };\nvoid shift(Block *block) {\nfor(int i=block->size-1;i>0;--i) {\nblock->values[i] = block->values[i-1];\n}\n}";
    assert!(
        analyze(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    let descriptor = "struct Context { int worker_id; };\nvoid update(Context *block, int *values) {\nvalues[block->worker_id]++;\n}";
    assert!(
        !analyze(descriptor, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    let scalar = "void update(const int &worker_id, int *values) {\nvalues[worker_id]++;\n}";
    assert!(
        !analyze(scalar, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    let immutable_pointer = "struct Block { int size; };\nstruct Context { const Block *const block; };\nvoid update(Context *context, int *values) {\nfor(int i=context->block->size-1;i>0;--i) {\nvalues[i]++;\n}\n}";
    assert!(
        analyze(immutable_pointer, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
}

#[test]
fn quantity_parameter_names_do_not_seed_partition_identity() {
    for name in [
        "block_size",
        "worker_count",
        "thread_stride",
        "partition_length",
        "cell_capacity",
        "slot_bytes",
        "block_size_per_chunk",
        "worker_count_total",
        "thread_stride_in_bytes",
        "num_threads",
        "num_threads_total",
    ] {
        let source = format!(
            "void update(int {name}, int *values) {{\nfor(int i=0;i<16;++i) {{\nvalues[i * {name}]++;\n}}\n}}"
        );
        assert!(
            analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{source}"
        );
        let parallel = source.replace("for(int i", "#pragma omp parallel for\nfor(int i");
        assert!(
            !analyze(&parallel, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{parallel}"
        );
    }
    let callback = "void update(int worker_id, int *values) {\nauto apply = [](int block_size, int *data) {\ndata[block_size]++;\n};\napply(worker_id, values);\n}";
    assert!(
        !analyze(callback, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
}

#[test]
fn sycl_item_identity_requires_bound_type_and_scalar_id_overload() {
    for (ty, call, expected) in [
        ("const sycl::nd_item<3>&", "item.get_local_id(2)", true),
        ("sycl::nd_item<3>", "item.get_global_linear_id()", true),
        ("CustomItem&", "item.get_local_id(2)", false),
        ("const sycl::nd_item<3>&", "item.get_local_range(2)", false),
        ("const sycl::nd_item<3>&", "item.get_local_id()", false),
        ("const sycl::nd_item<3>&", "item.get_local_id(3)", false),
        ("const sycl::nd_item<3>&", "item.get_local_id(2) * 0", false),
    ] {
        let source = format!(
            "void norm({ty} item, float *out, int block_size) {{\nint tid = {call};\nfor(int col=tid;col<64;col+=block_size) {{\nout[col]++;\n}}\n}}"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{source}: {report:#?}"
        );
        if expected {
            assert!(
                report
                    .findings
                    .iter()
                    .flat_map(|finding| &finding.access_evidence)
                    .any(|access| access.in_concurrent_context)
            );
        }
    }
}

#[test]
fn native_compound_step_preserves_identity_but_overwrite_and_cancellation_do_not() {
    for (update, expected) in [
        ("index += stride", true),
        ("index -= stride", true),
        ("index = stride", false),
        ("index -= index", false),
    ] {
        let source = format!(
            "void update(int worker_id, int stride, int *values) {{\nint index = worker_id;\n{update};\nvalues[index]++;\n}}"
        );
        assert_eq!(
            !analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn array_size_query_does_not_publish_automatic_storage() {
    for (prefix, query, expected) in [
        ("", "sizeof(scratch)", false),
        ("", "sizeof((scratch))", false),
        ("", "sizeof scratch", false),
        ("", "publish(scratch)", true),
        ("#define sizeof(x) publish(x)", "sizeof(scratch)", true),
    ] {
        let source = format!(
            "{prefix}\nfloat scratch[32];\nvoid run(int worker_id) {{\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {{\nfloat scratch[32];\nunsigned long bytes = {query};\nscratch[worker_id] = row;\n}}\n}}"
        );
        for extension in ["c", "cpp"] {
            let root = tempdir().unwrap();
            fs::write(root.path().join(format!("candidate.{extension}")), &source).unwrap();
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
            );
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "{extension}: {source}"
            );
        }
    }
}

#[test]
fn discarded_memory_operation_keeps_local_array_ownership() {
    for (prefix, operation, expected) in [
        ("", "memset(scratch, 0, sizeof(scratch));", false),
        ("", "memset((scratch), 0, sizeof(scratch));", false),
        ("", "memset((void *)scratch, 0, sizeof(scratch));", false),
        ("", "memset((void (*))scratch, 0, sizeof(scratch));", false),
        ("", "memset(scratch + 1, 0, 4);", false),
        ("", "memset(&scratch[1], 0, 4);", false),
        ("", "memset(transform(scratch), 0, 4);", true),
        (
            "struct Offset {}; Offset offset; float* operator+(float*, Offset);",
            "memset(scratch + offset, 0, 4);",
            true,
        ),
        ("", "memset((void *)(uintptr_t)scratch, 0, 4);", true),
        ("", "memcpy(scratch, input, sizeof(scratch));", false),
        ("", "memmove(input, scratch, sizeof(scratch));", false),
        ("", "published = memset(scratch, 0, sizeof(scratch));", true),
        ("", "publish(memset(scratch, 0, sizeof(scratch)));", true),
        (
            "#define memset(a,b,c) publish(a)",
            "memset(scratch, 0, sizeof(scratch));",
            true,
        ),
        (
            "void memset(float*, int, unsigned long);",
            "memset(scratch, 0, sizeof(scratch));",
            true,
        ),
        (
            "void memset(float* a, int b, unsigned long c) {publish(a);}",
            "memset(scratch, 0, sizeof(scratch));",
            true,
        ),
    ] {
        let source = format!(
            "{prefix}\nfloat scratch[32];\nvoid run(int worker_id, float *input) {{\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {{\nfloat scratch[32];\n{operation}\nscratch[worker_id] = row;\n}}\n}}"
        );
        assert_eq!(
            !analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn memory_operation_ownership_checks_other_translation_units() {
    for (other, expected) in [
        ("void unrelated();", false),
        (
            "void memset(float *p, int v, unsigned long n) { publish(p); }",
            true,
        ),
        (
            "namespace custom { void memcpy(float*, float*, unsigned long); }",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        let operation = if other.contains("memcpy") {
            "memcpy(scratch,input,128)"
        } else {
            "memset(scratch,0,128)"
        };
        fs::write(root.path().join("candidate.cpp"), format!("float scratch[32];\nvoid run(int worker_id, float *input) {{\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {{\nfloat scratch[32];\n{operation};\nscratch[worker_id] = row;\n}}\n}}" )).unwrap();
        fs::write(root.path().join("other.cpp"), other).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(!report.findings.is_empty(), expected, "{other}");
    }
}

#[test]
fn array_size_macros_require_unevaluated_parameter_uses() {
    for (definition, use_site, expected) in [
        (
            "#define COUNT(x) (sizeof(x)/sizeof((x)[0]))",
            "COUNT(scratch)",
            false,
        ),
        ("#define COUNT(x) sizeof(x)", "COUNT(scratch) - 1", false),
        ("#define COUNT(x) publish(x)", "COUNT(scratch)", true),
        ("#define COUNT(x) (x)", "COUNT(scratch)", true),
        (
            "#define COUNT(x) (sizeof(x), publish(x))",
            "COUNT(scratch)",
            true,
        ),
        (
            "#define COUNT(x) sizeof(publish(x))",
            "COUNT(scratch)",
            true,
        ),
        (
            "#define COUNT(x) sizeof(x)\n#define sizeof(x) publish(x)",
            "COUNT(scratch)",
            true,
        ),
        (
            "#define COUNT(x) sizeof(x)\n#undef COUNT",
            "COUNT(scratch)",
            true,
        ),
        (
            "#define COUNT(x) sizeof(x)\n#define OUT(x) other_##x",
            "OUT(COUNT(scratch))",
            true,
        ),
    ] {
        let source = format!(
            "{definition}\nfloat scratch[32];\nvoid run(int worker_id) {{\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {{\nfloat scratch[32];\nauto size = {use_site};\nscratch[worker_id] = row;\n}}\n}}"
        );
        assert_eq!(
            !analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn bpf_remote_partition_updates_are_not_cpu_private() {
    for block in [32, 64, 128] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("sample.bpf.c"),
            r#"
#define WIDTH 16
struct {
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __uint(map_flags, BPF_F_MMAPABLE);
 __type(key, u32);
 __type(value, u64);
} counters SEC(".maps");
SEC("tp_btf/sched_switch")
int sample() {
 u32 cpu = bpf_get_smp_processor_id();
 u32 remote_cpu = cpu + 1;
 u32 local_idx = cpu * WIDTH + 1;
 u32 remote_idx = remote_cpu * WIDTH;
 bpf_map_update_elem(&counters, &local_idx, &value, 0);
 bpf_map_update_elem(&counters, &remote_idx, &value, 0);
 return 0;
}
"#,
        )
        .unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cache_line_size = block;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|name| name == "counters")),
            "{block}: {report:#?}"
        );
    }
}

#[test]
fn bpf_declared_c_calls_preserve_only_unescaped_local_offsets() {
    for (declaration, call, expected) in [
        ("void observe(unsigned long value);", "observe(7);", false),
        (
            "static void observe(unsigned long value) {}",
            "observe(7);",
            false,
        ),
        ("", "observe(7);", true),
        (
            "void observe(unsigned long value);\n#define observe(x) offset = 0",
            "observe(7);",
            true,
        ),
        ("void observe(void *value);", "observe(&offset);", true),
        (
            "void observe(unsigned long value);",
            "outer(observe(7));",
            true,
        ),
        (
            "void observe(unsigned long value);",
            "observe(offset++);",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("sample.bpf.c"),
            format!(
                r#"
{declaration}
#define WIDTH 16
struct {{
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __uint(map_flags, BPF_F_MMAPABLE);
 __type(key, u32);
 __type(value, u64);
}} counters SEC(".maps");
int sample() {{
 u32 offset = WIDTH * bpf_get_smp_processor_id();
 {call}
 u32 idx = offset + 1;
 bpf_map_update_elem(&counters, &idx, &value, 0);
 return 0;
}}
"#
            ),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|name| name == "counters")),
            expected,
            "{declaration} {call}: {report:#?}"
        );
    }
}

#[test]
fn loop_local_pixel_pointer_does_not_make_shared_pixels_private() {
    for block in [32, 64, 128] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("sample.c"),
            r#"
void process(float *image, int count) {
#pragma omp parallel for
for(int row=0;row<count;++row) {
 float *const pixel = image + 4 * row;
 pixel[0] += 1.0f;
 pixel[1] += 2.0f;
}
}
"#,
        )
        .unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cache_line_size = block;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert!(!report.findings.is_empty(), "{block}: {report:#?}");
    }
}

#[test]
fn local_c_element_helpers_do_not_publish_private_arrays() {
    for (helper, expected) in [
        ("static void adjust(float *p) { p[0] = p[1] + 1; }", false),
        ("static void adjust(float *p) { *p += 1; }", false),
        ("static void adjust(float *p) { *(p) += 1; }", false),
        ("static void adjust(float *p) { (*p)++; }", false),
        (
            "#define SQUARE(x) ((x) * (x))\nstatic void adjust(float *p) { p[0] = SQUARE(p[1]); }",
            false,
        ),
        (
            "#define MINIMUM(x,y) ((x) < (y) ? (x) : (y))\nstatic void adjust(float *p) { p[0] = MINIMUM(p[1], 0); }",
            false,
        ),
        (
            "#define IDENTITY(x) (x)\nstatic void adjust(float *p) { saved = &IDENTITY(p[0]); }",
            true,
        ),
        (
            "#define SQUARE(x) (saved = &(x), (x) * (x))\nstatic void adjust(float *p) { p[0] = SQUARE(p[1]); }",
            true,
        ),
        (
            "#define SQUARE(x) ((x) * (x))\n#undef SQUARE\nstatic void adjust(float *p) { p[0] = SQUARE(p[1]); }",
            true,
        ),
        (
            "#include <math.h>\nstatic void adjust(float *p) { p[0] = fmaxf(p[1], 0); }",
            false,
        ),
        (
            "#include <math.h>\nstatic void adjust(float *p) { p[0] = modff(p[0], &p[1]); }",
            true,
        ),
        (
            "float scale(float); static void adjust(float *p) { p[0] = scale(p[1]); }",
            false,
        ),
        (
            "float scale(float); static void adjust(float *p) { *p = scale(*p); }",
            false,
        ),
        (
            "float scale(float); static void adjust(float *p) { p[0] = scale(scale(p[1])); }",
            false,
        ),
        (
            "void scale(float *); static void adjust(float *p) { scale(&p[1]); }",
            true,
        ),
        (
            "float scale(float); static void adjust(float *p) { p[0] = scale(p[1], p[2]); }",
            true,
        ),
        ("static void adjust(float *p) { p[0] = scale(p[1]); }", true),
        ("static void adjust(float *p) { saved = &*p; }", true),
        ("static void adjust(float *p) { *(p++) = 1; }", true),
        (
            "static void adjust(float p[32]) { p[0] = p[1] + 1; }",
            false,
        ),
        ("static void adjust(float p[]) { p[0] = p[1] + 1; }", false),
        (
            "static void adjust(float p[static 32]) { p[0] = p[1] + 1; }",
            false,
        ),
        (
            "static void adjust(float p[extent()]) { p[0] = p[1] + 1; }",
            true,
        ),
        ("static void adjust(float p[4][4]) { p[0][0] = 1; }", true),
        (
            "static void adjust(float *p) { for(int i=0;i<16;++i) p[i] *= 2; }",
            false,
        ),
        ("static void adjust(float *p) { saved = p; }", true),
        ("static void adjust(float *p) { publish(p); }", true),
        ("static void adjust(float *p) { PUBLISH_HIDDEN(); }", true),
        ("static void adjust(float *p) { PUBLISH_HIDDEN; }", true),
        (
            "#define LOCAL_TYPE float value = 0; saved = p; float\nstatic void adjust(float *p) { LOCAL_TYPE unused; p[0] = 1; }",
            true,
        ),
        ("static void adjust(float *p) { saved = &p[0]; }", true),
        (
            "static void adjust(float *p) {\n#pragma omp parallel for\nfor(int i=0;i<16;++i) p[i]++;\n}",
            true,
        ),
        (
            "static void adjust(float *p) { p[0] = p[1]; }\n#define adjust(x) publish(x)",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("float *saved;\n{helper}\nfloat scratch[32];\nvoid run(int worker_id) {{\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {{\nfloat scratch[32];\nadjust(scratch);\nscratch[worker_id] = row;\n}}\n}}" )).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{helper}: {report:#?}"
        );
    }
}

#[test]
fn local_c_helper_retention_is_parameter_specific() {
    for (arguments, expected) in [
        ("input, scratch", false),
        ("scratch, input", true),
        ("scratch, scratch", true),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("float *saved;\nstatic void adjust(float *p, float *q) {{ saved = p; q[0] = 1; }}\nfloat scratch[32];\nvoid run(int worker_id, float *input) {{\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {{\nfloat scratch[32];\nadjust({arguments});\nscratch[worker_id] = row;\n}}\n}}" )).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{arguments}: {report:#?}"
        );
    }
}

#[test]
fn c_parameter_bound_evaluation_can_publish_another_parameter() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("sample.c"), "float *saved;\nstatic void adjust(float *p, float q[(saved = p, 4)]) { p[0] = 1; }\nfloat scratch[32];\nvoid run(int worker_id, float *input) {\n#pragma omp parallel for\nfor(int row=0;row<16;++row) {\nfloat scratch[32];\nadjust(scratch, input);\nscratch[worker_id] = row;\n}\n}" ).unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(!report.findings.is_empty());
}

#[test]
fn critical_array_merge_requires_complete_serialization() {
    for extension in ["c", "cpp"] {
        for (critical, after, expected) in [
            ("#pragma omp critical(merge)", "", false),
            ("#pragma omp critical", "", false),
            (
                "#ifdef _OPENMP\n#pragma omp critical(merge)\n#endif",
                "#ifdef _OPENMP\n#pragma omp barrier\n#endif\n#ifdef _OPENMP\n#pragma omp single\n#endif\n{\nint value = sums[0][0];\n}",
                false,
            ),
            (
                "#ifdef _OPENMP\n#pragma omp critical(merge)\n#endif",
                "",
                false,
            ),
            (
                "#pragma omp critical(merge)",
                "#pragma omp barrier\n#pragma omp single\n{\nint value = sums[0][0];\n}",
                false,
            ),
            (
                "#pragma omp critical(merge)",
                "#pragma omp single\n{\nint value = sums[0][0];\n}",
                true,
            ),
            ("#pragma omp critical(merge)", "sums[worker_id][0]++;", true),
            (
                "#pragma omp critical(merge)",
                "#pragma omp critical(other)\n{\nsums[worker_id][0]++;\n}",
                true,
            ),
            (
                "#pragma omp critical(merge)",
                "#pragma omp barrier\n#pragma omp single nowait\n{\nint value = sums[0][0];\n}",
                true,
            ),
            (
                "#ifdef ENABLE_LOCK\n#pragma omp critical(merge)\n#endif",
                "",
                true,
            ),
        ] {
            let root = tempdir().unwrap();
            fs::write(root.path().join(format!("sample.{extension}")), format!("void run(int worker_id) {{\nint sums[16][2] = {{}};\n#pragma omp parallel\n{{\n{critical}\n{{\nsums[worker_id][0]++;\n}}\n{after}\n}}\n}}\n")).unwrap();
            for block in [32, 64, 128] {
                let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
                options.cache_line_size = block;
                let report = analyze_cpp_path_with_options(root.path(), &options);
                assert_eq!(
                    !report.findings.is_empty(),
                    expected,
                    "{extension} {block} {critical} {after}: {report:#?}"
                );
            }
        }
    }
}

#[test]
fn critical_array_merge_cannot_publish_storage() {
    for mutation in [
        "saved = &sums[0];",
        "publish(sums);",
        "#pragma omp task\n{ sums[worker_id]++; }",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("int *saved;\nvoid publish(int *p);\nvoid run(int worker_id) {{\nint sums[16] = {{}};\n#pragma omp parallel\n{{\n#pragma omp critical(merge)\n{{\nsums[worker_id]++;\n{mutation}\n}}\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(!report.findings.is_empty(), "{mutation}: {report:#?}");
    }
}

#[test]
fn critical_merge_phase_allows_common_condition_but_not_backedges() {
    for (entry, expected) in [
        ("if (enabled)", false),
        ("for (int pass=0;pass<2;++pass)", true),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("void run(int worker_id, int enabled) {{\nint sums[16] = {{}};\n#pragma omp parallel\n{{\n{entry}\n{{\n#pragma omp critical(merge)\n{{\nsums[worker_id]++;\n}}\n#pragma omp barrier\n#pragma omp single\n{{\nint value = sums[0];\n}}\n}}\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{entry}: {report:#?}"
        );
    }
}

#[test]
fn mathematical_rank_requires_partition_provenance() {
    for (parameter, body, expected) in [
        ("int rank", "bins[rank]++;", false),
        ("int order", "bins[order]++;", false),
        ("int worker_id", "bins[worker_id]++;", true),
        ("", "int rank = omp_get_thread_num();\nbins[rank]++;", true),
        (
            "",
            "#pragma omp parallel for\nfor (int rank=0;rank<16;++rank) { bins[rank]++; }",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.cpp"), format!("int omp_get_thread_num();\nint bins[16];\nvoid update({parameter}) {{\n{body}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{parameter}: {body}: {report:#?}"
        );
    }
}

#[test]
fn mathematical_parameter_spelling_preserves_parallel_call_binding() {
    let report = analyze(
        "int bins[16];\nvoid add(int rank) { bins[rank]++; }\nvoid run() {\n#pragma omp parallel for\nfor (int task=0;task<16;++task) { add(task); }\n}\n",
        &[CandidateKind::IndexedWrites],
    );
    assert!(!report.findings.is_empty(), "{report:#?}");
}

#[test]
fn critical_directive_can_protect_an_entire_loop() {
    for (following, expected) in [
        ("", false),
        ("sums[worker_id]++;", true),
        ("int observed = sums[worker_id];", true),
        (
            "#pragma omp critical(other)\nfor (int j=0;j<16;++j) { sums[j]++; }",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("void run(int worker_id) {{\nint sums[16] = {{0}};\n#pragma omp parallel\n{{\n#pragma omp critical\nfor (int i=0;i<16;++i) {{\nsums[i] += worker_id;\n}}\n{following}\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(root.path(), &speculative_index_options());
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{following}: {report:#?}"
        );
    }
}

#[test]
fn bpf_cpu_timestamp_map_cannot_borrow_another_maps_partition_layout() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("sample.bpf.c"),
        r#"
struct {
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __uint(map_flags, BPF_F_MMAPABLE);
 __type(key, u32);
 __type(value, u64);
} grouped SEC(".maps");
struct {
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __type(key, u32);
 __type(value, u64);
} timestamps SEC(".maps");
int sample() {
 u32 cpu = bpf_get_smp_processor_id();
 u32 key = 16 * cpu;
 bpf_map_update_elem(&grouped, &key, &value, 0);
 u64 value = bpf_ktime_get_ns();
 bpf_map_update_elem(&timestamps, &cpu, &value, 0);
 return 0;
}
"#,
    )
    .unwrap();
    for block in [32, 64, 128] {
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cache_line_size = block;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|name| name == "timestamps")),
            "{block}: {report:#?}"
        );
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|name| name == "grouped")),
            "{block}: {report:#?}"
        );
    }
}

#[test]
fn loop_unroll_hints_do_not_publish_worker_scratch() {
    for (directive, expected) in [
        ("unroll", false),
        ("nounroll", false),
        ("unroll 4", false),
        ("unroll(4)", false),
        ("clang loop unroll(enable)", false),
        ("clang loop unroll(disable)", false),
        ("clang loop unroll(full)", false),
        ("clang loop unroll_count(4)", false),
        ("unroll PUBLISH(scratch)", true),
        ("unroll_count(4)", true),
        ("omp parallel for", true),
        ("omp taskloop", true),
        ("custom_parallel", true),
    ] {
        for extension in ["c", "cpp"] {
            let root = tempdir().unwrap();
            fs::write(root.path().join(format!("sample.{extension}")), format!("void run(int worker_id) {{\n#pragma omp parallel\n{{\nfloat scratch[16] = {{0}};\n#pragma {directive}\nfor (int i=0;i<16;++i) {{ scratch[worker_id] += i; }}\n}}\n}}\n")).unwrap();
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
            );
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "{extension} {directive}: {report:#?}"
            );
        }
    }
}

#[test]
fn loop_unroll_hints_do_not_hide_shared_storage_or_escape() {
    for declaration in [
        "static float scratch[16];",
        "float *scratch = input;",
        "float scratch[16]; publish(scratch);",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("void publish(float *);\nvoid run(int worker_id, float *input) {{\n#pragma omp parallel\n{{\n{declaration}\n#pragma unroll\nfor (int i=0;i<16;++i) {{ scratch[worker_id] += i; }}\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(!report.findings.is_empty(), "{declaration}: {report:#?}");
    }
}

#[test]
fn c_math_header_value_parameters_do_not_publish_arrays() {
    for call in [
        "fabsf(scratch[0])",
        "sqrt(scratch[0])",
        "powf(scratch[0], 2)",
        "fmaxl(scratch[0], 0)",
        "fmaf(scratch[0], 2, 1)",
        "fmaxf(fabsf(scratch[0]), 0)",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("#include <math.h>\nvoid run(int worker_id) {{\n#pragma omp parallel\n{{\nfloat scratch[16] = {{0}};\nfor (int i=0;i<16;++i) {{\nscratch[worker_id] += i;\nfloat value = {call};\n}}\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(report.findings.is_empty(), "{call}: {report:#?}");
    }
}

#[test]
fn c_math_contract_requires_visible_header_and_unshadowed_call() {
    for (header, call, extension) in [
        ("", "fabsf(scratch[0])", "c"),
        ("#include \"math.h\"", "fabsf(scratch[0])", "c"),
        (
            "#ifdef ENABLE_MATH\n#include <math.h>\n#endif",
            "fabsf(scratch[0])",
            "c",
        ),
        ("#include <math.h>", "fabsf(scratch[0])", "cpp"),
        (
            "#include <math.h>\n#undef fabsf\n#define fabsf(x) (publish(&(x)), 0.f)",
            "fabsf(scratch[0])",
            "c",
        ),
        ("#include <math.h>", "fmaxf(scratch[0])", "c"),
        ("#include <math.h>", "modff(scratch[0], &scratch[1])", "c"),
        ("#include <math.h>", "OPAQUE(fabsf(scratch[0]))", "c"),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join(format!("sample.{extension}")), format!("{header}\nvoid run(int worker_id) {{\n#pragma omp parallel\n{{\nfloat scratch[16] = {{0}};\nfor (int i=0;i<16;++i) {{\nscratch[worker_id] += i;\nfloat value = {call};\n}}\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(
            !report.findings.is_empty(),
            "{extension} {header} {call}: {report:#?}"
        );
    }
}

#[test]
fn fresh_c_allocation_can_remain_private_through_local_pointer_table() {
    for body in [
        "float *views[1];\nviews[0] = data;\nviews[0][worker_id]++;",
        "float *views[2];\nviews[0] = data;\nviews[1] = data + 16;\nviews[worker_id % 2][worker_id]++;",
        "float *alias = data + 16;\nfloat *views[2];\nviews[0] = data;\nviews[1] = alias;\nfor (int i=0;i<2;++i) { views[i][worker_id]++; }",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("#include <stdlib.h>\nfloat *views[2];\nvoid run(int worker_id) {{\n#pragma omp parallel\n{{\nfloat *data = (float *)malloc(256);\n{body}\ndata[worker_id]++;\n}}\n}}\n")).unwrap();
        for block in [32, 64, 128] {
            let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
            options.cache_line_size = block;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert!(report.findings.is_empty(), "{block} {body}: {report:#?}");
        }
    }
}

#[test]
fn local_pointer_table_proof_rejects_publication_and_mixed_origins() {
    for body in [
        "views[0] = data;",
        "static float *views[1];\nviews[0] = data;",
        "float *views[1], *other = (publish_table(views), data);\nviews[0] = data;\nviews[0][worker_id]++;",
        "float *views[1];\nviews[0] = data;\npublish_table(views);",
        "float *views[1];\nviews[0] = data;\npublished = views[0];",
        "float *views[1];\nviews[0] = data;\npublished = &views[0][0];",
        "float *views[1];\nviews[0] = data;\nviews[0] = shared;",
        "float *views[2];\nviews[0] = data;\nviews[1] = shared;",
        "float *views[2];\nviews[0] = data;\nviews[0][worker_id]++;",
        "float *views[1];\nif (worker_id) views[0] = data;",
        "float *views[1];\nviews[0] = data;\n#pragma omp parallel\n{ views[0][worker_id]++; }",
        "float *views[1];\nviews[0] = data;\npublish_data(data);",
        "float *views[1];\nviews[0] = data;\nOPAQUE();",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("#include <stdlib.h>\nfloat *views[2], *published;\nvoid publish_table(float **);\nvoid publish_data(float *);\nvoid run(int worker_id, float *shared) {{\n#pragma omp parallel\n{{\nfloat *data = (float *)malloc(256);\n{body}\ndata[worker_id]++;\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(!report.findings.is_empty(), "{body}: {report:#?}");
    }
}

#[test]
fn local_pointer_table_cannot_privatize_allocation_outside_parallel_region() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("sample.c"), "#include <stdlib.h>\nvoid run(int worker_id) {\nfloat *data = (float *)malloc(256);\n#pragma omp parallel\n{\nfloat *views[1];\nviews[0] = data;\nviews[0][worker_id]++;\n}\n}\n").unwrap();
    let report = analyze_cpp_path_with_options(root.path(), &speculative_index_options());
    assert!(!report.findings.is_empty(), "{report:#?}");
}

#[test]
fn c_element_helpers_accept_visible_literal_macro_bounds() {
    for (definition, bound) in [
        ("#define WIDTH 4", "WIDTH * 3"),
        ("#define WIDTH ((4))", "(WIDTH + 2) * 2"),
        ("", "4 * 3"),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("{definition}\nstatic void fill(float p[{bound}]) {{\nfor (int i=0;i<{bound};++i) p[i] = i;\n}}\nvoid run(int worker_id) {{\n#pragma omp parallel\n{{ float scratch[16];\nfill(scratch);\nscratch[worker_id]++;\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(
            report.findings.is_empty(),
            "{definition} {bound}: {report:#?}"
        );
    }
}

#[test]
fn c_element_helper_bounds_keep_macro_side_effects_unresolved() {
    for (definition, bound, tail) in [
        ("#define WIDTH (publish(p), 4)", "WIDTH", ""),
        ("#define WIDTH 4\n#undef WIDTH", "WIDTH", ""),
        ("#define WIDTH 4\n#define WIDTH 8", "WIDTH", ""),
        ("#ifdef ENABLE\n#define WIDTH 4\n#endif", "WIDTH", ""),
        ("", "WIDTH", "#define WIDTH 4"),
        ("#define WIDTH ALIAS\n#define ALIAS 4", "WIDTH", ""),
        ("#define WIDTH 4", "WIDTH + (publish(p), 0)", ""),
        ("#define WIDTH 4", "WIDTH", "#undef WIDTH"),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.c"), format!("void publish(float *);\n{definition}\nstatic void fill(float p[{bound}]) {{ p[0] = 1; }}\n{tail}\nvoid run(int worker_id) {{\n#pragma omp parallel\n{{ float scratch[16];\nfill(scratch);\nscratch[worker_id]++;\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(
            !report.findings.is_empty(),
            "{definition} {bound} {tail}: {report:#?}"
        );
    }
}

#[test]
fn cross_file_local_pointer_cannot_supply_accessor_contiguity() {
    for unrelated in [
        "void unrelated(int *values) {}",
        "void unrelated() { int *values; }",
        "void unrelated() { static int values[8]; }",
        "void unrelated(int *values);",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.cpp"), "struct Accessor { int &operator[](int); };\nvoid run(Accessor values) {\n#pragma omp parallel for\nfor (int worker_id=0;worker_id<8;++worker_id) {\nvalues[worker_id]++;\n}\n}\n").unwrap();
        fs::write(root.path().join("unrelated.cpp"), unrelated).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(report.findings.is_empty(), "{unrelated}: {report:#?}");
    }
}

#[test]
fn local_pointer_retains_own_parallel_storage_evidence() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("sample.cpp"), "void run(int *values) {\n#pragma omp parallel for\nfor (int worker_id=0;worker_id<8;++worker_id) {\nvalues[worker_id]++;\n}\n}\n").unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(!report.findings.is_empty(), "{report:#?}");
}

#[test]
fn same_file_local_accessor_cannot_borrow_pointer_layout() {
    for extra in ["void unrelated(int *values) {}\n", "int *values;\n"] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.cpp"), format!("struct Accessor {{ int &operator[](int); }};\n{extra}\nvoid run(Accessor values) {{\n#pragma omp parallel for\nfor (int worker_id=0;worker_id<8;++worker_id) {{\nvalues[worker_id]++;\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(report.findings.is_empty(), "{extra}: {report:#?}");
    }
}

#[test]
fn pointer_layout_remains_bound_after_accessor_scope_ends() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("sample.cpp"), "struct Accessor { int &operator[](int); };\nvoid run(int *values) {\n{ Accessor values; }\nvoid unrelated(Accessor values);\n#pragma omp parallel for\nfor (int worker_id=0;worker_id<8;++worker_id) {\nvalues[worker_id]++;\n}\n}\n").unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(!report.findings.is_empty(), "{report:#?}");
}

#[test]
fn initializer_operators_do_not_prove_contiguous_object_storage() {
    for declaration in [
        "Proxy values = source * 2;",
        "Proxy values = source[0];",
        "auto values = source * 2;",
        "auto values = source[0];",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.cpp"), format!("struct Proxy {{ Proxy &operator[](int); Proxy &operator++(); }};\nProxy operator*(Proxy, int);\nProxy source;\n{declaration}\nvoid run() {{\n#pragma omp parallel for\nfor (int worker_id=0;worker_id<8;++worker_id) {{\n++values[worker_id];\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(report.findings.is_empty(), "{declaration}: {report:#?}");
    }
}

#[test]
fn native_declarators_and_pointer_initializers_keep_indexed_risks() {
    for declaration in [
        "int *values;",
        "int values[8];",
        "auto values = new int[8];",
        "auto values = (int *)opaque;",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.cpp"), format!("void *opaque;\n{declaration}\nvoid run() {{\n#pragma omp parallel for\nfor (int worker_id=0;worker_id<8;++worker_id) {{\n++values[worker_id];\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(!report.findings.is_empty(), "{declaration}: {report:#?}");
    }
}

#[test]
fn auto_subscript_result_uses_bound_native_pointer_layers() {
    for declaration in ["int **rows;", "int *rows[8];", "int rows[2][8];"] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.cpp"), format!("{declaration}\nvoid run() {{\nauto values = rows[0];\n#pragma omp parallel for\nfor(int worker_id=0;worker_id<8;++worker_id) {{\nvalues[worker_id]++;\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(!report.findings.is_empty(), "{declaration}: {report:#?}");
    }
}

#[test]
fn auto_subscript_cannot_borrow_unrelated_or_shadowed_pointer_layers() {
    for extra in ["void unrelated(int **rows) {}", "int **rows;"] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.cpp"), format!("struct Proxy {{ Proxy &operator[](int); Proxy &operator++(); }};\n{extra}\nvoid run(Proxy rows) {{\nauto values = rows[0];\n#pragma omp parallel for\nfor(int worker_id=0;worker_id<8;++worker_id) {{\n++values[worker_id];\n}}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(report.findings.is_empty(), "{extra}: {report:#?}");
    }
}

#[test]
fn auto_pointer_table_selection_does_not_prove_cross_row_colocation() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("sample.cpp"), "alignas(128) int first[32];\nalignas(128) int second[32];\nint *rows[2] = {first, second};\nvoid run() {\n#pragma omp parallel for\nfor(int worker_id=0;worker_id<2;++worker_id) {\nauto values = rows[worker_id];\nvalues[0]++;\n}\n}\n").unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(report.findings.is_empty(), "{report:#?}");
}

#[test]
fn ordinary_bpf_array_single_cpu_slot_uses_eight_byte_alignment() {
    for (width, block, extra, isolated) in [
        (8, 32, "", true),
        (8, 64, "", true),
        (8, 128, "", false),
        (16, 128, "", true),
        (1, 64, "", false),
        (
            8,
            64,
            "u32 other = cpu * 8 + 1; bpf_map_update_elem(&timestamps, &other, &value, 0);",
            false,
        ),
        (
            8,
            64,
            "u32 other = (cpu + 1) * 8; bpf_map_update_elem(&timestamps, &other, &value, 0);",
            false,
        ),
        (8, 64, "publish(&timestamps);", false),
        (
            8,
            64,
            "u64 *p = bpf_map_lookup_elem(&timestamps, &key); p[1]++;",
            false,
        ),
        (
            8,
            64,
            "u64 *p = bpf_map_lookup_elem(&timestamps, &key); publish(p);",
            false,
        ),
        (
            8,
            64,
            "mutate(&key); bpf_map_update_elem(&timestamps, &key, &value, 0);",
            false,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("sample.bpf.c"),
            format!(
                r#"
struct {{
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __type(key, u32);
 __type(value, u64);
}} timestamps SEC(".maps");
int enter() {{
 u32 cpu = bpf_get_smp_processor_id();
 u32 key = cpu * {width};
 u64 value = bpf_ktime_get_ns();
 bpf_map_update_elem(&timestamps, &key, &value, 0);
 {extra}
 return 0;
}}
int exit() {{
 u32 cpu = bpf_get_smp_processor_id();
 u32 key = cpu * {width};
 u64 *value = bpf_map_lookup_elem(&timestamps, &key);
 if (value) *value = 0;
 return 0;
}}
"#
            ),
        )
        .unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cache_line_size = block;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|name| name == "timestamps")),
            !isolated,
            "{width} {block} {extra}: {report:#?}"
        );
    }
}

// Ownership and escape tests above exercise the broader candidate calculus:
// losing a nonescape proof is not itself positive index-partition evidence.
fn speculative_index_options() -> AnalysisOptions {
    let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    options.cpp_include_speculative = true;
    options
}

fn analyze_speculative(source: &str, rules: &[CandidateKind]) -> Report {
    // Project a discovery method for these focused regressions; public selection uses relations.
    let mut report = {
        let root = tempdir().unwrap();
        fs::write(root.path().join("candidate.cpp"), source).unwrap();
        let mut options = AnalysisOptions::with_rules(
            &false_sharing_detector::types::ALL_RULES
                .into_iter()
                .filter(|relation| rules.iter().any(|kind| kind.supports(*relation)))
                .collect::<Vec<_>>(),
        );
        options.cpp_include_speculative = true;
        analyze_cpp_path_with_options(root.path(), &options)
    };
    report.findings.retain(|finding| {
        rules.iter().any(|kind| {
            finding.candidate_kind == *kind || finding.related_candidate_kinds.contains(kind)
        })
    });
    report
}

#[test]
fn indexed_parallel_region_needs_a_partition_on_the_selected_writer() {
    for block in [32, 64, 128] {
        for (body, expected) in [
            (
                "#pragma omp parallel\n{\nfor(int i=0;i<16;++i) values[i]++;\n}",
                false,
            ),
            (
                "#pragma omp parallel for\nfor(int i=0;i<16;++i) values[i]++;",
                true,
            ),
            (
                "#pragma omp parallel\n{\n#pragma omp for\nfor(int i=0;i<16;++i) values[i]++;\n}",
                true,
            ),
            (
                "#pragma omp parallel\n{\nint part=omp_get_thread_num();\nvalues[part]++;\n}",
                true,
            ),
            (
                "#pragma omp parallel\n{\nint part=omp_get_thread_num();\nconsume(values[part]);\nfor(int i=0;i<16;++i) values[i]++;\n}",
                false,
            ),
        ] {
            let root = tempdir().unwrap();
            fs::write(
                root.path().join("sample.cpp"),
                format!("void run(int *values) {{\n{body}\n}}\n"),
            )
            .unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
            options.cache_line_size = block;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "{block} {body}: {report:#?}"
            );
            options.cpp_include_speculative = true;
            let speculative = analyze_cpp_path_with_options(root.path(), &options);
            assert!(
                !speculative.findings.is_empty(),
                "unresolved parallel access stays available: {body}"
            );
        }
    }
}

#[test]
fn parallel_callback_binds_one_dimensional_sycl_id_by_type() {
    for (api, ty, overwrite, expected) in [
        ("parallel_for", "sycl::id<1>", "", true),
        ("parallel_for", "::sycl::id<1>", "", true),
        ("parallel_for", "cl::sycl::id<1>", "", true),
        ("parallel_for", "sycl::id<2>", "", false),
        ("parallel_for", "ApplicationId", "", false),
        ("parallel_for", "sycl::id<1>", "position = 0;", false),
        ("consume", "sycl::id<1>", "", false),
    ] {
        let source = format!(
            "void run(int *values) {{\nqueue.{api}(range, [=]({ty} position) {{\n{overwrite}\nvalues[position]++;\n}});\n}}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{source}: {report:#?}"
        );
    }
}

#[test]
fn recovered_const_scalar_declaration_keeps_its_runtime_index_binding() {
    for (ty, overwrite, expected) in [
        ("size_t", "", true),
        ("unsigned int", "", true),
        ("size_t", "piece = 0;", false),
        ("size_t", "piece = unknown_index();", false),
    ] {
        let source = format!(
            "void run(int *values) {{\nconsume(0);\nruntime_omp_parallel {{\nconst {ty} piece = omp_get_thread_num();\n{overwrite}\nruntime_omp_for(int i=0;i<16;i++) {{\nvalues[piece]++;\n}}\n}}\n}}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{source}: {report:#?}"
        );
    }
}

#[test]
fn this_callback_contract_requires_nonvirtual_member_dispatch() {
    for (base, qualifier, body, expected) in [
        ("", "", "action(0);", false),
        ("", "virtual", "action(0);", true),
        (": public Base", "", "action(0);", true),
        ("", "", "save(action);", true),
        ("", "", "queue([&] { action(0); });", true),
    ] {
        let source = format!(
            r#"
struct Base {{}};
class Worker {base} {{
    unsigned values[16];
    void update(unsigned worker_id) {{ values[worker_id]++; }}
    {qualifier} void invoke(const std::function<void(unsigned)> & action) {{ {body} }}
public:
    void parse() {{
        this->invoke([this](unsigned position) {{ update(position); }});
    }}
}};
"#
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "base={base}, qualifier={qualifier}, body={body}: {report:#?}"
        );
    }
}

#[test]
fn member_callback_contract_does_not_guess_other_receivers_or_macro_effects() {
    for (directive, body, receiver) in [
        ("", "action(0);", "other"),
        (
            "#define HIDDEN saved = action",
            "HIDDEN; action(0);",
            "this",
        ),
    ] {
        let source = format!(
            r#"
{directive}
class Worker {{
    unsigned values[16];
    void update(unsigned worker_id) {{ values[worker_id]++; }}
    void invoke(const std::function<void(unsigned)> & action) {{ {body} }}
public:
    void parse(Worker *other) {{
        {receiver}->invoke([this](unsigned position) {{ update(position); }});
    }}
}};
"#
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert!(!report.findings.is_empty(), "{source}: {report:#?}");
    }
}

#[test]
fn indexed_scalar_field_distance_is_bound_to_all_element_uses() {
    use false_sharing_detector::cpp_detection::{
        evidence::collect_indexed_write_candidates, layout::collect_cpp_structs,
        parser::parse_cpp_files, types::CppFile,
    };
    for bytes in [8, 128] {
        let files = parse_cpp_files(vec![CppFile {
            path: "array.hpp".into(),
            source: format!(
                "struct Slot {{ int hits; char payload[{bytes}]; }};\nSlot slots[8];\nvoid update(int thread_id) {{\n slots[thread_id].hits++;\n}}\n"
            ),
        }]);
        for block in [32, 64, 128] {
            let records = collect_cpp_structs(&files, "fixture", block);
            let candidates = collect_indexed_write_candidates(&files, &records, block);
            assert_eq!(
                candidates.is_empty(),
                bytes == 128,
                "{records:?} {candidates:?}"
            );
        }
    }
}

#[test]
fn indexed_field_distance_keeps_boundary_reads_and_unresolved_uses() {
    use false_sharing_detector::cpp_detection::{
        evidence::collect_indexed_write_candidates, layout::collect_cpp_structs,
        parser::parse_cpp_files, types::CppFile,
    };
    for extra in [
        "void second(int thread_id) { slots[thread_id].last++; }",
        "int read(int thread_id) { return slots[thread_id].last; }",
        "void escape(int thread_id) { consume(&slots[thread_id]); }",
        "int& borrow(int thread_id) { return slots[thread_id].first; }",
        "void consume_field(int thread_id) { consume(slots[thread_id].first); }",
        "Slot* alias = slots;",
        "#define ACCESS(i) slots[i].last",
    ] {
        for block in [32, 64, 128] {
            let files = parse_cpp_files(vec![CppFile {
                path: "array.hpp".into(),
                source: format!(
                    "struct Slot {{ int first; char bytes[128]; int last; }};\nSlot slots[8];\nvoid update(int thread_id) {{\n slots[thread_id].first++;\n}}\n{extra}\n"
                ),
            }]);
            let records = collect_cpp_structs(&files, "fixture", block);
            assert!(
                !collect_indexed_write_candidates(&files, &records, block).is_empty(),
                "{extra}"
            );
        }
    }
}

#[test]
fn indexed_field_distance_retains_ambient_packing_and_bitfields() {
    use false_sharing_detector::cpp_detection::{
        evidence::collect_indexed_write_candidates, layout::collect_cpp_structs,
        parser::parse_cpp_files, types::CppFile,
    };
    for declaration in [
        "#pragma pack(push, 1)\nstruct Slot { char prefix; char bytes[61]; int hits; };\n#pragma pack(pop)",
        "struct Slot { unsigned hits : 1; char bytes[128]; };",
    ] {
        let files = parse_cpp_files(vec![CppFile {
            path: "array.hpp".into(),
            source: format!(
                "{declaration}\nSlot slots[8];\nvoid update(int thread_id) {{\n slots[thread_id].hits++;\n}}\n"
            ),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        assert!(
            !collect_indexed_write_candidates(&files, &records, 64).is_empty(),
            "{declaration}"
        );
    }
}

#[test]
fn indexed_field_distance_lower_bound_is_independent_of_padding() {
    use false_sharing_detector::cpp_detection::{
        evidence::collect_indexed_write_candidates, layout::collect_cpp_structs,
        parser::parse_cpp_files, types::CppFile,
    };
    for block in [32, 64, 128] {
        for packed in [false, true] {
            for bytes in [block - 2, block - 1] {
                let prefix = if packed {
                    "# pragma pack(push, 1)\n"
                } else {
                    ""
                };
                let suffix = if packed { "# pragma pack(pop)\n" } else { "" };
                let files = parse_cpp_files(vec![CppFile {
                    path: "array.hpp".into(),
                    source: format!(
                        "{prefix}struct Slot {{ char bytes[{bytes}]; int hits; }};\n{suffix}Slot slots[8];\nvoid update(int thread_id) {{\n slots[thread_id].hits++;\n}}\n"
                    ),
                }]);
                let records = collect_cpp_structs(&files, "fixture", block);
                let candidates = collect_indexed_write_candidates(&files, &records, block);
                assert_eq!(
                    candidates.is_empty(),
                    bytes + 1 >= block,
                    "block={block}, bytes={bytes}, packed={packed}"
                );
            }
        }
    }
}

#[test]
fn ordinary_coordinates_require_bound_caller_partition_provenance() {
    for coordinate in [
        "slot",
        "cell",
        "block",
        "partition",
        "scenario_idx",
        "state_idx",
    ] {
        let body = format!(
            "int values[64];\nvoid update(int {coordinate}) {{\n values[{coordinate}]++;\n}}\n"
        );
        assert!(
            analyze(&body, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{coordinate}"
        );
        for caller in [
            "void run() {\n update(omp_get_thread_num());\n}\n",
            "void run(int worker_id) {\n update(worker_id);\n}\n",
            "void run() {\n#pragma omp parallel for\nfor(int i=0;i<64;++i) {\n update(i);\n}\n}\n",
        ] {
            assert!(
                !analyze(&(body.clone() + caller), &[CandidateKind::IndexedWrites])
                    .findings
                    .is_empty(),
                "{coordinate}: {caller}"
            );
        }
        for caller in [
            "void run() {\nfor(int i=0;i<64;++i) {\n update(i);\n}\n}\n",
            "void run(int worker_id) {\n update(transform(worker_id));\n}\n",
            "void run(int worker_id) {\n auto update = factory();\n update(worker_id);\n}\n",
        ] {
            assert!(
                analyze(&(body.clone() + caller), &[CandidateKind::IndexedWrites])
                    .findings
                    .is_empty(),
                "{coordinate}: {caller}"
            );
        }
    }
}

#[test]
fn immutable_descriptor_external_api_is_not_closed_by_one_local_call() {
    let base = "struct Ticket {\n const int key;\n explicit Ticket(int number) : key(number) {}\n};\nint values[64];\nTicket acquire() { return Ticket(omp_get_thread_num()); }\nvoid release(const Ticket& ticket) {\n values[ticket.key]++;\n}\nvoid run() {\n#pragma omp parallel\n {\n auto ticket = acquire();\n release(ticket);\n }\n}\n";
    assert!(
        !analyze(base, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
    for source in [
        base.replace("key(number)", "key(0)"),
        base.replace("const int key", "int key"),
    ] {
        assert!(
            analyze(&source, &[CandidateKind::IndexedWrites])
                .findings
                .is_empty(),
            "{source}"
        );
    }
    // `release` remains externally callable with a caller-selected Ticket.
    // These local call choices do not close its API or prove runtime MHP.
    for source in [
        base.replace("Ticket(omp_get_thread_num())", "Ticket(0)"),
        base.replace(
            "auto ticket = acquire();",
            "auto acquire = [] { return Ticket(0); };\nauto ticket = acquire();",
        ),
        base.replace(
            "auto ticket = acquire();",
            "auto release = [](auto) {};\nauto ticket = acquire();",
        ),
        base.replace("release(ticket);", "unknown(ticket);\nrelease(ticket);"),
        base.replace(
            "int number) : key(number)",
            "int number, int other) : key(other)",
        )
        .replace(
            "Ticket(omp_get_thread_num())",
            "Ticket(omp_get_thread_num(), 0)",
        ),
        format!("int omp_get_thread_num() {{ return 0; }}\n{base}"),
    ] {
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert!(!report.findings.is_empty(), "{source}");
        assert!(
            report
                .findings
                .iter()
                .all(|f| f.static_pattern.as_ref().is_some_and(
                    |p| p.parallelism_evidence == ParallelismEvidence::ExternalApiPotential
                )),
            "{source}\n{report:#?}"
        );
    }
    let reordered = base
        .replace(
            "int number) : key(number)",
            "int number, int other) : key(other)",
        )
        .replace(
            "Ticket(omp_get_thread_num())",
            "Ticket(0, omp_get_thread_num())",
        );
    assert!(
        !analyze(&reordered, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
}

#[test]
fn indexed_call_summaries_preserve_the_callees_common_global_mutex() {
    for block in [32, 64, 128] {
        for (declaration, parameter, body, expected) in [
            (
                "pthread_mutex_t gate;",
                "",
                "pthread_mutex_lock(&gate);\nvalues[index] = 0;\npthread_mutex_unlock(&gate);",
                false,
            ),
            (
                "std::mutex gate;",
                "",
                "std::lock_guard guard(gate);\nvalues[index]++;",
                false,
            ),
            (
                "pthread_mutex_t gate;",
                "",
                "pthread_mutex_lock(&gate);\npthread_mutex_unlock(&gate);\nvalues[index] = 0;",
                true,
            ),
            (
                "pthread_mutex_t gate;",
                "",
                "pthread_mutex_lock(&gate);\nvalues[index] = 0;\npthread_mutex_unlock(&gate);\nvalues[0]++;",
                true,
            ),
            (
                "pthread_mutex_t gate, other;",
                "",
                "pthread_mutex_lock(&gate);\nvalues[index] = 0;\npthread_mutex_unlock(&gate);\npthread_mutex_lock(&other);\nvalues[index]++;\npthread_mutex_unlock(&other);",
                true,
            ),
            (
                "",
                ", pthread_mutex_t& gate",
                "pthread_mutex_lock(&gate);\nvalues[index] = 0;\npthread_mutex_unlock(&gate);",
                true,
            ),
            (
                "thread_local pthread_mutex_t gate;",
                "",
                "pthread_mutex_lock(&gate);\nvalues[index] = 0;\npthread_mutex_unlock(&gate);",
                true,
            ),
            (
                "pthread_mutex_t gate;",
                "",
                "pthread_mutex_t gate;\npthread_mutex_lock(&gate);\nvalues[index] = 0;\npthread_mutex_unlock(&gate);",
                true,
            ),
        ] {
            let root = tempdir().unwrap();
            let source = format!(
                "{declaration}\nint values[64];\nvoid change(int index{parameter}) {{\n{body}\n}}\nvoid run(int worker_id) {{\nchange(worker_id{});\n}}\n",
                if parameter.is_empty() {
                    ""
                } else {
                    ", external_gate"
                }
            );
            fs::write(root.path().join("slots.cpp"), &source).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
            options.cache_line_size = block;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            let at_call = report.findings.iter().any(|f| {
                f.symbol.as_deref() == Some("run") && f.field_list.contains(&"values".into())
            });
            assert_eq!(at_call, expected, "B={block}: {source}\n{report:#?}");
        }
    }
}

#[test]
fn indexed_lock_macros_require_visible_definitions_and_a_shared_declared_object() {
    let base_header = "#define MAKE_MUTEX(x) pthread_mutex_t x##_mutex = PTHREAD_MUTEX_INITIALIZER\n#define TAKE(x) pthread_mutex_lock(&x##_mutex)\n#define GIVE(x) pthread_mutex_unlock(&x##_mutex)\n#ifndef INTERNAL\n#define INTERNAL static\n#endif\n";
    let body = "int values[64];\nvoid change(int index) {\nTAKE(serial);\nvalues[index] = 0;\nGIVE(serial);\n}\nvoid run(int worker_id) {\nchange(worker_id);\n}\n";
    for (header, source, expected) in [
        (
            format!(
                "{base_header}\n#define TRACE(x) do {{ TAKE(logger); GIVE(logger); }} while(0)\n"
            ),
            format!(
                "#include \"locks.h\"\nMAKE_MUTEX(serial);\n{body}\nvoid unrelated() {{ TRACE(0); }}\n"
            ),
            false,
        ),
        (
            format!("{base_header}\n#define TAKE(x)\n"),
            format!("#include \"locks.h\"\nMAKE_MUTEX(serial);\n{body}"),
            true,
        ),
        (
            base_header.to_string(),
            format!("#include \"locks.h\"\nINTERNAL MAKE_MUTEX(serial);\n{body}"),
            false,
        ),
        (
            base_header.to_string(),
            format!(
                "#ifndef ENABLED\nvoid idle() {{}}\n#else\n#include \"locks.h\"\nINTERNAL MAKE_MUTEX(serial);\n{body}\n#endif"
            ),
            false,
        ),
        (
            base_header.to_string(),
            format!("INTERNAL MAKE_MUTEX(serial);\n{body}"),
            true,
        ),
        (
            base_header.to_string(),
            format!(
                "#ifdef ENABLED\n#include \"locks.h\"\n#endif\nINTERNAL MAKE_MUTEX(serial);\n{body}"
            ),
            true,
        ),
        (
            base_header.replace("pthread_mutex_t x", "__thread pthread_mutex_t x"),
            format!("#include \"locks.h\"\nMAKE_MUTEX(serial);\n{body}"),
            true,
        ),
        (
            format!("{base_header}\n#ifdef OTHER\n#define GIVE(x) ignore(x)\n#endif\n"),
            format!(
                "#include \"locks.h\"\nMAKE_MUTEX(serial);\n{}",
                body.replace(
                    "values[index] = 0;\nGIVE(serial);",
                    "GIVE(serial);\nvalues[index] = 0;"
                )
            ),
            true,
        ),
        (
            format!("{base_header}\n#undef GIVE\n#define GIVE(x)\n"),
            format!(
                "#include \"locks.h\"\nMAKE_MUTEX(serial);\n{}",
                body.replace(
                    "values[index] = 0;\nGIVE(serial);",
                    "GIVE(serial);\nvalues[index] = 0;"
                )
            ),
            true,
        ),
        (
            base_header.to_string(),
            format!(
                "#include \"locks.h\"\n{}",
                body.replace("TAKE(serial);", "MAKE_MUTEX(serial);\nTAKE(serial);")
            ),
            true,
        ),
        (
            base_header.to_string(),
            format!(
                "#include \"locks.h\"\nMAKE_MUTEX(serial);\n{}",
                body.replace(
                    "values[index] = 0;\nGIVE(serial);",
                    "GIVE(serial);\nvalues[index] = 0;"
                )
            ),
            true,
        ),
        (
            format!("{base_header}\n#define DROP(x) GIVE(x)\n"),
            format!(
                "#include \"locks.h\"\nMAKE_MUTEX(serial);\n{}",
                body.replace(
                    "values[index] = 0;\nGIVE(serial);",
                    "DROP(serial);\nvalues[index] = 0;"
                )
            ),
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("locks.h"), &header).unwrap();
        fs::write(root.path().join("slots.cpp"), &source).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{header}\n{source}\n{report:#?}"
        );
    }
}

#[test]
fn lock_macro_proofs_respect_compile_database_overrides() {
    for (flags, expected) in [
        (vec!["-DUNRELATED=1"], false),
        (vec!["-DINTERNAL=thread_local"], true),
        (vec!["-D", "INTERNAL=thread_local"], true),
        (vec!["/DINTERNAL=thread_local"], true),
        (vec!["-UTAKE"], true),
        (vec!["-Dpthread_mutex_lock=pretend_lock"], true),
        (vec!["-include", "unknown_config.h"], true),
        (vec!["@flags.rsp"], true),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("locks.h"), "#define MAKE_MUTEX(x) pthread_mutex_t x##_mutex = PTHREAD_MUTEX_INITIALIZER\n#define TAKE(x) pthread_mutex_lock(&x##_mutex)\n#define GIVE(x) pthread_mutex_unlock(&x##_mutex)\n#ifndef INTERNAL\n#define INTERNAL static\n#endif\n").unwrap();
        let path = root.path().join("slots.cpp");
        fs::write(&path, "#include \"locks.h\"\nINTERNAL MAKE_MUTEX(serial);\nint values[64];\nvoid change(int index) {\nTAKE(serial);\nvalues[index] = 0;\nGIVE(serial);\n}\nvoid run(int worker_id) {\nchange(worker_id);\n}\n").unwrap();
        let mut arguments = vec!["c++"];
        arguments.extend(flags.clone());
        arguments.extend(["-c", "slots.cpp"]);
        fs::write(root.path().join("compile_commands.json"), serde_json::to_string(&serde_json::json!([{
            "directory": root.path().to_str().unwrap(), "file": path.to_str().unwrap(), "arguments": arguments
        }])).unwrap()).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{flags:?}: {report:#?}"
        );
    }
}

#[test]
fn internal_free_function_parameter_names_are_not_external_partition_apis() {
    for block in [32, 64, 128] {
        for (prefix, suffix) in [("static ", ""), ("namespace {\n", "}\n")] {
            for caller in [
                "void run() { for (int i=0;i<16;++i) change(i); }",
                "void run() { change(0); }",
                "",
            ] {
                let root = tempdir().unwrap();
                let source = format!(
                    "int slots[16];\n{prefix}void change(int worker_id) {{\nslots[worker_id]++;\n}}\n{caller}\n{suffix}"
                );
                fs::write(root.path().join("local.cpp"), &source).unwrap();
                let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
                options.cache_line_size = block;
                let report = analyze_cpp_path_with_options(root.path(), &options);
                assert!(
                    report.findings.is_empty(),
                    "B={block}: {source}\n{report:#?}"
                );
            }
        }
    }
}

#[test]
fn internal_partition_helpers_recover_bound_api_and_runtime_callers() {
    for (prefix, suffix) in [("static ", ""), ("namespace {\n", "}\n")] {
        for caller in [
            "void run(int worker_id) { forward(worker_id); }",
            "void run() { forward(omp_get_thread_num()); }",
            "void run() {\n#pragma omp parallel for\nfor (int i=0;i<16;++i) forward(i);\n}",
        ] {
            // In the namespace case run itself is internal; an actual runtime
            // index remains a root, and an escaping API-style callback does too.
            let escape = if prefix.starts_with("namespace") {
                "auto entry = run;"
            } else {
                ""
            };
            let source = format!(
                "int slots[16];\n{prefix}void change(int worker_id) {{\nslots[worker_id]++;\n}}\nstatic void forward(int coordinate) {{ change(coordinate); }}\n{caller}\n{escape}\n{suffix}"
            );
            let report = analyze(&source, &[CandidateKind::IndexedWrites]);
            assert!(!report.findings.is_empty(), "{source}\n{report:#?}");
        }
    }
}

#[test]
fn internal_callable_escapes_headers_and_ambiguous_lookup_remain_candidates() {
    for tail in [
        "auto callback = change;",
        "void launch() { register_callback(change); }",
        "#define APPLY(x) change(x)\nvoid run(int i) { APPLY(i); }",
        "void change(double worker_id);\nvoid run() { change(1.0); }",
        "namespace other { void change(int worker_id) {} }",
    ] {
        let source = format!(
            "int slots[16];\nstatic void change(int worker_id) {{\nslots[worker_id]++;\n}}\n{tail}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert!(!report.findings.is_empty(), "{source}\n{report:#?}");
    }
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("api.hpp"),
        "int slots[16];\nstatic void change(int worker_id) {\nslots[worker_id]++;\n}\n",
    )
    .unwrap();
    assert!(
        !analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements])
        )
        .findings
        .is_empty()
    );
}

#[test]
fn internal_helpers_keep_distinct_constant_thread_entry_paths() {
    let source = r#"
        int slots[16];
        static void change(int worker_id) {
            slots[worker_id]++;
        }
        void run() {
            std::thread first([] { change(0); });
            std::thread second([] { change(1); });
            first.join(); second.join();
        }
    "#;
    assert!(
        !analyze(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
}

#[test]
fn internal_scalar_and_pointer_overloads_do_not_manufacture_api_roots() {
    for (body, expected) in [
        ("for (int i=0;i<16;++i) change(i);", false),
        ("change(omp_get_thread_num());", true),
        (
            "auto pointer = (int*)omp_get_thread_num(); change(pointer);",
            false,
        ),
    ] {
        let source = format!(
            "namespace {{\nint slots[16];\nvoid change(int *pointer) {{ *pointer += 1; }}\nvoid change(int worker_id) {{\nslots[worker_id]++;\n}}\nvoid run() {{ {body} }}\n}}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{source}\n{report:#?}"
        );
    }
}

#[test]
fn internal_api_refinement_preserves_ambiguous_same_line_callables() {
    let source = "int slots[16];\nvoid exposed(int worker_id) { slots[worker_id]++; } static void hidden(int worker_id) { slots[worker_id]++; }\n";
    assert!(
        !analyze(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
}

#[test]
fn internal_linkage_survives_unrelated_preprocessor_argument_recovery() {
    let source = r#"
        namespace {
        int slots[16];
        void change(int *pointer) {
            consume(pointer
        #ifdef EXTRA
                , 1
        #endif
            );
        }
        void change(int worker_id) {
            slots[worker_id]++;
        }
        void run() {
            for (int i=0;i<16;++i) change(i);
        }
        }
    "#;
    assert!(
        analyze(source, &[CandidateKind::IndexedWrites])
            .findings
            .is_empty()
    );
}

#[test]
fn linkage_keyword_macros_do_not_close_external_partition_apis() {
    let body = "int slots[16];\nstatic void update(int worker_id) {\nslots[worker_id]++;\n}\n";
    for prefix in [
        "#define static\n",
        "#if CONFIG\n#define static\n#endif\n",
        "#define sta\\\ntic\n",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("case.c"), format!("{prefix}{body}")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(!report.findings.is_empty(), "{prefix}\n{report:#?}");
    }
    let root = tempdir().unwrap();
    fs::write(root.path().join("compat.h"), "#define static\n").unwrap();
    fs::write(
        root.path().join("case.c"),
        format!("#include \"compat.h\"\n{body}"),
    )
    .unwrap();
    assert!(
        !analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements])
        )
        .findings
        .is_empty()
    );
}

#[test]
fn compile_command_linkage_overrides_remain_unresolved() {
    for extra in [
        vec!["-Dstatic="],
        vec!["-D", "static="],
        vec!["-include", "compat.h"],
        vec!["@flags.rsp"],
    ] {
        let root = tempdir().unwrap();
        let path = root.path().join("case.c");
        fs::write(
            &path,
            "int slots[16];\nstatic void update(int worker_id) {\nslots[worker_id]++;\n}\n",
        )
        .unwrap();
        let mut args = vec!["cc".to_string()];
        args.extend(extra.iter().map(|x| x.to_string()));
        args.push(path.to_string_lossy().into_owned());
        fs::write(
            root.path().join("compile_commands.json"),
            serde_json::json!([{"directory":root.path(),"file":path,"arguments":args}]).to_string(),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert!(!report.findings.is_empty(), "{extra:?}\n{report:#?}");
    }
}

#[test]
fn atomic_accessor_returns_bind_the_actual_storage_and_target_argument() {
    let helper = "int &slot(int *values, int coordinate) {\nreturn values[coordinate];\n}\n";
    for (body, expected) in [
        ("__sync_fetch_and_add(&slot(data, worker_id), 1);", true),
        ("__atomic_store_n(&slot(data, worker_id), 1, 0);", true),
        (
            "__sync_fetch_and_add(/* target */ &slot(/* storage */ data, /* partition */ worker_id), 1);",
            true,
        ),
        ("custom_atomic_fetch_add(&slot(data, worker_id), 1);", false),
        (
            "__sync_fetch_and_add(counter, slot(data, worker_id));",
            false,
        ),
        (
            "consume(slot(data, worker_id)); __sync_fetch_and_add(counter, 1);",
            false,
        ),
        ("__atomic_load_n(&slot(data, worker_id), 0);", false),
        ("__sync_fetch_and_add(&slot(data, 0), worker_id);", false),
        (
            "__sync_fetch_and_add(transform(&slot(data, worker_id)), 1);",
            false,
        ),
        (
            "__sync_fetch_and_add(&slot(data, worker_id), slot(data, 0));",
            true,
        ),
    ] {
        let report = analyze(
            &format!(
                "{helper}\nvoid consume(int);\nint *transform(int *);\nvoid update(int *data, int *counter, int worker_id) {{\n{body}\n}}\n"
            ),
            &[CandidateKind::IndexedWrites],
        );
        assert_eq!(!report.findings.is_empty(), expected, "{body}: {report:#?}");
        for finding in &report.findings {
            assert_eq!(finding.field_list, ["data"], "{body}: {report:#?}");
        }
    }
}

#[test]
fn atomic_accessor_native_return_shapes_are_positional() {
    for (helper, call, expected) in [
        (
            "int &slot(int position, int *values) { return values[position]; }",
            "&slot(worker_id, data)",
            true,
        ),
        (
            "int *slot(int *values, int position) { return &values[position]; }",
            "slot(data, worker_id)",
            true,
        ),
        (
            "int *slot(int **values, int position) { return values[position]; }",
            "slot(data, worker_id)",
            false,
        ),
        (
            "int &slot(Proxy *values, int position) { return values[position]; }",
            "&slot(data, worker_id)",
            false,
        ),
        (
            "int &slot(Proxy &values, int position) { return values[position]; }",
            "&slot(data, worker_id)",
            false,
        ),
        (
            "int &slot(int *values, int position) { return values[0]; }",
            "&slot(data, worker_id)",
            false,
        ),
        (
            "int &slot(int *values, int position) { return values[choose(position)]; }",
            "&slot(data, worker_id)",
            false,
        ),
        (
            "int &slot(int *values, int position) { values = other; return values[position]; }",
            "&slot(data, worker_id)",
            false,
        ),
    ] {
        let report = analyze(
            &format!(
                "{helper}\nvoid update(int *data, int worker_id) {{\n__sync_fetch_and_add({call}, 1);\n}}\n"
            ),
            &[CandidateKind::IndexedWrites],
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{helper}: {report:#?}"
        );
    }
}

#[test]
fn atomic_accessor_receivers_cannot_borrow_same_named_methods() {
    for (receiver, expected) in [("Slots", true), ("Other", false), ("Unknown", false)] {
        let source = format!(
            "struct Slots {{ int marker;\nint &slot(int *values, int position) {{ return values[position]; }}\n}};\nstruct Other {{ int marker; int &slot(int *, int); }};\nvoid update({receiver} &object, int *data, int worker_id) {{\n__sync_fetch_and_add(&object.slot(data, worker_id), 1);\n}}\n"
        );
        let report = analyze(&source, &[CandidateKind::IndexedWrites]);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{receiver}: {report:#?}"
        );
    }
}

#[test]
fn atomic_accessor_shadowing_and_overloads_supply_no_summary() {
    let helper = "int &slot(int *values, int position) { return values[position]; }\n";
    for (extra, body) in [
        (
            "",
            "auto slot = other;\n__sync_fetch_and_add(&slot(data, worker_id), 1);",
        ),
        (
            "int &slot(int *, unsigned);",
            "__sync_fetch_and_add(&slot(data, worker_id), 1);",
        ),
        (
            "#define slot(p, i) other(p, i)",
            "__sync_fetch_and_add(&slot(data, worker_id), 1);",
        ),
        (
            "#define __sync_fetch_and_add(p, v) consume(p)",
            "__sync_fetch_and_add(&slot(data, worker_id), 1);",
        ),
    ] {
        let report = analyze(
            &format!("{helper}{extra}\nvoid update(int *data, int worker_id) {{\n{body}\n}}\n"),
            &[CandidateKind::IndexedWrites],
        );
        assert!(report.findings.is_empty(), "{extra} {body}: {report:#?}");
    }
}

#[test]
fn atomic_accessor_summary_follows_a_cross_file_member_body() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("storage.hpp"), "struct Slots { int marker;\nint &slot(int *values, int position) {\nreturn values[(unsigned)position >> 6];\n}\nvoid update(int *data, int worker_id);\n};\n").unwrap();
    fs::write(root.path().join("sample.cpp"), "#include \"storage.hpp\"\nvoid Slots::update(int *data, int worker_id) {\n__sync_fetch_and_add(&slot(data, worker_id), 1);\n}\n").unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert_eq!(report.findings.len(), 1, "{report:#?}");
    assert_eq!(report.findings[0].field_list, ["data"]);
}

#[test]
fn atomic_accessor_stride_uses_a_type_independent_bound_and_configured_block() {
    for (ty, step, size, expected) in [
        ("char", 64, 32, false),
        ("char", 64, 64, false),
        ("char", 64, 128, true),
        ("int", 16, 64, true),
        ("int", 16, 128, true),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.cpp"),format!("{ty} &slot({ty} *values, int position) {{ return values[position * {step}]; }}\nvoid update({ty} *data, int worker_id) {{\n__sync_fetch_and_add(&slot(data,worker_id),1);\n}}\n")).unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cache_line_size = size;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{ty} {step} B={size}: {report:#?}"
        );
    }
    for expression in [
        "position * 0",
        "position & 0",
        "position % 1",
        "position ^ position",
    ] {
        let report = analyze(
            &format!(
                "int &slot(int *values,int position) {{ return values[{expression}]; }}\nvoid update(int *data,int worker_id) {{\n__sync_fetch_and_add(&slot(data,worker_id),1);\n}}\n"
            ),
            &[CandidateKind::IndexedWrites],
        );
        assert!(report.findings.is_empty(), "{expression}: {report:#?}");
    }
}

#[test]
fn atomic_accessor_stride_does_not_borrow_an_unexpanded_scalar_size() {
    for prefix in ["#define int char\n", ""] {
        let report = analyze(
            &format!(
                "{prefix}int &slot(int *values, int position) {{\nreturn values[position * 16];\n}}\nvoid update(int *data, int worker_id) {{\n__sync_fetch_and_add(&slot(data, worker_id),1);\n}}\n"
            ),
            &[CandidateKind::IndexedWrites],
        );
        assert_eq!(report.findings.len(), 1, "{prefix}: {report:#?}");
        assert_eq!(report.findings[0].field_list, ["data"]);
    }
}

#[test]
fn atomic_index_summaries_bind_the_written_field_and_parameter() {
    for size in [32, 64, 128] {
        for (body, arguments, expected) in [
            (
                "plain[first]++;\n__atomic_fetch_add(&atomic_values[second], 1, 0);",
                "incoming, 0",
                false,
            ),
            (
                "atomic_values[first]++;\n__atomic_fetch_add(&atomic_values[second], 1, 0);",
                "incoming, 0",
                false,
            ),
            (
                "__atomic_fetch_add(&atomic_values[second], 1, 0);",
                "0, incoming",
                true,
            ),
            (
                "plain[first]++;\n__atomic_fetch_add(&atomic_values[second], 1, 0);",
                "worker_id, 0",
                true,
            ),
        ] {
            let root = tempdir().unwrap();
            let source = format!(
                "int plain[32];\nint atomic_values[32];\nvoid change(int first, int second) {{\n{body}\n}}\nvoid invoke(int incoming, int worker_id) {{\nchange({arguments});\n}}\n"
            );
            fs::write(root.path().join("sample.cpp"), source).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
            options.cache_line_size = size;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            let propagated = report
                .findings
                .iter()
                .flat_map(|f| &f.access_evidence)
                .any(|a| a.function_name.as_deref() == Some("invoke"));
            assert_eq!(
                propagated, expected,
                "B={size} {body} {arguments}: {report:#?}"
            );
        }
    }
}

#[test]
fn atomic_index_summary_does_not_treat_an_object_pointer_as_a_partition() {
    let source = "struct Descriptor { int index; };\nint values[32];\nvoid change(Descriptor *object) {\n__atomic_fetch_add(&values[object->index], 1, 0);\n}\nvoid invoke(Descriptor *object) {\nchange(object);\n}\n";
    let report = analyze(source, &[CandidateKind::IndexedWrites]);
    assert!(
        !report
            .findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .any(|a| a.function_name.as_deref() == Some("invoke")),
        "{report:#?}"
    );
}

#[test]
fn cache_related_index_spelling_does_not_prove_a_stride() {
    for index in ["slot", "cache_line_slot", "padded_slot"] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("index.cpp"),
            format!(
                "int omp_get_thread_num();\nvoid run(int counters[8]) {{
 int {index} = omp_get_thread_num();
 counters[{index}]++;
 }}"
            ),
        )
        .unwrap();
        for block in [32, 64, 128] {
            let options = AnalysisOptions {
                cache_line_size: block,
                ..AnalysisOptions::with_rules(&[RuleId::ContiguousElements])
            };
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert!(
                !report.findings.is_empty(),
                "{index}, B={block}: {report:#?}"
            );
        }
    }
}

#[test]
fn bpf_wrapper_effects_follow_the_body_and_argument_binding() {
    for helper in ["array_incr", "update_slot"] {
        for (body, call, expected) in [
            ("(void)map; (void)key;", "HELPER(&counters, cpu);", false),
            (
                "u64 value = 1; bpf_map_update_elem(map, &key, &value, 0); u32 other = key % 2; bpf_map_update_elem(map, &other, &value, 0);",
                "HELPER(&counters, cpu);",
                false,
            ),
            (
                "u64 local = 0; u64 *value = bpf_map_lookup_elem(map, &key); value = &local; __sync_fetch_and_add(value, 1);",
                "HELPER(&counters, cpu);",
                false,
            ),
            (
                "u64 *value = 0; if (key) { u64 *value = bpf_map_lookup_elem(map, &key); } __sync_fetch_and_add(value, 1);",
                "HELPER(&counters, cpu);",
                false,
            ),
            (
                "u64 *value = bpf_map_lookup_elem(map, &key); if(value) __sync_fetch_and_add(value, 1);",
                "HELPER(&counters, cpu);",
                true,
            ),
            (
                "u64 value = 1; bpf_map_update_elem(map, &key, &value, 0);",
                "HELPER(&counters, cpu);",
                true,
            ),
            (
                "u64 value = 1; bpf_map_update_elem(map, &key, &value, 0);",
                "HELPER(&counters, 0);",
                false,
            ),
        ] {
            let root = tempdir().unwrap();
            let call = call.replace("HELPER", helper);
            fs::write(
                root.path().join("map.c"),
                format!(
                    "typedef unsigned int u32; typedef unsigned long u64;\nstruct {{
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __type(key, u32);
 __type(value, u64);
 }} counters SEC(\".maps\");\nstatic void {helper}(void *map, u32 key) {{ {body} }}\nint sample() {{
 u32 cpu = bpf_get_smp_processor_id();
 {call}
 return 0;
 }}"
                ),
            )
            .unwrap();
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
            );
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "{helper}: {body}: {call}: {report:#?}"
            );
        }
    }
    let root = tempdir().unwrap();
    fs::write(root.path().join("map.c"), "typedef unsigned int u32; typedef unsigned long u64;\nstruct {
 __uint(type, BPF_MAP_TYPE_ARRAY);
 __type(value, u64);
 } counters SEC(\".maps\");\nstatic void reordered(u32 key, void *map) { u64 value = 1; bpf_map_update_elem(map, &key, &value, 0); }\nint sample() {
 u32 cpu = bpf_get_smp_processor_id();
 reordered(cpu, &counters);
 return 0;
 }").unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
    );
    assert!(!report.findings.is_empty(), "{report:#?}");
}
