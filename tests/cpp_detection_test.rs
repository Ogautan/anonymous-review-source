use false_sharing_detector::types::RuleId;
use std::fs;

use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
use false_sharing_detector::types::{AnalysisOptions, CandidateKind, Report};
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use tempfile::tempdir;

fn analyze(source: &str, rule: CandidateKind) -> Report {
    // Project a discovery method for these focused regressions; public selection uses relations.
    let mut report = {
        let root = tempdir().expect("create temporary C++ project");
        fs::write(root.path().join("candidate.cpp"), source).expect("write C++ fixture");
        // These fixtures exercise the underlying may-risk rules independently of
        // the default reviewability policy, which has dedicated tests below.
        let mut options = AnalysisOptions::with_rules(
            &false_sharing_detector::types::ALL_RULES
                .into_iter()
                .filter(|relation| rule.supports(*relation))
                .collect::<Vec<_>>(),
        );
        options.cpp_include_speculative = true;
        analyze_cpp_path_with_options(root.path(), &options)
    };
    report.findings.retain(|finding| {
        [rule].iter().any(|kind| {
            finding.candidate_kind == *kind || finding.related_candidate_kinds.contains(kind)
        })
    });
    report
}

#[test]
fn cpp_mixed_layout_does_not_project_unrelated_same_named_types() {
    let source = r#"
        namespace unrelated { struct Payload {
            std::atomic<int> target_count;
            void update() { ++target_count; }
        }; }
        namespace local {
        struct Payload { int data; };
        struct Owner {
            Payload ref;
            std::atomic<int> requests;
            void read() {
                consume(ref);
            }
            void count() {
                ++requests;
            }
        };
        }
    "#;
    use false_sharing_detector::cpp_detection::{
        evidence::collect_cpp_evidence, layout::collect_cpp_structs, parser::parse_cpp_files,
        rules::apply_cpp_rules, types::CppFile,
    };
    for (source, expected) in [
        (source.to_string(), false),
        (
            source.replace("Payload ref;", "::local::Payload ref;"),
            false,
        ),
        (
            source.replace("Payload ref;", "missing::Payload ref;"),
            false,
        ),
        (
            source.replace("Payload ref;", "unrelated::Payload ref;"),
            true,
        ),
        (
            source.replace("int data;", "std::atomic<int> target_count;"),
            true,
        ),
    ] {
        let files = parse_cpp_files(vec![CppFile {
            path: "fixture.hpp".into(),
            source,
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        let findings = apply_cpp_rules(
            &records,
            &facts,
            &[],
            &[],
            &[],
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        let owner = findings
            .iter()
            .find(|f| {
                f.struct_name.as_deref() == Some("Owner")
                    && f.candidate_kind == CandidateKind::MixedFields
            })
            .expect("holder read can still conflict with adjacent counter");
        assert_eq!(
            owner.field_list.iter().any(|name| name == "target_count"),
            expected,
            "{owner:#?}"
        );
    }
}

#[test]
fn cpp_declaration_projection_requires_typed_member_ownership() {
    for (signature, expression, projected) in [
        (
            "void update(int *slots, int worker_id)",
            "slots[worker_id]++",
            false,
        ),
        (
            "void update(Owner *owner, int worker_id)",
            "owner->slots[worker_id]++",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("owner.hpp"),
            "struct Owner { int slots[16]; };\n",
        )
        .unwrap();
        fs::write(
            root.path().join("worker.cpp"),
            format!("{signature} {{\n{expression};\n}}\n"),
        )
        .unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cpp_include_speculative = true;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.file.ends_with("owner.hpp")),
            projected,
            "{report:#?}"
        );
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.file.ends_with("worker.cpp")),
            "preserve access-site hypothesis: {report:#?}"
        );
    }
}

#[test]
fn cpp_api_blind_store_is_speculative_but_state_update_is_reviewable() {
    for (operation, expected) in [("= 0", false), ("+= 1", true)] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("state.cpp"),
            format!(
                "int slots[16];\nvoid update(int worker_id) {{\nslots[worker_id] {operation};\n}}\n"
            ),
        )
        .unwrap();
        let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(!report.findings.is_empty(), expected, "{report:#?}");
        let mut broad = options;
        broad.cpp_include_speculative = true;
        assert!(
            !analyze_cpp_path_with_options(root.path(), &broad)
                .findings
                .is_empty()
        );
    }
}

#[test]
fn cpp_scalar_prvalue_does_not_publish_private_array() {
    for (argument, expected) in [
        ("(int)local[worker_id]", false),
        ("local[worker_id] + 1", false),
        ("local[worker_id]", true),
        ("&local[worker_id]", true),
        ("[&] { return local[worker_id] + 1; }", true),
    ] {
        let source = format!(
            "void run(int worker_id) {{\nint local[8] = {{}};\nfor (int n=0; n<100; ++n) {{\nlocal[worker_id]++;\nconsume({argument});\n}}\n}}\n"
        );
        assert_eq!(
            !analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn cpp_static_local_array_does_not_borrow_other_functions_parameters() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("storage.cpp"), "void owner() {\nstatic char buffer[sizeof(std::mutex)]{};\n}\nchar *range(char *buffer, int worker_id) {\nreturn buffer + worker_id;\n}\nvoid modify(char *buffer, int worker_id) {\nbuffer[worker_id]++;\n}\n").unwrap();
    let mut options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    options.cpp_include_speculative = true;
    assert!(
        analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .iter()
            .all(|finding| !finding.has_candidate(CandidateKind::StaticData))
    );
    fs::write(root.path().join("storage.cpp"), "char *range(int worker_id) {\nstatic char buffer[sizeof(std::mutex)]{};\nreturn buffer + worker_id;\n}\n").unwrap();
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .iter()
            .all(|finding| !finding.has_candidate(CandidateKind::StaticData))
    );
}

#[test]
fn cpp_atomic_setter_and_readers_do_not_establish_recurrent_writes() {
    for (write, expected) in [("left.store(1)", false), ("left.fetch_add(1)", true)] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("state.hpp"), format!("struct State {{\nstd::atomic<int> left;\nstd::atomic<int> right;\nvoid set() {{ {write}; }}\nint read() {{ return right.load(); }}\n}};\n")).unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
        assert_eq!(
            !analyze_cpp_path_with_options(root.path(), &options)
                .findings
                .is_empty(),
            expected
        );
        options.cpp_include_speculative = true;
        assert!(
            !analyze_cpp_path_with_options(root.path(), &options)
                .findings
                .is_empty()
        );
    }
}

#[test]
fn cpp_inline_subobject_effect_requires_a_bound_receiver_and_body() {
    for (method, member, call, expected) in [
        (
            "void touch() { value.fetch_add(1); }",
            "Inner state;",
            "p->state.touch()",
            true,
        ),
        (
            "void touch() { value.load(); }",
            "Inner state;",
            "p->state.touch()",
            false,
        ),
        (
            "auto touch() { return [this] { value.fetch_add(1); }; }",
            "Inner state;",
            "p->state.touch()",
            false,
        ),
        (
            "void touch() { value.fetch_add(1); }",
            "Inner *state;",
            "p->state->touch()",
            false,
        ),
        (
            "void touch(Inner *other) { other->value.fetch_add(1); }",
            "Inner state;",
            "p->state.touch(other)",
            false,
        ),
        (
            "void touch() { value.fetch_add(1); } void touch(int) { value.load(); }",
            "Inner state;",
            "p->state.touch(1)",
            false,
        ),
        (
            "void touch() { value.fetch_add(1); } void touch(int) { value.fetch_add(2); }",
            "Inner state;",
            "p->state.touch(1)",
            true,
        ),
        (
            "void touch() { value.fetch_add(1); }",
            "Wrapper<Inner> state;",
            "p->state.touch()",
            false,
        ),
        (
            "void touch() { value.fetch_add(1); }",
            "Missing::Inner state;",
            "p->state.touch()",
            false,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("objects.hpp"), format!("struct Inner {{\nstd::atomic<int> value;\n{method}\n}};\nstruct Outer {{\n{member}\nstd::atomic<int> flag;\n}};\nvoid change(Outer *p, Inner *other) {{ {call}; }}\nint read(Outer *p) {{ return p->flag.load(); }}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("Outer")),
            expected,
            "{method} {member}\n{report:#?}"
        );
    }
}

#[test]
fn cpp_indexed_call_summary_preserves_write_instead_of_inventing_rmw() {
    for (operation, kind) in [("= 0", "write"), ("+= 1", "read_modify_write")] {
        let source = format!(
            "int slots[16];\nvoid put(int index) {{\nslots[index] {operation};\n}}\nvoid entry(int worker_id) {{\nput(worker_id);\n}}\n"
        );
        let report = analyze(&source, CandidateKind::IndexedWrites);
        let calls = report
            .findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .filter(|a| a.function_name.as_deref() == Some("entry"))
            .collect::<Vec<_>>();
        assert!(!calls.is_empty(), "{report:#?}");
        assert!(
            calls.iter().all(|a| a.access_kind.as_deref() == Some(kind)),
            "{calls:#?}"
        );
    }
}

#[test]
fn cpp_contiguous_field_updates_need_their_own_concurrency_evidence() {
    for (ty, expected) in [("unsigned", false), ("std::atomic<unsigned>", true)] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("state.hpp"), format!("struct State {{\n{ty} worker_state[4];\n{ty} worker_count[2];\nvoid step(int i) {{ worker_state[i]++; worker_count[i%2]++; }}\n}};\n")).unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(!report.findings.is_empty(), expected, "{report:#?}");
        options.cpp_include_speculative = true;
        assert!(
            !analyze_cpp_path_with_options(root.path(), &options)
                .findings
                .is_empty()
        );
    }
}

#[test]
fn cpp_adjacent_objects_require_non_initialization_slot_writes() {
    for (operation, expected) in [
        ("consume(cells[i].value.load());", false),
        ("cells[i].value.fetch_add(1);", true),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("objects.cpp"), format!("struct Cell {{\nstd::atomic<int> value;\nCell() {{ value.store(0); }}\n}};\nCell cells[8];\nvoid run() {{\n#pragma omp parallel for\nfor (int i=0; i<8; ++i) {{ {operation} }}\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[
                RuleId::ContiguousElements,
                RuleId::IndependentAllocations,
            ]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{operation}\n{:#?}",
            report.findings
        );
    }
}

#[test]
fn cpp_container_read_only_access_is_not_container_elements_conflict() {
    let report = analyze(
        r#"
        #include <vector>
        struct State { std::vector<int> values; int get(int i) const { return values[i]; } };
        "#,
        CandidateKind::ContainerElements,
    );
    assert!(
        report.findings.is_empty(),
        "read-only container payload must not report: {report:#?}"
    );
}

#[test]
fn cpp_private_inline_array_stores_before_handoff_are_not_shared_writes() {
    let source = "void run() {\n#pragma omp parallel\n{\nstd::array<int, 4> local;\nlocal[0] = 1;\nlocal[1] = 2;\npublish(local.data());\nlocal[2] = 3;\n}\n}\n";
    let report = analyze(source, CandidateKind::IndexedWrites);
    assert!(
        !report.findings.is_empty(),
        "post-publication accesses must remain eligible"
    );
    assert!(
        report
            .findings
            .iter()
            .all(|f| f.access_evidence.iter().all(|a| !matches!(a.line, 5 | 6))),
        "{:#?}",
        report.findings
    );
}

#[test]
fn cpp_array_publication_on_loop_backedge_is_not_a_private_prefix() {
    for body in [
        "for (int n=0; n<10; ++n) {\nlocal[worker_id]++;\npublish(local);\n}",
        "again:\nlocal[worker_id]++;\npublish(local);\nif (repeat()) goto again;",
    ] {
        let source = format!("void run(int worker_id) {{\nint local[8] = {{}};\n{body}\n}}\n");
        let report = analyze(&source, CandidateKind::IndexedWrites);
        assert!(!report.findings.is_empty(), "{source}\n{report:#?}");
    }
}

#[test]
fn cpp_static_function_array_parameters_are_not_static_storage() {
    for declaration in [
        "static void transform(unsigned state[4], const unsigned block[16]);",
        "struct Digest { static void transform(unsigned state[4], const unsigned block[16]); };",
    ] {
        let source = format!(
            "{declaration}\nvoid update(unsigned *state, int worker_id) {{\nstate[worker_id]++;\n}}\n"
        );
        assert!(
            analyze(&source, CandidateKind::StaticData)
                .findings
                .is_empty()
        );
    }
    // A same-named real global must survive prototype rejection and deduplication.
    let source = "static void transform(unsigned counters[4], unsigned block[16]);\nstatic int counters[8];\nvoid update(int worker_id) {\ncounters[worker_id]++;\n}\n";
    assert!(
        !analyze(source, CandidateKind::StaticData)
            .findings
            .is_empty()
    );
}

#[test]
fn cpp_static_scalar_arithmetic_is_not_a_mutable_partition_accessor() {
    let source = "static int state[16];\nunsigned long next(unsigned long state) {\nreturn 7 * state + 3;\n}\n";
    assert!(
        analyze(source, CandidateKind::StaticData)
            .findings
            .is_empty()
    );
    let source =
        "static int counters[16];\nint *slot(int worker_id) {\nreturn counters + worker_id;\n}\n";
    assert!(
        !analyze(source, CandidateKind::StaticData)
            .findings
            .is_empty()
    );
}

#[test]
fn cpp_bound_storage_is_not_projected_to_an_unrelated_same_named_field() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("unrelated.hpp"),
        "struct Other { int values[16]; };\n",
    )
    .unwrap();
    fs::write(root.path().join("caller.cpp"), "int values[16];\nvoid put(int *p, int q) { p[q]++; }\nvoid worker() { put(values, omp_get_thread_num()); }\n").unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    options.cpp_include_speculative = true;
    let report = analyze_cpp_path_with_options(root.path(), &options);
    let bound = report
        .findings
        .iter()
        .filter(|f| {
            f.concurrency_evidence
                .iter()
                .any(|s| s.contains("过程间绑定"))
        })
        .collect::<Vec<_>>();
    assert!(!bound.is_empty());
    assert!(
        bound
            .iter()
            .all(|f| f.file.ends_with("caller.cpp") && f.struct_name.is_none()),
        "{bound:#?}"
    );
}

#[test]
fn cpp_bound_pointer_calls_respect_cross_file_linkage_and_prototypes() {
    for (definition, prototype, expected) in [
        (
            "void put(int *p, int q) { p[q]++; }",
            "void put(int *data, int n);",
            true,
        ),
        (
            "static void put(int *p, int q) { p[q]++; }",
            "void put(int *data, int n);",
            false,
        ),
        (
            "void put(int *p, int q) { p[q]++; }",
            "void put(double *data, int n);",
            false,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("helper.cpp"), definition).unwrap();
        fs::write(root.path().join("caller.cpp"), format!("{prototype}\nint values[16];\nvoid worker() {{ put(values, omp_get_thread_num()); }}\n")).unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
        options.cpp_include_speculative = true;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(
            report.findings.iter().any(|f| f
                .concurrency_evidence
                .iter()
                .any(|s| s.contains("过程间绑定"))),
            expected,
            "{definition}\n{prototype}\n{:#?}",
            report.findings
        );
    }
}

#[test]
fn cpp_indexed_storage_aliases_are_callable_scoped_and_killed_by_assignment() {
    let prefix = "std::vector<int> backing;\nvoid setup() {\nint *p = backing.data();\n}\n";
    for body in [
        "void worker(int *p, int worker_id) {\np[worker_id]++;\n}\n",
        "void worker(int worker_id, int *other) {\nint *p = backing.data();\np = other;\np[worker_id]++;\n}\n",
        "void worker(int worker_id, int *other, bool b) {\nint *p = backing.data();\nif (b) { p = other; }\np[worker_id]++;\n}\n",
    ] {
        let report = analyze(&format!("{prefix}{body}"), CandidateKind::IndexedWrites);
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|s| s == "backing")),
            "{body}\n{:#?}",
            report.findings
        );
    }
    let report = analyze(
        "std::vector<int> backing;\nvoid worker(int worker_id) {\nint *p = backing.data();\np[worker_id]++;\n}\n",
        CandidateKind::IndexedWrites,
    );
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.field_list.iter().any(|s| s == "backing")),
        "{:#?}",
        report.findings
    );
}

#[test]
fn cpp_straight_line_member_assignment_binds_storage_without_global_aliases() {
    let report = analyze(
        "struct Owner { int *items; };\nvoid worker(Owner *owner, int worker_id) {\nint *alias;\nalias = owner->items;\nalias[worker_id]++;\n}\n",
        CandidateKind::IndexedWrites,
    );
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.field_list.iter().any(|s| s == "items")),
        "{:#?}",
        report.findings
    );
    let report = analyze(
        "struct Owner { int *items; };\nvoid worker(Owner *owner, int *alias, int worker_id, bool b) {\nif (b) alias = owner->items;\nalias[worker_id]++;\n}\n",
        CandidateKind::IndexedWrites,
    );
    assert!(
        !report
            .findings
            .iter()
            .any(|f| f.field_list.iter().any(|s| s == "items")),
        "{:#?}",
        report.findings
    );
}

#[test]
fn cpp_bound_pointer_mutation_uses_actual_storage_and_runtime_index() {
    for call in [
        "put(values, omp_get_thread_num());",
        "forward(omp_get_thread_num(), values);",
        "const int n = omp_get_thread_num();\nput(values, n);",
    ] {
        let source = format!(
            "int values[16];\nvoid put(int *p, int q) {{ p[q]++; }}\nvoid forward(int a, int *b) {{ put(b, a); }}\nvoid worker() {{\n{call}\n}}\n"
        );
        let report = analyze(&source, CandidateKind::IndexedWrites);
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.iter().any(|s| s == "values")
                    && f.concurrency_evidence
                        .iter()
                        .any(|s| s.contains("过程间绑定"))),
            "{:#?}",
            report.findings
        );
    }
}

#[test]
fn cpp_bound_pointer_mutation_rejects_unresolved_or_private_bindings() {
    for source in [
        "int values[16];\nvoid put(int *p, int q) { p[q]++; }\nvoid worker() { put(values, 0); }\n",
        "int values[16];\nvoid put(int *p, int q) { p[q]++; }\nvoid worker() {\nint n = omp_get_thread_num();\nn = 0;\nput(values, n);\n}\n",
        "int values[16];\nvoid put(int *p, int q) { p[q]++; }\nvoid worker() { put(values, remap(omp_get_thread_num())); }\n",
        "void put(int *p, int q) { p[q]++; }\nvoid worker() { int values[16]; put(values, omp_get_thread_num()); }\n",
        "int values[16];\nvoid put(int *p, int q) { p[q]++; }\nvoid put(float *p, int q) { p[q]++; }\nvoid worker() { put(values, omp_get_thread_num()); }\n",
        "int values[16];\nvoid put(int *p, int q) { p = other; p[q]++; }\nvoid worker() { put(values, omp_get_thread_num()); }\n",
        "extern int *values;\nvoid unrelated(int values[]);\nvoid put(int *p, int q) { p[q]++; }\nvoid worker() { put(values, omp_get_thread_num()); }\n",
    ] {
        let report = analyze(source, CandidateKind::IndexedWrites);
        assert!(
            !report.findings.iter().any(|f| f
                .concurrency_evidence
                .iter()
                .any(|s| s.contains("过程间绑定"))),
            "{source}\n{:#?}",
            report.findings
        );
    }
}

#[test]
fn cpp_cross_file_indexed_access_does_not_bind_a_function_local_array() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("local.cpp"),
        "void unrelated() {\nstatic int values[16];\n}\n",
    )
    .unwrap();
    fs::write(
        root.path().join("worker.cpp"),
        "void update(int *values) {\nvalues[omp_get_thread_num()]++;\n}\n",
    )
    .unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    options.cpp_include_speculative = true;
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert!(!report.findings.is_empty());
    assert!(
        report
            .findings
            .iter()
            .all(|f| !f.file.ends_with("local.cpp")),
        "{:#?}",
        report.findings
    );
}

#[test]
fn cpp_indexed_cpu_risk_excludes_explicit_device_only_functions() {
    for qualifier in ["__global__", "__device__"] {
        let source = format!(
            "int values[16];\n{qualifier} void update(int worker_id) {{\nvalues[worker_id]++;\n}}\n"
        );
        assert!(
            analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{source}"
        );
    }
    for qualifier in ["", "__host__ __device__"] {
        let source = format!(
            "int values[16];\n{qualifier} void update(int worker_id) {{\nvalues[worker_id]++;\n}}\n"
        );
        assert!(
            !analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{source}"
        );
    }
}

#[test]
fn cpp_gpu_lane_identity_is_not_cpu_worker_identity() {
    let gpu = "int values[16];\nvoid update() {\nvalues[threadIdx.x]++;\n}\n";
    assert!(
        analyze(gpu, CandidateKind::IndexedWrites)
            .findings
            .is_empty()
    );
    let cpu = "int values[16];\nvoid update() {\nvalues[omp_get_thread_num()]++;\n}\n";
    assert!(
        !analyze(cpu, CandidateKind::IndexedWrites)
            .findings
            .is_empty()
    );
}

#[test]
fn cpp_default_pair_report_keeps_actual_witnesses_after_api_prefix() {
    let root = tempdir().unwrap();
    let owners = (0..24)
        .map(|i| format!("std::shared_ptr<State> owner_{i};\n"))
        .collect::<String>();
    fs::write(root.path().join("candidate.hpp"), format!("struct State {{\nstd::atomic<size_t> left;\nstd::atomic<size_t> right;\n}};\n{owners}\nvoid write_left(State* s) {{ s->left.fetch_add(1); }}\nvoid write_right(State* s) {{ s->right.fetch_add(1); }}\n")).unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(!report.findings.is_empty());
    for finding in &report.findings {
        for (field, function) in [("left", "write_left"), ("right", "write_right")] {
            assert!(
                finding
                    .access_evidence
                    .iter()
                    .any(|a| a.field_name.as_deref() == Some(field)
                        && a.function_name.as_deref() == Some(function)
                        && a.access_kind.as_deref() == Some("read_modify_write")),
                "{:#?}",
                finding.access_evidence
            );
        }
    }
}

#[test]
fn cpp_same_spelled_file_local_functions_keep_distinct_access_roles() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("state.hpp"),
        "struct State {\nstd::atomic<int> left;\nstd::atomic<int> right;\n};\n",
    )
    .unwrap();
    fs::write(
        root.path().join("a.cpp"),
        "static void work(State* s) { s->left.fetch_add(1); }\n",
    )
    .unwrap();
    fs::write(
        root.path().join("b.cpp"),
        "static void work(State* s) { s->right.fetch_add(1); }\n",
    )
    .unwrap();
    assert!(
        !analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields])
        )
        .findings
        .is_empty()
    );
}

#[test]
fn cpp_annotation_macros_do_not_merge_method_access_roles() {
    let root = tempdir().unwrap();
    let path = root.path().join("candidate.hpp");
    for annotation in ["QUALIFIER", "ANOTHER_ANNOTATION"] {
        fs::write(&path, format!("struct State {{\nstd::atomic<int> left;\nstd::atomic<int> right;\ninline void first() {annotation}\n{{ left.fetch_add(1); }}\ninline void second() {annotation}\n{{ right.fetch_add(1); }}\n}};\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert!(!report.findings.is_empty(), "{annotation}");
        let names = report
            .findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .filter_map(|a| a.function_name.as_deref())
            .collect::<Vec<_>>();
        assert!(
            names.contains(&"first") && names.contains(&"second"),
            "{names:?}"
        );
        assert!(!names.contains(&annotation));
    }
}

#[test]
fn cpp_same_object_requires_actual_distinct_access_roles_not_public_atomic_names() {
    let root = tempdir().unwrap();
    let path = root.path().join("candidate.hpp");
    for (left, right) in [("left", "right"), ("apple", "orange")] {
        let prefix =
            format!("struct State {{\nstd::atomic<int> {left};\nstd::atomic<int> {right};\n}};\n");
        for (body, expected) in [
            (
                format!(
                    "void update(State* s) {{ s->{left}.fetch_add(1); s->{right}.load(); }}\nvoid peer(State* s) {{ s->{right}.fetch_add(1); s->{left}.load(); }}"
                ),
                true,
            ),
            (
                format!(
                    "void update(State* s) {{ s->{left}.fetch_add(1); s->{right}.fetch_add(1); }}"
                ),
                false,
            ),
            (
                format!(
                    "void update(State* s) {{ s->{left}.fetch_add(1); }}\nvoid peer(State* s) {{ s->{right}.fetch_add(1); }}"
                ),
                true,
            ),
            (
                format!(
                    "void update(State* s) {{ s->{left}.fetch_add(1); s->{right}.fetch_add(1); }}\nvoid peer(State* s) {{ s->{right}.fetch_add(1); }}"
                ),
                true,
            ),
        ] {
            fs::write(&path, format!("{prefix}{body}\n")).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "{body}: {:#?}",
                report.findings
            );
            options.cpp_include_speculative = true;
            assert!(
                !analyze_cpp_path_with_options(root.path(), &options)
                    .findings
                    .is_empty(),
                "{body}"
            );
        }
    }
}

#[test]
fn cpp_parallel_method_context_requires_unambiguous_shared_receiver() {
    let root = tempdir().unwrap();
    let path = root.path().join("candidate.cpp");
    let prefix = "struct Entry {\nint counter;\nvoid update() {\nfor(int i=0; i<100; ++i) counter++;\n}\n};\nEntry entries[32];\n";
    for (declarations, call, expected) in [
        (
            "using Alias = Entry;\nstruct Owner { static inline Alias shared;\nstatic void start() { std::async([] -> void { shared.update(); }); } };",
            "Owner::start();",
            true,
        ),
        (
            "static Entry shared;",
            "sequential([] -> void { shared.update(); });",
            false,
        ),
        (
            "using Alias = Entry;\nstatic Alias shared;",
            "std::async([] { shared.update(); });",
            true,
        ),
        (
            "static Entry shared;",
            "sequential([] { shared.update(); });",
            false,
        ),
        (
            "static Entry shared;",
            "std::async([] { Entry shared; shared.update(); });",
            false,
        ),
        (
            "static Entry shared;",
            "std::async([] { for(auto& shared : others) shared.update(); });",
            false,
        ),
        (
            "thread_local Entry shared;",
            "std::async([] { shared.update(); });",
            false,
        ),
        (
            "Entry* shared;",
            "std::async([] { shared->update(); });",
            false,
        ),
        (
            "struct Other { void update() {} };\nstatic Other shared;",
            "std::async([] { shared.update(); });",
            false,
        ),
        (
            "using Alias = Entry;\nusing Alias = Other;\nstatic Alias shared;",
            "std::async([] { shared.update(); });",
            false,
        ),
    ] {
        fs::write(
            &path,
            format!("{prefix}{declarations}\nvoid launch() {{\n{call}\n}}\n"),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[
                RuleId::ContiguousElements,
                RuleId::IndependentAllocations,
            ]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{declarations} / {call}: {:#?}",
            report.findings
        );
        if expected {
            assert!(
                report
                    .findings
                    .iter()
                    .any(|finding| finding.access_evidence.iter().any(|access| access
                        .in_concurrent_context
                        && access.propagation_depth == 1
                        && access
                            .call_path
                            .last()
                            .is_some_and(|call| call == "shared.update")))
            );
        }
    }
    fs::write(
        &path,
        format!(
            "{}static Entry shared;\nvoid launch() {{\nstd::async([] {{ shared.update(); }});\n}}",
            prefix.replace("void update()", "void update(int n) {}\nvoid update()")
        ),
    )
    .unwrap();
    assert!(
        analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[
                RuleId::ContiguousElements,
                RuleId::IndependentAllocations
            ])
        )
        .findings
        .is_empty()
    );
    for body in [
        "counter++;",
        "auto unused = [this] { for(int i=0; i<100; ++i) counter++; };",
    ] {
        fs::write(&path, format!("{}static Entry shared;\nvoid launch() {{\nstd::async([] {{ shared.update(); }});\n}}", prefix.replace("for(int i=0; i<100; ++i) counter++;", body))).unwrap();
        assert!(
            analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions::with_rules(&[
                    RuleId::ContiguousElements,
                    RuleId::IndependentAllocations
                ])
            )
            .findings
            .is_empty(),
            "{body}"
        );
    }
}

#[test]
fn indexed_writes_dynamic_mutex_slots_do_not_require_worker_named_indices() {
    for (index, expected) in [("selected", true), ("0", false)] {
        let source = format!(
            "pthread_mutex_t locks[32];\nvoid acquire(int key) {{\nint selected = lookup(key);\npthread_mutex_lock(&locks[{index}]);\n}}\n"
        );
        let report = analyze(&source, CandidateKind::IndexedWrites);
        assert_eq!(!report.findings.is_empty(), expected, "{index}");
        assert!(
            report
                .findings
                .iter()
                .all(|f| f.access_evidence.iter().all(|e| !e.in_concurrent_context))
        );
    }
    let private = "void acquire(int key) {\npthread_mutex_t locks[32];\nint selected = lookup(key);\npthread_mutex_lock(&locks[selected]);\n}\n";
    assert!(
        analyze(private, CandidateKind::IndexedWrites)
            .findings
            .is_empty()
    );
}

#[test]
fn indexed_writes_same_named_local_indices_do_not_cross_callable_boundaries() {
    for bodies in [
        "void first() {\nint selected = omp_get_thread_num();\nvalues[selected]++;\n}\nvoid second() {\nint selected = 0;\nvalues[selected]++;\n}",
        "void second() {\nint selected = 0;\nvalues[selected]++;\n}\nvoid first() {\nint selected = omp_get_thread_num();\nvalues[selected]++;\n}",
    ] {
        let report = analyze(
            &format!("int values[32];\n{bodies}"),
            CandidateKind::IndexedWrites,
        );
        assert!(!report.findings.is_empty());
        assert!(
            report.findings.iter().all(|f| f
                .access_evidence
                .iter()
                .all(|e| e.function_name.as_deref() != Some("second"))),
            "{:#?}",
            report.findings
        );
    }
}

#[test]
fn indexed_writes_data_indices_are_not_runtime_thread_identities() {
    for assignment in [
        "int selected = descriptor->tuple_index;",
        "int column_index = 2;\nint selected = column_index;",
    ] {
        let source = format!(
            "struct Descriptor {{ int tuple_index; }};\nint values[32];\nvoid fill(Descriptor* descriptor) {{\n{assignment}\nvalues[selected] = 1;\n}}\n"
        );
        assert!(
            analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{assignment}"
        );
    }
    let source = "struct Descriptor { int worker_id; };\nint values[32];\nvoid fill(Descriptor* descriptor) {\nint selected = descriptor->worker_id;\nvalues[selected] = 1;\n}\n";
    let report = analyze(source, CandidateKind::IndexedWrites);
    assert!(!report.findings.is_empty());
    assert!(
        report
            .findings
            .iter()
            .all(|f| f.access_evidence.iter().all(|e| !e.in_concurrent_context))
    );
}

#[test]
fn object_instances_sequential_bulk_writes_need_more_than_loop_hotness() {
    let root = tempdir().unwrap();
    let path = root.path().join("candidate.hpp");
    let source = "struct Entry {\nint counter;\nvoid update() { counter++; }\n};\nEntry entries[32];\nvoid fill() {\nfor(int i=0; i<32; ++i) {\nentries[i].counter++;\n}\n}\n";
    fs::write(&path, source).unwrap();
    let mut options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    assert!(
        analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
    options.cpp_include_speculative = true;
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
    fs::write(
        &path,
        source.replace("for(int", "#pragma omp parallel for\nfor(int"),
    )
    .unwrap();
    options.cpp_include_speculative = false;
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
}

#[test]
fn kernel_thread_callback_supplies_candidate_linked_concurrency() {
    let root = tempdir().unwrap();
    let path = root.path().join("candidate.c");
    let ordinary_accesses = (0..20)
        .map(|i| format!("void inspect_{i}(struct State* state) {{ consume(state->pending); }}\n"))
        .collect::<String>();
    for (launcher, expected) in [("kthread_run", true), ("inspect_callback", false)] {
        fs::write(&path, format!("struct State {{\nvoid* pending;\nvoid* running;\nspinlock_t lock;\n}};\n{ordinary_accesses}\nint consume_queue(void* data) {{\nstruct State* state = (struct State*)data;\nstate->running = state->pending;\nstate->pending = 0;\nreturn 0;\n}}\nvoid submit(struct State* state, void* value) {{\nstate->pending = value;\n}}\nvoid start(struct State* state) {{\n{launcher}(consume_queue, state, \"worker\");\n}}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{launcher}: {:#?}",
            report.findings
        );
        if expected {
            assert!(report.findings.iter().any(|f| {
                f.access_evidence.iter().any(|e| {
                    e.in_concurrent_context && e.function_name.as_deref() == Some("consume_queue")
                })
            }));
        }
    }
}

#[test]
fn unrelated_mutex_does_not_establish_parallel_access_to_plain_field_pair() {
    let root = tempdir().unwrap();
    let path = root.path().join("candidate.hpp");
    fs::write(&path, "struct State {\nvoid* left;\nstd::vector<int> right;\nstd::mutex unrelated;\nvoid set_left() { left = nullptr; }\nvoid set_right() { right.clear(); }\nvoid inspect() { consume(left); }\n};\nstd::shared_ptr<State> owner;\n").unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    assert!(
        analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
    options.cpp_include_speculative = true;
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
    fs::write(&path, "struct State {\nstd::atomic<int> left;\nstd::vector<int> right;\nvoid set_left() { left++; }\nvoid set_right() { right.clear(); }\nvoid inspect() { consume(left.load()); }\n};\nstd::shared_ptr<State> owner;\n").unwrap();
    options.cpp_include_speculative = false;
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
}

#[test]
fn indexed_writes_sequential_callbacks_cannot_borrow_nested_parallelism() {
    for call in ["tbb::this_task_arena::isolate", "invoke"] {
        let source = format!(
            "float* values;\nvoid update() {{\n{call}([&] {{\nfor(int i=0; i<16; ++i) {{\nvalues[i] = 1;\n}}\nstd::thread unrelated([] {{ work(); }});\n}});\n}}"
        );
        assert!(
            analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{call}"
        );
    }
    for call in [
        "tbb::parallel_for(0, 16,",
        "std::for_each(std::execution::par, begin, end,",
    ] {
        let source = format!(
            "float* values;\nvoid update() {{\n{call} [&](int i) {{\nvalues[i] = 1;\n}});\n}}"
        );
        assert!(
            !analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{call}"
        );
    }
}

#[test]
fn indexed_writes_mutator_summary_does_not_export_private_or_formal_storage_names() {
    for target in ["int scratch[32];", ""] {
        let params = if target.is_empty() {
            "int* scratch, unsigned worker"
        } else {
            "unsigned worker"
        };
        let call = if target.is_empty() {
            "helper(shared_buffer, worker);"
        } else {
            "helper(worker);"
        };
        let source = format!(
            "int* shared_buffer;\nvoid helper({params}) {{\n{target}\nscratch[worker] = 1;\n}}\nvoid run(unsigned worker) {{\n{call}\n}}"
        );
        assert!(
            !analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .iter()
                .any(|f| f.symbol.as_deref() == Some("run")),
            "{target}"
        );
    }
}

#[test]
fn indexed_writes_private_stack_arrays_are_not_shared_slots() {
    let private = "void update() {\n#pragma omp parallel\n{\nint scratch[16];\nfor(int i=0; i<16; ++i) {\nscratch[i] = i;\n}\n}\n}";
    assert!(
        analyze(private, CandidateKind::IndexedWrites)
            .findings
            .is_empty()
    );
    let shared = "void update() {\nint scratch[16];\n#pragma omp parallel for\nfor(int i=0; i<16; ++i) {\nscratch[i] = i;\n}\n}";
    assert!(
        !analyze(shared, CandidateKind::IndexedWrites)
            .findings
            .is_empty()
    );
    for declaration in [
        "static int scratch[16];",
        "int* scratch = shared_buffer;",
        "int scratch[16];\npublish(scratch);",
    ] {
        let source = format!(
            "void update() {{\n#pragma omp parallel\n{{\n{declaration}\nfor(int i=0; i<16; ++i) {{\nscratch[i] = i;\n}}\n}}\n}}"
        );
        assert!(
            !analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{declaration}"
        );
    }
}

#[test]
fn indexed_writes_simd_is_not_thread_parallelism() {
    for directive in ["simd", "declare simd", "atomic", "barrier"] {
        let source = format!(
            "void update(float* output) {{\n#pragma omp {directive}\nfor(int i = 0; i < 16; ++i) {{\noutput[i] += 1;\n}}\n}}"
        );
        assert!(
            analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{directive}"
        );
    }
    for directive in ["parallel for", "parallel for simd", "for simd"] {
        let source = format!(
            "void update(float* output) {{\n#pragma omp {directive}\nfor(int i = 0; i < 16; ++i) {{\noutput[i] += 1;\n}}\n}}"
        );
        assert!(
            !analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{directive}"
        );
    }
    let nested = "void update(float* output) {\n#pragma omp parallel\n{\nint worker = omp_get_thread_num();\n#pragma omp simd\nfor(int i = 0; i < 16; ++i) {\noutput[worker + i] += 1;\n}\n}\n}";
    assert!(
        !analyze(nested, CandidateKind::IndexedWrites)
            .findings
            .is_empty()
    );
}

#[test]
fn container_clear_does_not_supply_atomic_evidence_for_default_reports() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("candidate.hpp"),
        r#"
        class Connection {
            void* handle;
            void* headers;
            std::vector<int> cache;
        public:
            void reset() { cache.clear(); handle = nullptr; }
            void replace() { headers = build(); }
            void inspect() { consume(handle); }
        };
        std::shared_ptr<Connection> owner;
    "#,
    )
    .unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
    options.cpp_include_speculative = true;
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
}

#[test]
fn indexed_writes_pointer_edges_do_not_write_the_contiguous_pointer_slot() {
    for expression in [
        "nodes[worker_id].next->counter++;",
        "auto& ref = *pointers[worker_id];\n ref.counter++;",
        "auto& ref = pointers[worker_id]->counter;\n ref++;",
        "auto& ref = nodes[worker_id];\n ref.next->counter++;",
    ] {
        let source = format!(
            "struct Node {{ int counter; Node* next; }};\nNode nodes[32];\nNode* pointers[32];\nvoid update(unsigned worker_id) {{\n{expression}\n}}"
        );
        assert!(
            analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{expression}"
        );
    }
    let report = analyze(
        "struct Node { int counter; };\nNode nodes[32];\nvoid update(unsigned worker_id) {\n auto* ptr = &nodes[worker_id];\n ptr->counter++;\n}",
        CandidateKind::IndexedWrites,
    );
    assert!(!report.findings.is_empty());
}

#[test]
fn indexed_writes_retains_pointer_to_inline_array_rows_but_not_pointer_tables() {
    for (declaration, expected) in [
        (
            "double(*const rows)[width] = (double(*)[width])malloc(32 * width * sizeof(double));",
            true,
        ),
        (
            "double **rows = (double**)malloc(32 * sizeof(double*));",
            false,
        ),
        ("double *rows[32];", false),
    ] {
        let source = format!(
            "void update(unsigned width) {{\n{declaration}\n#pragma omp parallel\n{{\n unsigned worker_id = omp_get_thread_num();\n double *const row = rows[worker_id];\n memset(row, 0, width * sizeof(double));\n}}\n}}"
        );
        let report = analyze(&source, CandidateKind::IndexedWrites);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{declaration}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn object_instances_atomic_member_alone_does_not_establish_adjacent_instances() {
    let root = tempdir().unwrap();
    let path = root.path().join("candidate.hpp");
    let source = "struct QueueState {\n std::atomic<bool> counter;\n std::atomic<bool> state;\n void update() { counter.store(true); }\n void change() { state.store(true); }\n};\n";
    fs::write(&path, source).unwrap();
    let mut options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]);
    assert!(
        analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
    options.cpp_include_speculative = true;
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
    options.cpp_include_speculative = false;
    fs::write(&path, format!("{source}\nQueueState counters[16];")).unwrap();
    // An array establishes adjacency, not recurrent invalidating writes.
    assert!(
        analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
    fs::write(&path, format!("{source}\nQueueState counters[16];\nvoid run() {{\n#pragma omp parallel for\nfor(int i=0;i<16;++i) counters[i].counter.store(true);\n}}\n")).unwrap();
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
    fs::write(&path, "struct SpinLock {\n std::atomic<bool> busy;\n void lock() { while (busy.exchange(true)) {} }\n void unlock() { busy.store(false); }\n};").unwrap();
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
}

#[test]
fn indexed_writes_reads_and_copies_do_not_create_partition_alias_writes() {
    for body in [
        "for (int i = 0; i < values[worker_id]; i++) { consume(i); }",
        "auto local = values[worker_id];\n local++;",
        "auto &local = lookup(values[worker_id]);\n local++;",
        "int result = consume(values[worker_id]);\n result++;",
        "consume(values[worker_id]); unrelated++;",
        "consume(values[worker_id], unrelated.fetch_add(1));",
        "auto *local = &values[worker_id];\n local++;",
        "auto *local = &values[worker_id];\n local = other;\n local[0]++;",
        "auto &local = values[worker_id];\n consume(local); unrelated++;",
    ] {
        let source = format!(
            "long values[32];\nlong* other;\nstd::atomic<long> unrelated;\nvoid update(unsigned worker_id) {{\n{body}\n}}\n"
        );
        let report = analyze(&source, CandidateKind::IndexedWrites);
        assert!(report.findings.is_empty(), "{body}: {:#?}", report.findings);
    }
    for body in [
        "auto &local = values[worker_id];\n local++;",
        "auto *local = &values[worker_id];\n local[0]++;",
        "auto *local = &values[worker_id];\n *local = 1;",
        "values[worker_id]++;",
    ] {
        let source = format!("long values[32];\nvoid update(unsigned worker_id) {{\n{body}\n}}\n");
        assert!(
            !analyze(&source, CandidateKind::IndexedWrites)
                .findings
                .is_empty(),
            "{body}"
        );
    }
}

#[test]
fn cpp_default_report_requires_evidence_beyond_generic_public_mutability() {
    let root = tempdir().unwrap();
    let path = root.path().join("candidate.cpp");
    fs::write(&path, "struct Counters {\n int counter;\n int state;\n void left() { counter++; }\n void right() { state++; }\n int first() const { return counter; }\n int second() const { return state; }\n};\nstd::shared_ptr<Counters> published;").unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let actionable = analyze_cpp_path_with_options(root.path(), &options);
    assert!(actionable.findings.is_empty());
    assert!(actionable.summary.cpp_speculative_candidates > 0);
    options.cpp_include_speculative = true;
    let broad = analyze_cpp_path_with_options(root.path(), &options);
    assert!(!broad.findings.is_empty());
    assert_eq!(broad.summary.cpp_speculative_candidates, 0);
    assert_eq!(
        actionable.summary.cpp_speculative_candidates,
        broad.findings.len()
    );
    fs::write(&path, "struct Counters {\n std::atomic<unsigned> counter;\n std::atomic<unsigned> state;\n void left() { counter++; }\n void right() { state++; }\n};\nstd::shared_ptr<Counters> published;").unwrap();
    options.cpp_include_speculative = false;
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
    options.max_findings = Some(0);
    let capped = analyze_cpp_path_with_options(root.path(), &options);
    assert!(capped.findings.is_empty());
    assert_eq!(capped.summary.cpp_speculative_candidates, 0);
    assert!(capped.summary.suppressed_candidates > 0);
    assert_eq!(
        capped.summary.candidate_findings,
        capped.summary.suppressed_candidates
    );
}

#[test]
fn mixed_fields_serialized_evidence_does_not_invent_independent_private_field_paths() {
    for methods in [
        "void update() { handle = open(); headers = build(); }",
        "void reset() { handle = open(); } void replace() { handle = open(); headers = build(); }",
    ] {
        let source = format!(
            "class Connection {{ void* handle; void* headers; public: {methods} }};\nstd::shared_ptr<Connection> shared;"
        );
        let report = analyze(&source, CandidateKind::MixedFields);
        assert!(report.findings.is_empty(), "{:#?}", report.findings);
    }
    let report = analyze(
        "class Connection { void* handle; void* headers; public:\nvoid inspect() { consume(handle); }\nvoid replace() { consume(handle); headers = build(); }\n};\nstd::shared_ptr<Connection> shared;",
        CandidateKind::MixedFields,
    );
    assert!(
        !report.findings.is_empty(),
        "separate write/read paths must survive"
    );
}

#[test]
fn indexed_writes_mutator_summary_does_not_cross_same_named_definitions() {
    let report = analyze(
        r#"
        struct Counters {
            long values[32];
            void add(unsigned index, long delta) {
                __atomic_fetch_add(&values[index], delta, __ATOMIC_RELAXED);
            }
        };
        struct Log {
            void add(unsigned index, long delta) { consume(index, delta); }
        };
        void run(Log *log, unsigned worker_id) {
            log->add(worker_id, 1);
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        !report
            .findings
            .iter()
            .any(|finding| finding.symbol.as_deref() == Some("run")),
        "unresolved receiver/overload must not inherit another definition: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_mutator_summary_tracks_index_argument_not_value_argument() {
    let report = analyze(
        r#"
        struct Counters {
            long values[32];
            void add(unsigned index, long delta) {
                __atomic_fetch_add(&values[index], delta, __ATOMIC_RELAXED);
            }
        };
        void same_slot(Counters *counters, unsigned worker_id) {
            counters->add(0, worker_id);
        }
        void separate_slots(Counters *counters, unsigned worker_id) {
            counters->add(worker_id, 1);
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        !report
            .findings
            .iter()
            .any(|finding| finding.symbol.as_deref() == Some("same_slot")),
        "{:#?}",
        report.findings
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.symbol.as_deref() == Some("separate_slots")),
        "{:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_mutator_callee_requires_a_complete_identifier() {
    let report = analyze(
        r#"
        long values[32];
        void set(unsigned index) {
            __atomic_fetch_add(&values[index], 1, __ATOMIC_RELAXED);
        }
        void suffix_only(unsigned worker_id) {
            reset(worker_id);
            sigfillset(worker_id);
        }
        void exact_call(unsigned worker_id) {
            set(worker_id);
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        !report
            .findings
            .iter()
            .flat_map(|finding| &finding.access_evidence)
            .any(|access| access.function_name.as_deref() == Some("suffix_only")),
        "{:#?}",
        report.findings
    );
    assert!(
        report
            .findings
            .iter()
            .flat_map(|finding| &finding.access_evidence)
            .any(|access| access.function_name.as_deref() == Some("exact_call")),
        "{:#?}",
        report.findings
    );
}

#[test]
fn field_group_multiline_constructor_writes_do_not_overlap_shared_readers() {
    let report = analyze(
        r#"
        struct Counters {
            int counter;
            int state;
            Counters(int initial)
              : counter(initial)
            {
                counter = initial;
                state = 1;
            }
            int first() const { return counter; }
            int second() const { return state; }
        };
        std::shared_ptr<Counters> published;
    "#,
        CandidateKind::FieldGroup,
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn field_group_parameters_and_block_locals_shadow_implicit_members() {
    let report = analyze(
        r#"
        struct Counters {
            int counter;
            int state;
            void update(int counter, int state) {
                counter += 1;
                state += 1;
            }
            void local() {
                int counter = 1;
                int state = 2;
                counter++;
                state++;
            }
            int first() const { return counter; }
            int second() const { return state; }
        };
        std::shared_ptr<Counters> published;
    "#,
        CandidateKind::FieldGroup,
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
    let explicit = analyze(
        r#"
        struct Counters {
            int counter;
            int state;
            void first(int counter) { this->counter += counter; }
            void second(int state) { this->state += state; }
        };
        std::shared_ptr<Counters> published;
    "#,
        CandidateKind::FieldGroup,
    );
    assert!(!explicit.findings.is_empty());
}

#[test]
fn mixed_fields_pointee_writes_do_not_mutate_stored_pointer_fields() {
    let report = analyze(
        r#"
        struct Payload { int value; };
        struct Pointers {
            Payload *left;
            Payload *right;
            void first() { left->value++; }
            void second() { right->value++; }
        };
        std::shared_ptr<Pointers> published;
    "#,
        CandidateKind::MixedFields,
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
    let reassignment = analyze(
        r#"
        struct Payload { int value; };
        struct Pointers {
            Payload *left;
            Payload *right;
            void first(Payload *value) { left = value; }
            void second(Payload *value) { right = value; }
        };
        std::shared_ptr<Pointers> published;
    "#,
        CandidateKind::MixedFields,
    );
    assert!(!reassignment.findings.is_empty());
}

#[test]
fn field_group_constructor_cannot_hide_writes_to_another_instance_or_escaped_this() {
    let other_instance = analyze(
        r#"
        struct Counters {
            int counter;
            int state;
            Counters(Counters *other) {
                other->counter++;
                other->state++;
            }
        };
        std::shared_ptr<Counters> published;
    "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        !other_instance.findings.is_empty(),
        "writes to other are not initialization"
    );
    let escaped = analyze(
        r#"
        struct Counters {
            int counter;
            int state;
            Counters() {
                publish(this);
                counter++;
                state++;
            }
        };
        std::shared_ptr<Counters> published;
    "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        !escaped.findings.is_empty(),
        "publication invalidates constructor exclusion"
    );
}

#[test]
fn field_group_read_member_is_not_changed_by_another_statement_on_the_line() {
    let report = analyze(
        r#"
        struct Counters { int counter; int state; };
        void first(Counters *value) {
            int result = value->counter; result++;
        }
        void second(Counters *value) {
            int result = value->state; result++;
        }
    "#,
        CandidateKind::FieldGroup,
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn field_group_evaluated_initializer_rhs_retains_atomic_writes_and_peer_reads() {
    let report = analyze(
        r#"
        struct Counters {
            std::atomic<int> counter;
            int state;
            void update() { auto previous = counter.fetch_add(1); consume(previous); }
            int inspect() const { auto snapshot = state; return snapshot; }
        };
        std::shared_ptr<Counters> published;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(!report.findings.is_empty(), "{:#?}", report.findings);
    assert!(
        report
            .findings
            .iter()
            .flat_map(|finding| &finding.access_evidence)
            .any(|item| {
                item.field_name.as_deref() == Some("counter")
                    && item.access_kind.as_deref() == Some("read_modify_write")
            })
    );
}

#[test]
fn field_group_unevaluated_initializer_operand_does_not_supply_a_write() {
    let report = analyze(
        r#"
        struct Counters {
            int counter;
            int state;
            int inspect() { auto size = sizeof(counter++); return state + size; }
        };
        std::shared_ptr<Counters> published;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn field_group_same_line_publication_preserves_the_later_runtime_write() {
    for separator in [" ", "\n"] {
        let source = format!(
            "struct Counters {{ int hits; int misses; }};\n\
             Counters *published;\nstd::shared_ptr<Counters> handle;\n\
             void create() {{\n\
               Counters* value = (Counters*)calloc(1, sizeof(Counters));\n\
               value->hits = 1;{separator}published = value;{separator}value->hits = 2;\n\
             }}\n\
             int first(Counters* value) {{ return value->hits; }}\n\
             int second(Counters* value) {{ return value->misses; }}\n"
        );
        let report = analyze(&source, CandidateKind::FieldGroup);
        assert!(!report.findings.is_empty(), "{separator:?}: {report:#?}");
    }
}

#[test]
fn field_group_constructor_member_publication_and_implicit_lambda_capture_preserve_risk() {
    for publish in [
        "publish();",
        "this->publish();",
        "std::thread([=] { counter++; }).detach();",
    ] {
        let source = format!(
            r#"
            struct Counters {{
                int counter;
                int state;
                Counters() {{
                    {publish}
                    counter++;
                    state++;
                }}
            private:
                void publish() {{ register_owner(this); }}
            }};
            std::shared_ptr<Counters> published;
        "#
        );
        let report = analyze(&source, CandidateKind::FieldGroup);
        assert!(
            !report.findings.is_empty(),
            "publication {publish} must invalidate initialization exclusion"
        );
    }
}

#[test]
fn writer_neighbor_requires_memory_access_to_a_real_peer_instead_of_address_taking() {
    let no_peer = analyze(
        r#"
        struct State {
            int payload;
            std::atomic<int> counter;
            void update() { counter.fetch_add(1); }
            void register_address() { register_external(&payload); }
        };
        std::shared_ptr<State> shared;
    "#,
        CandidateKind::WriterNeighbor,
    );
    assert!(
        no_peer.findings.is_empty(),
        "taking an address is not a peer load: {:#?}",
        no_peer.findings
    );
    let real_peer = analyze(
        r#"
        struct State {
            int payload;
            std::atomic<int> counter;
            void update() { counter.fetch_add(1); }
            int read() { return payload; }
        };
        std::shared_ptr<State> shared;
    "#,
        CandidateKind::WriterNeighbor,
    );
    assert!(
        !real_peer.findings.is_empty(),
        "a real write/read pair must remain"
    );
    assert_eq!(real_peer.findings[0].field_list.len(), 2);
}

#[test]
fn bounded_report_prioritizes_source_backed_api_partition_without_claiming_thread_spawn() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("candidate.cpp"),
        r#"
        struct GenericState {
            std::atomic<int> counter;
            std::atomic<int> state;
            void first() { counter++; }
            void second() { state++; }
        };
        int values[64];
        void worker(int worker_id) { values[worker_id]++; }
    "#,
    )
    .unwrap();
    let mut options =
        AnalysisOptions::with_rules(&[RuleId::SameObjectFields, RuleId::ContiguousElements]);
    options.max_findings = Some(1);
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert_eq!(report.findings.len(), 1);
    assert_eq!(
        report.findings[0].candidate_kind,
        CandidateKind::IndexedWrites
    );
    assert!(
        report.findings[0]
            .access_evidence
            .iter()
            .all(|item| !item.in_concurrent_context)
    );
}

#[test]
fn field_group_fresh_factory_initialization_stops_at_publication() {
    let factory = r#"
        #include <memory>
        #define ALLOC_RECORD(type) ((type *)calloc(1, sizeof(type)))
        struct State { int counter; int state; };
        State *published;
        std::shared_ptr<State> handle;
        State *make() {
            State *value = ALLOC_RECORD(State);
            value->counter = 1;
            value->state = 2;
            PUBLISH
            return value;
        }
        int first(State *value) { return value->counter; }
        int second(State *value) { return value->state; }
    "#;
    let private_initialization =
        analyze(&factory.replace("PUBLISH", ""), CandidateKind::FieldGroup);
    assert!(
        private_initialization.findings.is_empty(),
        "{:#?}",
        private_initialization.findings
    );
    let public_mutation = analyze(
        &factory.replace(
            "PUBLISH",
            "published = value; value->counter++; value->state++;",
        ),
        CandidateKind::FieldGroup,
    );
    assert!(
        !public_mutation.findings.is_empty(),
        "writes after publication must remain"
    );
}

#[test]
fn indexed_writes_rejects_rhs_indexed_reads() {
    let report = analyze(
        r#"
        int values[16];
        void consume(int);
        void worker(int worker_id) {
            const auto & value = values[worker_id];
            consume(value);
        }
        "#,
        CandidateKind::IndexedWrites,
    );

    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn indexed_writes_keeps_direct_worker_indexed_writes() {
    let report = analyze(
        r#"
        int values[16];
        void * worker(void * raw) {
            int worker_id = *static_cast<int *>(raw);
            values[worker_id] += 1;
            return nullptr;
        }
        void start(int * worker_id) {
            pthread_t thread;
            pthread_create(&thread, nullptr, worker, worker_id);
        }
        "#,
        CandidateKind::IndexedWrites,
    );

    let finding = report
        .findings
        .iter()
        .find(|finding| finding.has_candidate(CandidateKind::IndexedWrites))
        .expect("direct worker-indexed write should remain a candidate");
    let pattern = finding
        .static_pattern
        .as_ref()
        .expect("C++ finding should carry a theory witness");
    assert!(pattern.has_write);
    assert!(pattern.may_happen_in_parallel);
    assert!(pattern.distinct_accesses);
}

#[test]
fn indexed_writes_single_pthread_record_does_not_establish_shared_bucket_partition() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("candidate.c"),
        r#"
        #include <pthread.h>
        typedef struct { int values[64]; int slot; } worker_arg;
        worker_arg args[8];
        void *worker(void *raw) {
            worker_arg *arg = (worker_arg *)raw;
            arg->values[arg->slot]++;
            return 0;
        }
        void start(pthread_t *threads) {
            pthread_create(&threads[0], 0, worker, &args[0]);
        }
        "#,
    )
    .unwrap();
    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert!(
        report
            .findings
            .iter()
            .all(|finding| !finding.has_candidate(CandidateKind::IndexedWrites)),
        "one worker on args[0] supplies no distinct concurrent bucket access: {report:#?}"
    );
}

#[test]
fn static_data_keeps_mutable_static_sync_pool_reviewable() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("spinlock.hpp"),
        "class spinlock { public: bool try_lock(); void lock(); void unlock(); int value; };\n",
    )
    .unwrap();
    fs::write(
        root.path().join("pool.hpp"),
        r#"
        class spinlock;
        template<int I> class spinlock_pool {
          static spinlock pool_[41];
        public:
          static spinlock &spinlock_for(void const *p) {
            unsigned i = (unsigned long)p % 41;
            return pool_[i];
          }
        };
        template<int I> spinlock spinlock_pool<I>::pool_[41] = {};
        "#,
    )
    .unwrap();
    let options =
        AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentStatics]);
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert!(
        report.findings.iter().any(|finding| {
            finding.has_candidate(CandidateKind::StaticData)
                && finding.field_list.iter().any(|field| field == "pool_")
        }),
        "mutable indexed lock-pool access should be reviewable: {report:#?}"
    );
}

#[test]
fn indexed_writes_tracks_owner_guarded_heap_blocks_through_helper_pointers() {
    let report = analyze(
        r#"
        #define BARRIER(...) barrier_impl(__VA_ARGS__)
        double *a;
        void touch(double *block) { block[0] += 1; }
        int BlockOwner(int i, int j) { return (i + j) % 2; }
        void lu(int MyNum) {
            if (BlockOwner(1, 1) == MyNum) {
                double *A = &(a[MyNum * 8]);
                touch(A);
            }
            BARRIER();
        }
        void start() {
            a = (double *)G_MALLOC(128 * sizeof(double));
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::IndexedWrites)),
        "owner-guarded helper pointer writes should remain reviewable: {report:#?}"
    );
}

#[test]
fn indexed_writes_keeps_openmp_loop_indexed_writes() {
    let report = analyze(
        r#"
        int values[16];
        void update() {
            #pragma omp parallel for
            for (int index = 0; index < 16; ++index) {
                values[index] += 1;
            }
        }
        "#,
        CandidateKind::IndexedWrites,
    );

    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::IndexedWrites)),
        "{:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_tracks_partitioned_index_alias_writes() {
    let report = analyze(
        r#"
        #include <vector>
        std::vector<double> values(64);
        void update(unsigned worker_id, double value) {
            auto &local = values[worker_id];
            local = value;
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.has_candidate(CandidateKind::IndexedWrites)
                && finding.field_list.iter().any(|field| field == "values")
        }),
        "partitioned reference aliases must preserve the storage identity: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_tracks_openmp_slice_alias_writes() {
    let report = analyze(
        r#"
        #include <span>
        using Span = std::span<int>;
        Span values;
        void update() {
            #pragma omp parallel
            {
                int rank = omp_get_thread_num();
                auto local = values.slice(16 * rank, 16 * (rank + 1));
                local[3]++;
            }
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::IndexedWrites)),
        "an unpadded worker slice with a later write must be retained: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_parent_alignment_does_not_protect_array_elements() {
    let report = analyze(
        r#"
        struct alignas(64) Stats { unsigned long packets[128]; };
        Stats shared;
        void update() {
            shared.packets[rte_lcore_id()]++;
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::IndexedWrites)),
        "record alignment does not change the stride of an embedded array: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_recognizes_openmp_wrapper_macro_regions() {
    let report = analyze(
        r#"
        #include <vector>
        std::vector<int> counts(64);
        void update() {
            vendor_omp_parallel {
                int tid = vendor_omp_get_thread_num();
                counts[tid]++;
            }
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::IndexedWrites)),
        "explicit OpenMP wrapper macros must retain their lexical MHP region: {:#?}",
        report.findings
    );
}

#[test]
fn prefixed_atomic_apis_preserve_record_field_access_roles() {
    let report = analyze(
        r#"
        typedef struct {
            _Atomic(long) top;
            _Atomic(long) bottom;
            _Atomic(void *) array;
        } Queue;
        std::shared_ptr<Queue> published;
        void push(Queue *q) { jl_atomic_store_relaxed(&q->bottom, 1); }
        void steal(Queue *q) { jl_atomic_cmpswap(&q->top, 0, 1); }
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.field_list.iter().any(|field| field == "top")
                && finding.field_list.iter().any(|field| field == "bottom")
        }),
        "prefixing a standard atomic operation must not hide its first-argument role: {:#?}",
        report.findings
    );
}

#[test]
fn c11_atomic_typedef_header_exposes_multi_role_queue_api() {
    let root = tempdir().expect("create temporary C header project");
    fs::write(
        root.path().join("queue.h"),
        r#"
        typedef struct {
            _Atomic(long) top;
            _Atomic(long) bottom;
            _Atomic(void *) array;
        } Queue;
        static inline void push(Queue *q) JL_NOTSAFEPOINT
        { jl_atomic_store_relaxed(&q->bottom, 1); }
        static inline void steal(Queue *q) JL_NOTSAFEPOINT
        { jl_atomic_cmpswap(&q->top, 0, 1); }
        "#,
    )
    .expect("write C header fixture");
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.field_list.iter().any(|field| field == "top")
                && finding.field_list.iter().any(|field| field == "bottom")
        }),
        "an externally visible C atomic queue API supplies independent roles: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_recognizes_camel_case_lock_array_mutation() {
    let report = analyze(
        r#"
        struct Spin { void tryLock(); };
        Spin locks[32];
        void acquire(unsigned worker_id) { locks[worker_id].tryLock(); }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::IndexedWrites)),
        "custom lock method spelling still denotes an element mutation: {:#?}",
        report.findings
    );
}

#[test]
fn object_instances_recognizes_cas_spinlock_object_stride() {
    let report = analyze(
        r#"
        class SpinLock {
            volatile int _lock;
        public:
            bool tryLock() { return __sync_bool_compare_and_swap(&_lock, 0, 1); }
            void unlock() { __sync_fetch_and_sub(&_lock, 1); }
        };
        struct Pool {
            SpinLock locks[32];
        };
        "#,
        CandidateKind::ObjectInstances,
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.struct_name.as_deref() == Some("SpinLock")
                && finding.field_list.iter().any(|field| field == "_lock")
        }),
        "a dense custom CAS lock array has sub-cache-line object stride: {:#?}",
        report.findings
    );
}

#[test]
fn object_instances_propagates_template_type_aliases_into_contiguous_object_storage() {
    let report = analyze(
        r#"
        template <int Role>
        class SearchTask {
            unsigned long nodes = 0;
            unsigned long state = 0;
        public:
            void run() { nodes += 1; }
            unsigned long status() const { return state; }
        };
        using WorkerTask = SearchTask<1>;
        struct Pool {
            std::vector<WorkerTask> tasks;
        };
        "#,
        CandidateKind::ObjectInstances,
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.struct_name.as_deref() == Some("SearchTask")
                && finding.field_list.iter().any(|field| field == "nodes")
        }),
        "a template record remains the element type behind a using alias: {:#?}",
        report.findings
    );
}

#[test]
fn static_data_tracks_static_lock_arrays_through_pointer_accessors() {
    let report = analyze(
        r#"
        typedef pthread_mutex_t Lock;
        static Lock locks[128];
        static Lock *select_lock(unsigned hash) {
            return locks + (hash & 127);
        }
        void acquire(unsigned hash) { pthread_mutex_lock(select_lock(hash)); }
        "#,
        CandidateKind::StaticData,
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.has_candidate(CandidateKind::StaticData)
                && finding.field_list.iter().any(|field| field == "locks")
        }),
        "a mutable pointer accessor preserves the selected static array element: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_propagates_indexed_mutator_summaries_to_partitioned_calls() {
    let report = analyze(
        r#"
        struct Graph {
            long weights[32];
            void move_weight(unsigned block, long delta) {
                __atomic_fetch_add(
                    &weights[block],
                    delta,
                    __ATOMIC_RELAXED
                );
            }
        };
        void refine(Graph *graph, unsigned block) {
            graph->move_weight(block, 1);
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.has_candidate(CandidateKind::IndexedWrites)
                && finding.field_list.iter().any(|field| field == "weights")
                && finding.symbol.as_deref() == Some("refine")
        }),
        "bounded mutator summaries must preserve the backing indexed field: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_tracks_atomic_reference_aliases_inside_parallel_callbacks() {
    let vulnerable = analyze(
        r#"
        std::vector<int> counts;
        void update() {
            particle_loop([=](auto worker_index) {
                sycl::atomic_ref<int, sycl::memory_order::relaxed,
                                 sycl::memory_scope::device>
                    active(counts[worker_index.cell]);
                active.fetch_add(1);
            });
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        vulnerable.findings.iter().any(|finding| {
            finding.has_candidate(CandidateKind::IndexedWrites)
                && finding.field_list.iter().any(|field| field == "counts")
                && finding.symbol.as_deref() == Some("update")
        }),
        "an atomic_ref alias preserves its partitioned backing storage: {:#?}",
        vulnerable.findings
    );

    let unknown_stride = analyze(
        r#"
        std::vector<int> counts;
        void update() {
            parallel_for([=](auto worker_index) {
                atomic_fetch_add(&counts[worker_index.cell * CACHE_LINE_STEP], 1);
            });
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        !unknown_stride.findings.is_empty(),
        "an unresolved stride name supplies no numeric layout proof: {:#?}",
        unknown_stride.findings
    );
    let fixed = analyze(
        "struct alignas(128) Slot { int value; };\nSlot counts[16];\nvoid update() {\n#pragma omp parallel for\nfor (int i=0;i<16;++i) { counts[i].value++; }\n}",
        CandidateKind::IndexedWrites,
    );
    assert!(fixed.findings.is_empty(), "{:#?}", fixed.findings);
}

#[test]
fn indexed_writes_recognizes_cpu_keyed_bpf_array_map_updates() {
    let report = analyze(
        r#"
        struct {
            __uint(type, BPF_MAP_TYPE_ARRAY);
            __type(key, u32);
            __type(value, u64);
        } counters SEC(".maps");
        int sample() {
            u32 cpu = bpf_get_smp_processor_id();
            u64 value = 1;
            bpf_map_update_elem(&counters, &cpu, &value, 0);
            return 0;
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.has_candidate(CandidateKind::IndexedWrites)
                && finding.field_list.iter().any(|field| field == "counters")
        }),
        "CPU-keyed BPF array map slots are contiguous partitioned storage: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_suppresses_one_container_lock_but_not_indexed_locks() {
    let whole_container = analyze(
        r#"
        int values[16];
        int mutex;
        void * worker(void * raw) {
            int worker_id = *static_cast<int *>(raw);
            std::lock_guard guard(mutex);
            values[worker_id] += 1;
            return nullptr;
        }
        void start(int * worker_id) {
            pthread_t thread;
            pthread_create(&thread, nullptr, worker, worker_id);
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        whole_container.findings.is_empty(),
        "one scalar lock serializes all indexed writes: {:#?}",
        whole_container.findings
    );

    let per_element = analyze(
        r#"
        int values[16];
        int locks[16];
        void * worker(void * raw) {
            int worker_id = *static_cast<int *>(raw);
            std::lock_guard guard(locks[worker_id]);
            values[worker_id] += 1;
            return nullptr;
        }
        void start(int * worker_id) {
            pthread_t thread;
            pthread_create(&thread, nullptr, worker, worker_id);
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        per_element
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::IndexedWrites)),
        "locks[index] do not serialize writes to values[index] across workers: {:#?}",
        per_element.findings
    );
}

#[test]
fn static_data_requires_a_concurrent_partitioned_write_to_static_array_storage() {
    let positive = analyze(
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
        CandidateKind::StaticData,
    );
    assert!(
        positive
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::StaticData)),
        "an actual parallel indexed write should retain static-array risk: {:#?}",
        positive.findings
    );

    let read_only = analyze(
        r#"
        #include <atomic>
        static std::atomic<int> counters[16];
        int read(int index) {
            return counters[index].load();
        }
        "#,
        CandidateKind::StaticData,
    );
    assert!(
        read_only.findings.is_empty(),
        "a declaration and reads do not establish static-array false sharing: {:#?}",
        read_only.findings
    );
}

#[test]
fn atomic_array_requires_access_to_the_actual_atomic_alias_storage() {
    let positive = analyze(
        r#"
        #include <atomic>
        using Counter = std::atomic<int>;
        Counter counters[16];
        void update() {
            #pragma omp parallel for
            for (int index = 0; index < 16; ++index) {
                counters[index].fetch_add(1);
            }
        }
        "#,
        CandidateKind::AtomicArray,
    );
    assert!(
        positive
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::AtomicArray)),
        "atomic alias storage with a parallel indexed write should report: {:#?}",
        positive.findings
    );

    let unrelated_write = analyze(
        r#"
        #include <atomic>
        using Counter = std::atomic<int>;
        Counter counters[16];
        int other[16];
        void update() {
            #pragma omp parallel for
            for (int index = 0; index < 16; ++index) {
                other[index] += 1;
            }
        }
        "#,
        CandidateKind::AtomicArray,
    );
    assert!(
        unrelated_write.findings.is_empty(),
        "a write to another array cannot establish an alias-array write: {:#?}",
        unrelated_write.findings
    );
}

#[test]
fn atomic_array_does_not_report_unused_atomic_alias_storage() {
    let report = analyze(
        r#"
        #include <atomic>
        using Counter = std::atomic<int>;
        Counter counters[16];
        void initialize() {
            for (int index = 0; index < 16; ++index) counters[index].store(0);
        }
        "#,
        CandidateKind::AtomicArray,
    );
    assert!(
        report.findings.is_empty(),
        "declaration and initialization alone must not establish atomic-array sharing: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_rejects_associative_container_indexing() {
    let report = analyze(
        r#"
        #include <map>
        std::map<int, int> values;
        void worker(int worker_id) {
            values[worker_id] += 1;
        }
        "#,
        CandidateKind::IndexedWrites,
    );

    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn indexed_writes_read_only_indexed_traversal_is_not_a_write_conflict() {
    let report = analyze(
        r#"
        int values[64];
        int sum(int worker_id) {
            int total = 0;
            for (int index = worker_id; index < 64; index += 4) total += values[index];
            return total;
        }
        "#,
        CandidateKind::IndexedWrites,
    );
    assert!(
        report.findings.is_empty(),
        "read-only indexed traversal must not report: {report:#?}"
    );
}

#[test]
fn indexed_writes_requires_positive_contiguous_storage_evidence() {
    let report = analyze(
        r#"
        struct Settings {
            int & operator[](int);
        };
        Settings values;
        void * worker(void * raw) {
            int worker_id = *static_cast<int *>(raw);
            values[worker_id] += 1;
            return nullptr;
        }
        void start(int * worker_id) {
            pthread_t thread;
            pthread_create(&thread, nullptr, worker, worker_id);
        }
        "#,
        CandidateKind::IndexedWrites,
    );

    assert!(
        report.findings.is_empty(),
        "an arbitrary overloaded operator[] does not prove contiguous storage: {:#?}",
        report.findings
    );
}

#[test]
fn indexed_writes_rejects_thread_local_arrays() {
    let report = analyze(
        r#"
        thread_local int values[16];
        void worker(int worker_id) {
            values[worker_id] += 1;
        }
        "#,
        CandidateKind::IndexedWrites,
    );

    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn field_group_rejects_thread_local_record_access_inside_a_worker() {
    let shared = analyze(
        r#"
        struct Counters {
            int hits;
            int misses;
        };
        Counters current;
        void * worker(void *) {
            current.hits += 1;
            current.misses += 1;
            return nullptr;
        }
        void start() {
            pthread_t thread;
            pthread_create(&thread, nullptr, worker, nullptr);
        }
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        shared
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup)),
        "shared control should remain reportable: {:#?}",
        shared.findings
    );

    let thread_local = analyze(
        r#"
        struct Counters {
            int hits;
            int misses;
        };
        thread_local Counters current;
        void * worker(void *) {
            current.hits += 1;
            current.misses += 1;
            return nullptr;
        }
        void start() {
            pthread_t thread;
            pthread_create(&thread, nullptr, worker, nullptr);
        }
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        thread_local.findings.is_empty(),
        "TLS receiver has one record instance per thread: {:#?}",
        thread_local.findings
    );
}

#[test]
fn field_group_rejects_a_nonescaping_worker_local_record() {
    let report = analyze(
        r#"
        struct Counters {
            int hits;
            int misses;
        };
        void * worker(void *) {
            Counters local;
            local.hits += 1;
            local.misses += 1;
            return nullptr;
        }
        void start() {
            pthread_t thread;
            pthread_create(&thread, nullptr, worker, nullptr);
        }
        "#,
        CandidateKind::FieldGroup,
    );

    assert!(
        report.findings.is_empty(),
        "each worker invocation owns a distinct non-escaping stack object: {:#?}",
        report.findings
    );
}

#[test]
fn field_group_distinguishes_local_and_thread_escaped_shared_ownership() {
    let local_owner = analyze(
        r#"
        #include <memory>
        struct Counters {
            int hits;
            int misses;
        };
        void * worker(void *) {
            auto local = std::make_shared<Counters>();
            local->hits += 1;
            local->misses += 1;
            return nullptr;
        }
        void start() {
            pthread_t thread;
            pthread_create(&thread, nullptr, worker, nullptr);
        }
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        local_owner.findings.is_empty(),
        "a shared_ptr that never escapes one worker is not cross-thread sharing: {:#?}",
        local_owner.findings
    );

    let escaped_owner = analyze(
        r#"
        #include <memory>
        #include <thread>
        struct Counters {
            int hits;
            int misses;
        };
        void start() {
            auto shared = std::make_shared<Counters>();
            std::thread first([shared] {
                shared->hits += 1;
            });
            std::thread second([shared] {
                shared->misses += 1;
            });
        }
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        escaped_owner
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup)),
        "capturing the same owner into worker lambdas is shared reachability: {:#?}",
        escaped_owner.findings
    );
}

#[test]
fn field_group_uses_same_guard_annotations_as_a_positive_exclusion() {
    let unguarded = analyze(
        r#"
        #include <memory>
        struct Counters {
            int hits;
            int misses;
            void update() { hits += 1; misses += 1; }
        };
        std::shared_ptr<Counters> shared;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        unguarded
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup)),
        "unguarded control should remain reportable: {:#?}",
        unguarded.findings
    );

    let guarded = analyze(
        r#"
        #include <memory>
        #define GUARDED_BY(x)
        struct Counters {
            int mutex;
            int hits GUARDED_BY(mutex);
            int misses GUARDED_BY(mutex);
            void update() { hits += 1; misses += 1; }
        };
        std::shared_ptr<Counters> shared;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(guarded.findings.is_empty(), "{:#?}", guarded.findings);
}

#[test]
fn field_group_distinguishes_object_alignment_from_field_separation() {
    let object_only = analyze(
        r#"
        #include <atomic>
        #include <memory>
        struct alignas(64) Counters {
            std::atomic<int> hits;
            std::atomic<int> misses;
            void update_hits() { hits.fetch_add(1); }
            void update_misses() { misses.fetch_add(1); }
        };
        std::shared_ptr<Counters> shared;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        object_only
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup)),
        "aligning the object base does not separate fields within that object: {:#?}",
        object_only.findings
    );

    let separated_fields = analyze(
        r#"
        #include <atomic>
        #include <memory>
        struct Counters {
            alignas(64) std::atomic<int> hits;
            alignas(64) std::atomic<int> misses;
            void update_hits() { hits.fetch_add(1); }
            void update_misses() { misses.fetch_add(1); }
        };
        std::shared_ptr<Counters> shared;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        separated_fields.findings.is_empty(),
        "field-level alignment separates the candidate pair: {:#?}",
        separated_fields.findings
    );
}

#[test]
fn field_group_uses_a_common_scoped_lock_but_not_per_field_locks() {
    let whole_pair = analyze(
        r#"
        #include <memory>
        #include <mutex>
        struct Counters {
            int mutex;
            int hits;
            int misses;
            void update() {
                std::lock_guard guard(mutex);
                hits += 1;
                misses += 1;
            }
        };
        std::shared_ptr<Counters> shared;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        whole_pair.findings.is_empty(),
        "one common scalar lock serializes the complete pair: {:#?}",
        whole_pair.findings
    );

    let per_field = analyze(
        r#"
        #include <memory>
        #include <mutex>
        struct Counters {
            int hits_mutex;
            int misses_mutex;
            int hits;
            int misses;
            void update_hits() {
                std::lock_guard guard(hits_mutex);
                hits += 1;
            }
            void update_misses() {
                std::lock_guard guard(misses_mutex);
                misses += 1;
            }
        };
        std::shared_ptr<Counters> shared;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        per_field
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup)),
        "different per-field locks do not prevent false sharing: {:#?}",
        per_field.findings
    );
}

#[test]
fn field_group_does_not_treat_constructor_writes_as_shared_phase_writes() {
    let initialization_only = analyze(
        r#"
        #include <memory>
        struct Configuration {
            int counter;
            int state;
            Configuration() {
                counter = 0;
                state = 1;
            }
            int read() const { return counter + state; }
        };
        std::shared_ptr<Configuration> shared;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        initialization_only.findings.is_empty(),
        "constructor-only writes cannot overlap post-publication reads: {:#?}",
        initialization_only.findings
    );

    let mutable_after_publish = analyze(
        r#"
        #include <memory>
        struct Configuration {
            int counter;
            int state;
            Configuration() {
                counter = 0;
                state = 1;
            }
            void update_counter() { counter += 1; }
            void update_state() { state += 1; }
        };
        std::shared_ptr<Configuration> shared;
        "#,
        CandidateKind::FieldGroup,
    );
    assert!(
        mutable_after_publish
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup)),
        "post-construction writes should remain reportable: {:#?}",
        mutable_after_publish.findings
    );
}

#[test]
fn separate_allocations_requires_a_source_allocation_topology() {
    let report = analyze(
        r#"
        #include <atomic>
        struct ThreadState {
            std::atomic<int> counter;
            int thread_index;
        };
        void update(ThreadState * state) {
            state->counter.fetch_add(1);
            state->thread_index = 1;
        }
        "#,
        CandidateKind::SeparateAllocations,
    );

    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn mixed_fields_recognizes_queue_state_and_respects_a_manual_padding_boundary() {
    let vulnerable = analyze(
        r#"
        typedef int spinlock_t;
        struct list_head { void *next; };
        struct QueueState {
            struct list_head pending;
            spinlock_t pending_lock;
            unsigned num_pending;
            struct list_head ready;
        };
        void submit(QueueState *state, void *item) {
            state->pending.next = item;
            state->num_pending += 1;
        }
        void complete(QueueState *state, void *item) {
            state->ready.next = item;
        }
        void run(QueueState *state, void *item) {
            std::thread submitter(submit, state, item);
            std::thread completer(complete, state, item);
            submitter.join();
            completer.join();
        }
        "#,
        CandidateKind::MixedFields,
    );
    assert!(
        vulnerable.findings.iter().any(|finding| {
            finding.has_candidate(CandidateKind::MixedFields)
                && finding.struct_name.as_deref() == Some("QueueState")
                && finding.field_list.iter().any(|field| field == "pending")
                && finding.field_list.iter().any(|field| field == "ready")
        }),
        "unseparated queue roles should remain reportable: {:#?}",
        vulnerable.findings
    );

    let fixed = analyze(
        r#"
        typedef int spinlock_t;
        struct list_head { void *next; };
        struct QueueState {
            struct list_head pending;
            spinlock_t pending_lock;
            unsigned num_pending;
            unsigned long padding[16];
            struct list_head ready;
        };
        void submit(QueueState *state, void *item) {
            state->pending.next = item;
            state->num_pending += 1;
        }
        void complete(QueueState *state, void *item) {
            state->ready.next = item;
        }
        void run(QueueState *state, void *item) {
            std::thread submitter(submit, state, item);
            std::thread completer(complete, state, item);
            submitter.join();
            completer.join();
        }
        "#,
        CandidateKind::MixedFields,
    );
    assert!(
        fixed.findings.iter().all(|finding| {
            finding.struct_name.as_deref() != Some("QueueState")
                || !finding.has_candidate(CandidateKind::MixedFields)
        }),
        "cache-line padding is a negative layout proof: {:#?}",
        fixed.findings
    );
}

#[cfg(unix)]
#[test]
fn compiler_sidecar_exact_layout_changes_the_colocation_gate() {
    let root = tempdir().expect("create temporary C++ project");
    let source = r#"
        #include <memory>
        struct Counters {
            int hits;
            int misses;
            void update_hits() { hits += 1; }
            void update_misses() { misses += 1; }
        };
        std::shared_ptr<Counters> shared;
    "#;
    let source_path = root.path().join("candidate.cpp");
    fs::write(&source_path, source).expect("write C++ fixture");
    fs::write(
        root.path().join("compile_commands.json"),
        serde_json::to_vec(&serde_json::json!([{
            "directory": root.path(),
            "file": "candidate.cpp",
            "arguments": ["g++", "-c", "candidate.cpp"]
        }]))
        .expect("serialize compile database"),
    )
    .expect("write compile database");

    let mut broad_options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    broad_options.cpp_include_speculative = true;
    let baseline = analyze_cpp_path_with_options(root.path(), &broad_options);
    assert!(
        baseline
            .findings
            .iter()
            .any(|finding| finding.has_candidate(CandidateKind::FieldGroup)),
        "source-inferred layout should retain the may-colocation: {:#?}",
        baseline.findings
    );

    let sidecar = root.path().join("sidecar.sh");
    fs::write(
        &sidecar,
        "#!/bin/sh\ncat >/dev/null\nprintf '%s' '{\"schema_version\":\"false-sharing-cpp-semantic-sidecar/v1\",\"records\":[{\"name\":\"Counters\",\"canonical_type\":\"Counters\",\"size\":128,\"alignment\":64,\"fields\":[{\"name\":\"hits\",\"offset\":0,\"size\":4},{\"name\":\"misses\",\"offset\":64,\"size\":4}]}],\"accesses\":[]}'\n",
    )
    .expect("write fake compiler sidecar");
    let mut permissions = fs::metadata(&sidecar)
        .expect("sidecar metadata")
        .permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&sidecar, permissions).expect("make sidecar executable");

    let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    options.cpp_semantic_sidecar = Some(sidecar);
    options.cpp_include_speculative = true;
    let exact = analyze_cpp_path_with_options(root.path(), &options);
    assert!(
        exact.findings.is_empty(),
        "compiler-exact offsets place the fields on distinct lines: {:#?}",
        exact.findings
    );
    assert!(exact.diagnostics.is_empty(), "{:#?}", exact.diagnostics);
}
