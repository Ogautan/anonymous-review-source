use false_sharing_detector::cpp_detection::types::{
    CppAccessKind, CppEvidenceItem, CppEvidenceKind, CppEvidenceSet,
};
use false_sharing_detector::types::RuleId;

fn access(field: &str, kind: CppAccessKind, line: usize) -> CppEvidenceItem {
    CppEvidenceItem {
        element_member_path: Vec::new(),
        concurrent_call_path: vec![],
        kind: CppEvidenceKind::HotScalarWrite,
        access_kind: Some(kind),
        field_name: Some(field.into()),
        hotness_score: 10.0,
        in_concurrent_context: false,
        through_shared_indirection: true,
        through_raw_pointer: false,
        through_thread_local: false,
        through_nonescaping_local: false,
        through_automatic_receiver: false,
        guard_ids: vec![],
        initialization_phase: false,
        in_record_constructor: false,
        function_name: Some("work".into()),
        description: "fixture access".into(),
        file: "fixture.cpp".into(),
        line,
    }
}

#[test]
fn evidence_budget_retains_a_rare_read_peer_before_or_after_hot_writes() {
    for read_first in [false, true] {
        let mut evidence = CppEvidenceSet::default();
        let read = access("peer", CppAccessKind::Read, 1);
        if read_first {
            evidence.push_item(read.clone());
        }
        for line in 2..150 {
            evidence.push_item(access("counter", CppAccessKind::ReadModifyWrite, line));
        }
        if !read_first {
            evidence.push_item(read);
        }
        assert_eq!(evidence.items.len(), 64);
        assert!(evidence.truncated_items > 0);
        assert!(evidence.items.iter().any(|item| {
            item.field_name.as_deref() == Some("peer")
                && item.access_kind == Some(CppAccessKind::Read)
        }));
    }
}

#[test]
fn evidence_budget_keeps_unguarded_runtime_and_distinct_function_roles() {
    let mut evidence = CppEvidenceSet::default();
    for line in 1..100 {
        let mut item = access("counter", CppAccessKind::Write, line);
        item.initialization_phase = true;
        item.guard_ids.push("mutex".into());
        item.hotness_score = 100.0;
        evidence.push_item(item);
    }
    let runtime = access("counter", CppAccessKind::Write, 101);
    evidence.push_item(runtime);
    let mut other = access("counter", CppAccessKind::Read, 102);
    other.function_name = Some("inspect".into());
    evidence.push_item(other);
    assert!(evidence.items.iter().any(|item| {
        item.access_kind == Some(CppAccessKind::Write)
            && !item.initialization_phase
            && item.guard_ids.is_empty()
    }));
    assert!(evidence.items.iter().any(|item| {
        item.function_name.as_deref() == Some("inspect")
            && item.access_kind == Some(CppAccessKind::Read)
    }));
}

#[test]
fn evidence_dedup_preserves_same_line_phase_and_lock_transitions() {
    let mut evidence = CppEvidenceSet::default();
    let runtime = access("counter", CppAccessKind::Write, 10);
    let mut initialization = runtime.clone();
    initialization.initialization_phase = true;
    let mut guarded = runtime.clone();
    guarded.guard_ids.push("mutex".into());
    let mut construction = runtime.clone();
    construction.in_record_constructor = true;
    evidence.push_item(initialization);
    evidence.push_item(construction);
    evidence.push_item(guarded);
    evidence.push_item(runtime.clone());
    evidence.push_item(runtime);
    assert_eq!(evidence.items.len(), 4);
    assert!(
        evidence
            .items
            .iter()
            .any(|item| { !item.initialization_phase && item.guard_ids.is_empty() })
    );
}

#[test]
fn evidence_preserves_automatic_and_shared_receivers_under_dedup_and_budget() {
    for shared_first in [false, true] {
        let mut evidence = CppEvidenceSet::default();
        let shared = access("counter", CppAccessKind::Write, 10);
        let mut local = shared.clone();
        local.through_automatic_receiver = true;
        evidence.push_item(local.clone());
        evidence.push_item(shared.clone());
        assert_eq!(evidence.items.len(), 2);

        let mut evidence = CppEvidenceSet::default();
        if shared_first {
            evidence.push_item(shared.clone());
        }
        for line in 20..180 {
            local.line = line;
            local.hotness_score = 100.0;
            evidence.push_item(local.clone());
        }
        if !shared_first {
            evidence.push_item(shared);
        }
        assert!(evidence.truncated_items > 0);
        assert!(
            evidence
                .items
                .iter()
                .any(|item| !item.through_automatic_receiver)
        );
        assert!(
            evidence
                .items
                .iter()
                .any(|item| item.through_automatic_receiver)
        );
    }
}

#[test]
fn evidence_budget_prioritizes_field_roles_before_repeated_function_roles() {
    let mut evidence = CppEvidenceSet::default();
    for line in 1..90 {
        let mut item = access("counter", CppAccessKind::ReadModifyWrite, line);
        item.function_name = Some(format!("worker_{line}"));
        item.hotness_score = 100.0;
        evidence.push_item(item);
    }
    evidence.push_item(access("peer", CppAccessKind::Read, 100));
    let mut guarded = access("peer", CppAccessKind::Read, 101);
    guarded.guard_ids.push("mutex".into());
    evidence.push_item(guarded);
    for line in 102..180 {
        let mut item = access("counter", CppAccessKind::ReadModifyWrite, line);
        item.function_name = Some(format!("worker_{line}"));
        item.hotness_score = 100.0;
        evidence.push_item(item);
    }
    assert!(
        evidence.items.iter().any(|item| {
            item.field_name.as_deref() == Some("peer") && item.guard_ids.is_empty()
        })
    );
    assert!(
        evidence.items.iter().any(|item| {
            item.field_name.as_deref() == Some("peer") && !item.guard_ids.is_empty()
        })
    );
}

#[test]
fn inline_getter_effect_survives_record_evidence_truncation() {
    use false_sharing_detector::cpp_detection::{
        evidence::collect_cpp_evidence, layout::collect_cpp_structs, parser::parse_cpp_files,
        types::CppFile,
    };
    let fields = (0..90)
        .map(|i| format!("int value_{i};\n"))
        .collect::<String>();
    let writes = (0..90)
        .map(|i| format!("value_{i}++;\n"))
        .collect::<String>();
    for (getter, expected) in [("return payload;", true), ("return 7;", false)] {
        let files = parse_cpp_files(vec![CppFile {
            path: "objects.hpp".into(),
            source: format!(
                r#"
struct Inner {{
    int payload;
    {fields}
    int get() const {{ {getter} }}
    void update() {{ {writes} }}
}};
struct Outer {{
    Inner state;
    int read() {{ return state.get(); }}
}};
"#
            ),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        let inner = records.iter().position(|r| r.name == "Inner").unwrap();
        let outer = records.iter().position(|r| r.name == "Outer").unwrap();
        assert!(facts[inner].truncated_items > 0);
        assert!(facts[inner].items.len() <= 64);
        assert_eq!(
            facts[outer]
                .items
                .iter()
                .any(|a| a.field_name.as_deref() == Some("state")
                    && a.kind == CppEvidenceKind::InlineMemberAccess
                    && a.access_kind == Some(CppAccessKind::Read)),
            expected
        );
    }
}

#[test]
fn evidence_truncation_does_not_invent_separate_callable_field_sets() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    for block in [32, 64, 128] {
        for methods in [2, 80] {
            for independent_reader in [false, true] {
                let root = tempfile::tempdir().unwrap();
                let reader = if independent_reader {
                    "int inspect() { return peer.load(); }\n"
                } else {
                    ""
                };
                let coupled = (0..methods)
                    .map(|i| {
                        format!(
                            "void work_{i}() {{\ncounter.fetch_add(1);\npeer.fetch_add(1);\n}}\n"
                        )
                    })
                    .collect::<String>();
                std::fs::write(root.path().join("state.hpp"), format!(
                    "struct State {{\nstd::atomic<int> counter;\nstd::atomic<int> peer;\n{reader}{coupled}}};\nstd::shared_ptr<State> shared;\n"
                )).unwrap();
                let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
                options.cache_line_size = block;
                let report = analyze_cpp_path_with_options(root.path(), &options);
                assert_eq!(
                    !report.findings.is_empty(),
                    independent_reader,
                    "B={block}, methods={methods}, reader={independent_reader}: {report:#?}"
                );
                if methods == 80 {
                    assert!(report.truncated_facts > 0);
                    assert!(report.analysis_incomplete);
                    assert!(report.diagnostics.iter().any(|d| d.stage == "evidence"));
                    options.cpp_include_speculative = true;
                    assert!(
                        !analyze_cpp_path_with_options(root.path(), &options)
                            .findings
                            .is_empty()
                    );
                }
            }
        }
    }
}

#[test]
fn omitted_membership_keeps_file_identity_and_excludes_other_storage_domains() {
    let mut evidence = CppEvidenceSet::default();
    for line in 0..64 {
        let mut item = access("counter", CppAccessKind::ReadModifyWrite, line);
        item.function_name = Some(format!("worker_{line}"));
        evidence.push_item(item);
    }
    for file in ["left.cpp", "right.cpp"] {
        let mut omitted = access("counter", CppAccessKind::Read, 100);
        omitted.file = file.into();
        evidence.push_item(omitted);
    }
    assert_eq!(evidence.omitted_access_roles.len(), 2);
    for variant in 0..5 {
        let mut local = access("counter", CppAccessKind::Read, 200 + variant);
        match variant {
            0 => local.initialization_phase = true,
            1 => local.through_thread_local = true,
            2 => local.through_nonescaping_local = true,
            3 => local.through_automatic_receiver = true,
            _ => local.kind = CppEvidenceKind::ContiguousElementAccess,
        }
        evidence.push_item(local);
    }
    assert!(
        evidence
            .omitted_access_roles
            .iter()
            .all(|r| r.file != "fixture.cpp" || r.function != "work")
    );
}

#[test]
fn omitted_helper_access_invalidates_its_callers_partial_runtime_role() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    for methods in [2, 80] {
        let root = tempfile::tempdir().unwrap();
        let coupled = (0..methods)
            .map(|i| format!("void work_{i}() {{\ncounter.fetch_add(1);\npeer.fetch_add(1);\n}}\n"))
            .collect::<String>();
        std::fs::write(root.path().join("state.hpp"), format!(
            "struct State {{\nstd::atomic<int> counter;\nstd::atomic<int> peer;\npublic:\nvoid indirect() {{\npeer.fetch_add(1);\nhelper();\n}}\n{coupled}private:\nvoid helper() {{ counter.fetch_add(1); }}\n}};\nstd::shared_ptr<State> shared;\n"
        )).unwrap();
        let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert!(report.findings.is_empty(), "methods={methods}: {report:#?}");
        assert_eq!(report.truncated_facts > 0, methods == 80);
    }
}

#[test]
fn omitted_membership_overflow_is_bounded_and_diagnostic() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    let root = tempfile::tempdir().unwrap();
    let writers = (0..1100)
        .map(|i| format!("void work_{i}() {{ counter.fetch_add(1); }}\n"))
        .collect::<String>();
    std::fs::write(root.path().join("state.hpp"), format!(
        "struct State {{\nstd::atomic<int> counter;\nstd::atomic<int> peer;\nint inspect() {{ return peer.load(); }}\n{writers}}};\n"
    )).unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let report = analyze_cpp_path_with_options(root.path(), &options);
    assert!(report.analysis_incomplete);
    assert!(report.findings.is_empty());
    assert!(
        report
            .diagnostics
            .iter()
            .any(|d| d.message.contains("membership summary overflowed"))
    );
    options.cpp_include_speculative = true;
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
}

#[test]
fn retained_helper_write_covers_an_omitted_read_in_the_same_runtime_entry() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    for methods in [2, 80] {
        let root = tempfile::tempdir().unwrap();
        let writers = (0..methods)
            .map(|i| format!("void work_{i}() {{ counter.fetch_add(1); }}\n"))
            .collect::<String>();
        std::fs::write(root.path().join("state.hpp"), format!(
            "struct State {{\nstd::atomic<int> counter;\nstd::atomic<int> peer;\nprivate:\nvoid helper() {{\nconsume(peer.load());\npeer.fetch_add(1);\n}}\npublic:\nint inspect() {{ return counter.load(); }}\n{writers}void wrapper() {{\nconsume(peer.load());\nhelper();\n}}\n}};\nstd::shared_ptr<State> shared;\n"
        )).unwrap();
        let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert!(
            !report.findings.is_empty(),
            "methods={methods}: {report:#?}"
        );
        assert_eq!(report.truncated_facts > 0, methods == 80);
    }
}
