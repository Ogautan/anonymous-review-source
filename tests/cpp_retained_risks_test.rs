use false_sharing_detector::types::RuleId;
use std::fs;

use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
use false_sharing_detector::cpp_detection::evidence::collect_cpp_evidence;
use false_sharing_detector::cpp_detection::layout::collect_cpp_structs;
use false_sharing_detector::cpp_detection::parser::parse_cpp_files;
use false_sharing_detector::cpp_detection::pattern::retain_theory_candidates;
use false_sharing_detector::cpp_detection::rules::apply_cpp_rules;
use false_sharing_detector::cpp_detection::types::{
    CppAccessKind, CppEvidenceKind, CppEvidenceSet, CppFile,
};
use false_sharing_detector::types::{
    AccessPattern, AnalysisOptions, CandidateKind, Finding, Report,
};
use tempfile::tempdir;

fn evidence(source: &str) -> Vec<(String, CppEvidenceSet)> {
    let files = parse_cpp_files(vec![CppFile {
        path: "candidate.cpp".into(),
        source: source.into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    collect_cpp_evidence(&files, &records)
        .into_iter()
        .zip(records)
        .map(|(evidence, record)| (record.name, evidence))
        .collect()
}

fn analyze(source: &str, rule: CandidateKind) -> Report {
    // Project a discovery method for these focused regressions; public selection uses relations.
    let mut report = {
        let root = tempdir().unwrap();
        fs::write(root.path().join("candidate.hpp"), source).unwrap();
        // These are may-risk retention tests, not default reportability tests.
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

fn field_has_write(source: &str, record: &str, field: &str) -> bool {
    let facts = evidence(source);
    facts.iter().any(|(name, facts)| {
        name == record
            && facts.items.iter().any(|item| {
                item.field_name.as_deref() == Some(field)
                    && item.kind != CppEvidenceKind::ContiguousElementAccess
                    && !item.initialization_phase
                    && matches!(
                        item.access_kind,
                        Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                    )
            })
    })
}

#[test]
fn weak_promotion_writes_control_block_not_holder_but_reset_and_swap_do() {
    assert!(!field_has_write(
        "struct State { std::weak_ptr<int> pointer; void use() { auto strong = pointer.lock(); } };",
        "State",
        "pointer"
    ));
    for ty in [
        "std::weak_ptr<int>",
        "std::shared_ptr<int>",
        "std::unique_ptr<int>",
    ] {
        for operation in ["pointer.reset()", "pointer.swap(other)", "pointer = other"] {
            let source = format!("struct State {{ {ty} pointer; void use() {{ {operation}; }} }};");
            assert!(field_has_write(&source, "State", "pointer"), "{source}");
        }
    }
    assert!(field_has_write(
        "struct State { std::mutex pointer; void use() { pointer.lock(); } };",
        "State",
        "pointer"
    ));
    assert!(field_has_write(
        "struct State { custom::weak_ptr<int> pointer; void use() { pointer.lock(); } };",
        "State",
        "pointer"
    ));
    assert!(field_has_write(
        "struct State { std::unique_ptr<int> pointer; void use() { auto raw = pointer.release(); } };",
        "State",
        "pointer"
    ));
}

#[test]
fn constructor_prefix_remains_unpublished_until_handoff_but_not_across_backedge() {
    let source = "struct State { int before; int after; State() {\nbefore++;\npublish(this);\nafter++;\n} };";
    assert!(!field_has_write(source, "State", "before"));
    assert!(field_has_write(source, "State", "after"));
    let source = "struct State { int counter; State() { while (again()) {\ncounter++;\npublish(this);\n} } };";
    assert!(field_has_write(source, "State", "counter"));
    let source = "struct State { int counter; State() { label:\ncounter++;\npublish(this);\ngoto label;\n} };";
    assert!(field_has_write(source, "State", "counter"));
    let source = "struct State { int before; int after; void initialize(); State() {\nbefore++;\ninitialize();\nafter++;\n} };";
    assert!(!field_has_write(source, "State", "before"));
    assert!(field_has_write(source, "State", "after"));
}

fn syntax_only_partitions(source: &str) -> Vec<Finding> {
    let files = parse_cpp_files(vec![CppFile {
        path: "candidate.hpp".into(),
        source: source.into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    let mut findings = apply_cpp_rules(
        &records,
        &facts,
        &[],
        &[],
        &[],
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    // Isolate source-derived function partitions from independent compiler /
    // reported-access capabilities accepted elsewhere by the pattern adapter.
    for finding in &mut findings {
        finding.access_evidence.clear();
    }
    retain_theory_candidates(&mut findings, &records, &facts);
    findings
}

#[test]
fn runtime_pointer_read_can_pair_with_peer_write_after_construction() {
    let findings = syntax_only_partitions(
        r#"
        class Connection {
            void* handle;
            void* headers;
        public:
            Connection() { handle = open(); headers = nullptr; }
            void inspect() { consume(handle); }
            void replace() { consume(handle); headers = build(); }
        };
        "#,
    );
    assert!(
        findings.iter().any(|finding| {
            finding
                .static_pattern
                .as_ref()
                .is_some_and(|witness| witness.access_pattern == AccessPattern::WriteRead)
        }),
        "{:#?}",
        findings
    );
}

#[test]
fn constructor_only_writes_do_not_make_runtime_read_pairs_writable() {
    let report = analyze(
        r#"
        class Connection {
            void* handle;
            void* headers;
        public:
            Connection() { handle = open(); headers = build(); }
            void inspect() { consume(handle); }
            void inspect_headers() { consume(handle); consume(headers); }
        };
        "#,
        CandidateKind::MixedFields,
    );
    assert!(report.findings.is_empty(), "{:#?}", report.findings);
}

#[test]
fn shared_actual_writes_do_not_create_read_only_access_partitions() {
    let findings = syntax_only_partitions(
        r#"
        class Connection {
            void* handle;
            void* headers;
        public:
            void reset() { handle = open(); }
            void replace() { handle = open(); headers = build(); }
        };
        "#,
    );
    assert!(findings.is_empty(), "{findings:#?}");
}

#[test]
fn pointer_template_arguments_do_not_turn_inline_maps_into_pointer_fields() {
    for ty in ["std::map<int, Value*>", "std::unordered_map<int, Value*>"] {
        let source = format!(
            "struct Value {{ int n; }};\nstruct Registry {{ {ty} slots;\nvoid assign(int key, Value* value) {{ slots[key] = value; }}\n}};"
        );
        assert!(field_has_write(&source, "Registry", "slots"), "{ty}");
    }
}

#[test]
fn map_subscript_can_insert_even_when_only_its_pointee_is_changed() {
    assert!(field_has_write(
        "struct Registry { std::map<int, Value*> slots;\nvoid assign(int key) { slots[key]->n = 1; }\n};",
        "Registry",
        "slots"
    ));
}

#[test]
fn heap_container_element_updates_are_not_control_block_writes() {
    for body in [
        "slots[key] = value;",
        "slots[key]->n = 1;",
        "(slots)[key] = value;",
    ] {
        let source = format!(
            "struct Registry {{ std::vector<Value*> slots;\nvoid assign(int key, Value* value) {{ {body} }}\n}};"
        );
        assert!(!field_has_write(&source, "Registry", "slots"), "{body}");
    }
}

#[test]
fn inline_pointer_and_atomic_pointer_array_slot_updates_are_writes() {
    for (ty, body) in [
        ("Value*", "slots[key] = value;"),
        ("std::atomic<Value*>", "slots[key].store(value);"),
        ("std::atomic<Value*>", "slots[key].exchange(value);"),
    ] {
        let source = format!(
            "struct Registry {{ {ty} slots[8];\nvoid assign(int key, Value* value) {{ {body} }}\n}};"
        );
        assert!(
            field_has_write(&source, "Registry", "slots"),
            "{ty}: {body}"
        );
    }
}

#[test]
fn inline_pointer_array_pointee_writes_are_not_slot_writes() {
    for (ty, body) in [
        ("Value*", "slots[key]->n = 1;"),
        ("int*", "slots[key][other] = 1;"),
        ("std::vector<int>", "slots[key][other] = 1;"),
    ] {
        let source = format!(
            "struct Registry {{ {ty} slots[8];\nvoid assign(int key, int other) {{ {body} }}\n}};"
        );
        assert!(
            !field_has_write(&source, "Registry", "slots"),
            "{ty}: {body}"
        );
    }
}

#[test]
fn standard_array_slots_and_small_string_storage_remain_inline() {
    for (ty, body, written) in [
        ("std::array<Value*, 8>", "slots[key] = value;", true),
        ("std::array<Value*, 8>", "slots[key][other] = value;", false),
        (
            "std::array<std::vector<int>, 8>",
            "slots[key][other] = 1;",
            false,
        ),
        ("std::string", "slots[key] = 'x';", true),
    ] {
        let source = format!(
            "struct Registry {{ {ty} slots;\nvoid assign(int key, int other, Value* value) {{ {body} }}\n}};"
        );
        assert_eq!(
            field_has_write(&source, "Registry", "slots"),
            written,
            "{ty}: {body}"
        );
    }
}

#[test]
fn nested_out_of_line_method_binds_innermost_record() {
    let source = r#"
        class Outer {
            int slots[8];
        public:
            class Batch {
                int slots[8];
            public:
                void assign(int key);
            };
            int read(int key) { return slots[key]; }
        };
        void Outer::Batch::assign(int key) { slots[key] = 1; }
    "#;
    assert!(field_has_write(source, "Batch", "slots"));
    assert!(!field_has_write(source, "Outer", "slots"));
}

#[test]
fn nested_same_named_field_does_not_hide_a_real_outer_slot_mutation() {
    let source = r#"
        class Outer {
            std::atomic<Value*> slots[8];
        public:
            class Batch {
                Value* slots[8];
            public:
                void assign(int key, Value* value);
            };
            void publish(int key, Value* value);
        };
        void Outer::Batch::assign(int key, Value* value) { slots[key] = value; }
        void Outer::publish(int key, Value* value) { slots[key].store(value); }
    "#;
    assert!(field_has_write(source, "Batch", "slots"));
    assert!(field_has_write(source, "Outer", "slots"));
}

#[test]
fn destructor_stop_before_join_is_not_unpublished_initialization() {
    for destructor in [
        "~Worker() { stop.store(true); background.join(); }",
        "~Worker();",
    ] {
        let out_of_line = if destructor.ends_with(';') {
            "Worker::~Worker() { stop.store(true); background.join(); }"
        } else {
            ""
        };
        let source = format!(
            "struct Worker {{ std::atomic<bool> stop; std::thread background;\nWorker() {{ stop.store(false); }}\n{destructor}\nvoid start() {{ background = std::thread([this] {{ while (!stop.load()) work(); }}); }}\n}};\n{out_of_line}"
        );
        let facts = evidence(&source);
        let worker = facts.iter().find(|(name, _)| name == "Worker").unwrap();
        assert!(worker.1.items.iter().any(|item| {
            item.field_name.as_deref() == Some("stop")
                && item.initialization_phase
                && item.description.contains("stop.store(false)")
        }));
        assert!(worker.1.items.iter().any(|item| {
            item.field_name.as_deref() == Some("stop")
                && !item.initialization_phase
                && item.access_kind == Some(CppAccessKind::Write)
                && item.description.contains("stop.store(true)")
        }));
    }
}

#[test]
fn qualified_nested_owner_ignores_same_named_records_in_other_namespaces() {
    let facts = evidence(
        r#"
        namespace first {
            class Outer {
                int slots[8];
            public:
                class Batch { int slots[8]; public: void assign(int key); };
            };
        }
        namespace second { class Batch { int slots[8]; }; }
        void first::Outer::Batch::assign(int key) { slots[key] = 1; }
        "#,
    );
    let writers = facts
        .iter()
        .filter(|(_, facts)| {
            facts.items.iter().any(|item| {
                item.field_name.as_deref() == Some("slots")
                    && item.access_kind == Some(CppAccessKind::Write)
            })
        })
        .map(|(name, _)| name.as_str())
        .collect::<Vec<_>>();
    assert_eq!(writers, ["Batch"]);
}

#[test]
fn c11_explicit_atomic_calls_preserve_exact_target_reads_and_writes() {
    for (call, expected) in [
        ("atomic_load(&value->target)", CppAccessKind::Read),
        (
            "atomic_load_explicit(&value->target, relaxed)",
            CppAccessKind::Read,
        ),
        (
            "atomic_store_explicit(&value->target, value->desired, relaxed)",
            CppAccessKind::Write,
        ),
        (
            "atomic_fetch_add_explicit(&value->target, value->desired, relaxed)",
            CppAccessKind::ReadModifyWrite,
        ),
        (
            "atomic_flag_test_and_set_explicit(&value->target, relaxed)",
            CppAccessKind::ReadModifyWrite,
        ),
    ] {
        let source = format!(
            "struct State {{ atomic_int target; int desired; }};\nvoid update(State* value) {{ {call}; }}"
        );
        let facts = evidence(&source);
        let items = &facts[0].1.items;
        assert!(
            items
                .iter()
                .any(|item| item.field_name.as_deref() == Some("target")
                    && item.access_kind.as_ref() == Some(&expected)),
            "{call}: {items:#?}"
        );
        assert!(
            !items
                .iter()
                .any(|item| item.field_name.as_deref() == Some("desired")
                    && matches!(
                        item.access_kind,
                        Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                    )),
            "{call}: {items:#?}"
        );
    }
}

#[test]
fn atomic_compare_exchange_expected_and_desired_have_distinct_argument_roles() {
    for call in [
        "atomic_compare_exchange_weak_explicit(&value->target, &value->expected, value->desired, success, failure)",
        "__atomic_compare_exchange(&value->target, &value->expected, &value->desired, false, success, failure)",
    ] {
        let source = format!(
            "struct State {{ atomic_int target; int expected; int desired; }};\nvoid update(State* value) {{ {call}; }}"
        );
        let facts = evidence(&source);
        for field in ["target", "expected"] {
            assert!(
                facts[0]
                    .1
                    .items
                    .iter()
                    .any(|item| item.field_name.as_deref() == Some(field)
                        && item.access_kind == Some(CppAccessKind::ReadModifyWrite)),
                "{call}: {facts:#?}"
            );
        }
        assert!(
            facts[0]
                .1
                .items
                .iter()
                .any(|item| item.field_name.as_deref() == Some("desired")
                    && item.access_kind == Some(CppAccessKind::Read)),
            "{call}: {facts:#?}"
        );
        assert!(
            !facts[0]
                .1
                .items
                .iter()
                .any(|item| item.field_name.as_deref() == Some("desired")
                    && matches!(
                        item.access_kind,
                        Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                    ))
        );
    }
}

#[test]
fn unknown_atomic_named_call_is_not_a_memory_access_summary() {
    let facts = evidence(
        "struct State { int target; };\nvoid update(State* value) { atomic_diagnostic(&value->target); }",
    );
    assert!(
        facts[0]
            .1
            .items
            .iter()
            .all(|item| item.access_kind.is_none()),
        "{facts:#?}"
    );
}

#[test]
fn syntax_recovery_with_a_comment_cannot_erase_the_fallback_access_row() {
    for comment in ["", "/* harmless comment */"] {
        let report = analyze(
            &format!(
                "struct Counters {{ int hits; int misses; }};\n#define ANNOTATE\nvoid first(Counters* value) {{\nANNOTATE value->hits += 1; {comment}\n}}\nvoid second(Counters* value) {{ value->misses += 1; }}"
            ),
            CandidateKind::FieldGroup,
        );
        assert!(!report.findings.is_empty(), "{comment}: {report:#?}");
        assert!(
            report.analysis_incomplete,
            "syntax recovery must remain visible"
        );
    }
}

#[test]
fn recovered_nested_method_uses_the_same_innermost_owner_as_exact_syntax() {
    let source = r#"
        #define ANNOTATE
        class Outer {
            int hits;
        public:
            class Batch { int hits; public: void assign(int key); };
        };
        void Outer::Batch::assign(int key) {
            ANNOTATE this->hits += 1; /* recovered prefix macro */
        }
    "#;
    assert!(field_has_write(source, "Batch", "hits"));
    assert!(!field_has_write(source, "Outer", "hits"));
}
