use false_sharing_detector::types::RuleId;
use std::fs;

use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
use false_sharing_detector::cpp_detection::evidence::collect_cpp_evidence;
use false_sharing_detector::cpp_detection::layout::collect_cpp_structs;
use false_sharing_detector::cpp_detection::parser::parse_cpp_files;
use false_sharing_detector::cpp_detection::types::{CppEvidenceKind, CppFile};
use false_sharing_detector::types::{AnalysisOptions, CandidateKind};
use tempfile::tempdir;

#[test]
fn counter_container_names_do_not_suppress_element_record_risks() {
    for field in ["payload", "counter_data"] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("record.cpp"), format!("#include <atomic>\n#include <vector>\n#include <thread>\nstruct Cell {{ std::atomic<int> first; std::atomic<int> second; }};\nstruct Owner {{ std::vector<Cell> {field}; }};\nvoid one(Cell *c) {{ c->first.fetch_add(1); }}\nvoid two(Cell *c) {{ c->second.fetch_add(1); }}\nvoid run(Cell *c) {{
std::thread a(one,c);
std::thread b(two,c);
 a.join(); b.join(); }}")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert!(
            report
                .findings
                .iter()
                .any(|finding| finding.struct_name.as_deref() == Some("Cell")),
            "{report:#?}"
        );
    }
}

#[test]
fn wrapper_type_names_do_not_supply_alignment() {
    for name in ["Word", "CacheLineWord", "CachePaddedWord"] {
        for (alignment, protected) in [("", false), ("alignas(128)", true)] {
            let root = tempdir().unwrap();
            fs::write(root.path().join("record.cpp"), format!("#include <atomic>\n#include <thread>\nstruct {alignment} {name} {{ std::atomic<int> value; }};\nstruct Data {{ {name} first; {name} second; }};\nvoid one(Data *c) {{ c->first.value.fetch_add(1); }}\nvoid two(Data *c) {{ c->second.value.fetch_add(1); }}\nvoid run(Data *c) {{
std::thread a(one,c);
std::thread b(two,c);
 a.join(); b.join(); }}")).unwrap();
            for block in [32, 64, 128] {
                let options = AnalysisOptions {
                    cache_line_size: block,
                    ..AnalysisOptions::with_rules(&[RuleId::SameObjectFields])
                };
                let report = analyze_cpp_path_with_options(root.path(), &options);
                assert_eq!(
                    report.findings.is_empty(),
                    protected,
                    "{name}, B={block}: {report:#?}"
                );
            }
        }
    }
}

#[test]
fn allocation_topology_does_not_require_thread_state_names() {
    for name in ["ThreadState", "Record"] {
        for allocated in [false, true] {
            let root = tempdir().unwrap();
            let storage = if allocated {
                format!("{name} *a = new {name}{{}}; {name} *b = new {name}{{}};")
            } else {
                format!("{name} first, second; {name} *a = &first; {name} *b = &second;")
            };
            fs::write(root.path().join("record.cpp"), format!("#include <atomic>\n#include <thread>\nstruct {name} {{ std::atomic<int> state; }};\nvoid work({name} *c) {{ c->state.fetch_add(1); }}\nvoid run() {{ {storage}
std::thread x(work,a);
std::thread y(work,b);
 x.join(); y.join(); }}")).unwrap();
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions::with_rules(&[RuleId::IndependentAllocations]),
            );
            assert_eq!(!report.findings.is_empty(), allocated, "{report:#?}");
        }
    }
}

#[test]
fn automatic_objects_with_unknown_escape_do_not_borrow_enclosing_parallelism() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("local.hpp"), "struct State { int count_left; int count_right; };\nvoid read(State& s) { consume(s.count_left); }\nstd::shared_ptr<State> external;\nvoid run() {\n#pragma omp parallel for\nfor(int i=0;i<32;++i) {\nState local;\nlocal.count_right++;\nread(local);\n}\n}\n").unwrap();
    let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let normal = analyze_cpp_path_with_options(root.path(), &options);
    assert!(normal.findings.is_empty(), "{normal:#?}");
    let source = fs::read_to_string(root.path().join("local.hpp")).unwrap();
    let files = parse_cpp_files(vec![CppFile {
        path: "local.hpp".into(),
        source,
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    assert!(
        facts
            .iter()
            .flat_map(|f| &f.items)
            .any(|e| e.through_automatic_receiver
                && !e.through_nonescaping_local
                && e.field_name.as_deref() == Some("count_right"))
    );
}

#[test]
fn parallel_read_does_not_make_serial_container_updates_concurrent() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("phase.hpp"), "struct State { std::vector<int> left; std::vector<int> right;\nvoid prepare() { left.push_back(1); }\nvoid inspect() {\n#pragma omp parallel for\nfor(int i=0;i<16;++i) { consume(right[i]); }\n}\n};\n").unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    let normal = analyze_cpp_path_with_options(root.path(), &options);
    assert!(normal.findings.is_empty(), "{normal:#?}");
    options.cpp_include_speculative = true;
    assert!(
        !analyze_cpp_path_with_options(root.path(), &options)
            .findings
            .is_empty()
    );
}

#[test]
fn adjacent_objects_require_concurrency_on_the_plain_writer() {
    for block in [32, 64, 128] {
        for (member, serial, parallel, expected) in [
            ("int count;", "count++;", "consume(items[i].count);", false),
            ("int count;", "count++;", "items[i].count++;", true),
            (
                "std::atomic<int> count;",
                "count.fetch_add(1);",
                "consume(items[i].count.load());",
                true,
            ),
        ] {
            let root = tempdir().unwrap();
            fs::write(root.path().join("objects.hpp"), format!(
                "struct Entry {{ {member} void update() {{ {serial} }} }};\nEntry items[32];\nvoid run() {{\n#pragma omp parallel for\nfor(int i=0;i<32;++i) {{ {parallel} }}\n}}\n"
            )).unwrap();
            let mut options = AnalysisOptions {
                cache_line_size: block,
                ..AnalysisOptions::with_rules(&[
                    RuleId::ContiguousElements,
                    RuleId::IndependentAllocations,
                ])
            };
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "B={block} {member} {parallel}: {report:#?}"
            );
            options.cpp_include_speculative = true;
            assert!(
                !analyze_cpp_path_with_options(root.path(), &options)
                    .findings
                    .is_empty(),
                "unresolved ordinary API writes remain may-risk: B={block} {member}"
            );
        }
    }
}

#[test]
fn same_bitfield_location_is_excluded_without_hiding_other_field_pairs() {
    for block in [32, 64, 128] {
        for (members, expected) in [
            (
                "unsigned int count_left:1; unsigned int count_right:1;",
                false,
            ),
            ("unsigned int count_left; unsigned int count_right;", true),
            (
                "unsigned int count_left:1; unsigned int :0; unsigned int count_right:1;",
                true,
            ),
        ] {
            let root = tempdir().unwrap();
            fs::write(root.path().join("state.hpp"), format!(
                "struct State {{ {members}\nvoid left() {{ for(int i=0;i<100;++i) count_left++; }}\nvoid right() {{ for(int i=0;i<100;++i) count_right++; }}\n}};\nstd::shared_ptr<State> shared_state;\n"
            )).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
            options.cache_line_size = block;
            options.cpp_include_speculative = true;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "B={block}: {members}\n{report:#?}"
            );
        }
        let root = tempdir().unwrap();
        fs::write(root.path().join("state.hpp"), "struct State {\nstd::atomic<int> counter;\nunsigned int left:1, right:1;\nvoid write() { counter.fetch_add(1); }\nint read_left() { return left; }\nint read_right() { return right; }\n};\n").unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
        options.cache_line_size = block;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert!(!report.findings.is_empty(), "B={block}: {report:#?}");
        assert!(
            report
                .findings
                .iter()
                .all(|f| f.field_list.iter().any(|s| s == "counter")),
            "{report:#?}"
        );
    }
}

#[test]
fn direct_reference_getters_bind_reads_and_writes_to_the_caller() {
    for (tail, expected, caller_kind) in [
        ("", false, None),
        ("void observe(State &s) { s.view(); }", false, None),
        (
            "int observe(State &s) { return s.view(); }",
            true,
            Some("read"),
        ),
        (
            "void observe(State &s) { s.view()++; }",
            true,
            Some("read_modify_write"),
        ),
        // Alias effects are not yet recovered: retain the conservative source
        // evidence rather than dropping this real read.
        (
            "int observe(State &s) { int &r = s.view(); return r; }",
            true,
            None,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("state.hpp"), "struct State { std::atomic<int> counter; int value;\n int &view() { return value; }\n void update() { counter.fetch_add(1); }\n};\n").unwrap();
        fs::write(
            root.path().join("use.cpp"),
            format!("#include \"state.hpp\"\n{tail}\n"),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(!report.findings.is_empty(), expected, "{tail}");
        if let Some(kind) = caller_kind {
            let evidence = report
                .findings
                .iter()
                .flat_map(|f| &f.access_evidence)
                .collect::<Vec<_>>();
            assert!(
                evidence
                    .iter()
                    .any(|a| a.function_name.as_deref() == Some("observe")
                        && a.field_name.as_deref() == Some("value")
                        && a.access_kind.as_deref() == Some(kind)),
                "caller effect: {tail}"
            );
            assert!(
                !evidence
                    .iter()
                    .any(|a| a.function_name.as_deref() == Some("view")
                        && a.field_name.as_deref() == Some("value")),
                "getter only forms a reference: {tail}"
            );
        }
    }
}

#[test]
fn unresolved_reference_getter_uses_keep_conservative_evidence() {
    for (getters, use_site) in [
        (
            "int &view() { return value; }",
            "template<class T> int read(T &s) { return s.view(); }",
        ),
        (
            "int &view() { return value; } auto callback() { return &State::view; }",
            "",
        ),
        ("virtual int &view() { return value; }", ""),
        ("virtual/*modifier*/ int &view() { return value; }", ""),
        (
            "int &view() { return value; } const int &view() const { return value; }",
            "",
        ),
        (
            "int &view() { return value; }",
            "#define BORROW(s) s.view()\n",
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("state.hpp"), format!("struct State {{ std::atomic<int> counter; int value; {getters} void update() {{ counter.fetch_add(1); }} }};\n{use_site}\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert!(!report.findings.is_empty(), "{getters}: {use_site}");
    }
}

#[test]
fn mutation_through_an_atomic_reference_getter_is_a_real_writer() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("state.hpp"),
        r#"
struct State {
    std::atomic<int> counter;
    int value;
    std::atomic<int> &slot() { return counter; }
    int read() { return value; }
};
void mutate(State &s) { s.slot().fetch_add(1); }
"#,
    )
    .unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(!report.findings.is_empty());
    assert!(report.findings.iter().flat_map(|f| &f.access_evidence).any(
        |a| a.field_name.as_deref() == Some("counter")
            && a.function_name.as_deref() == Some("mutate")
            && a.access_kind.as_deref() == Some("read_modify_write")
    ));
}

#[test]
fn locking_through_a_mutex_reference_getter_preserves_acquisition_semantics() {
    for (guard, expected) in [
        ("std::lock_guard<std::mutex> guard(s.gate());", true),
        (
            "std::unique_lock<std::mutex> guard(s.gate(), std::defer_lock);",
            false,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("state.hpp"),
            format!(
                r#"
struct State {{
    std::mutex mutex;
    int value;
    std::mutex &gate() {{ return mutex; }}
    int read() {{ return value; }}
}};
void acquire(State &s) {{ {guard} }}
"#
            ),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(!report.findings.is_empty(), expected, "{guard}");
    }
}

#[test]
fn a_template_parameter_cannot_bind_a_same_named_concrete_reference_getter() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("state.hpp"),
        r#"
struct State {
    std::atomic<int> counter;
    int value;
    int &view() { return value; }
    void update() { counter.fetch_add(1); }
};
template<class State> int observe(State &s) { return s.view(); }
"#,
    )
    .unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    let accesses = report
        .findings
        .iter()
        .flat_map(|f| &f.access_evidence)
        .collect::<Vec<_>>();
    assert!(
        accesses
            .iter()
            .any(|a| a.function_name.as_deref() == Some("view"))
    );
    assert!(
        !accesses
            .iter()
            .any(|a| a.function_name.as_deref() == Some("observe")
                && a.field_name.as_deref() == Some("value"))
    );
}

#[test]
fn inline_array_address_formation_is_not_an_element_read() {
    for (reader, expected) in [
        ("int *read() { return slots; }", false),
        ("int *read() { return (slots); }", false),
        ("void read() { int *p = slots; }", false),
        ("void read() { auto p = slots; }", false),
        ("int read() { return slots[0]; }", true),
        ("int read() { return *slots; }", true),
        ("int read() { int *p = slots; return p[0]; }", true),
        ("View read() { return slots; }", true),
        ("void read() { View copy = slots; }", true),
        ("int read() { auto [a,b] = slots; return a; }", true),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("state.hpp"), format!(
            "struct View {{ View(const int *p) {{ consume(p[0]); }} }}; struct State {{ std::atomic<int> counter; int slots[2]; void update() {{ counter.fetch_add(1); }} {reader} }};"
        )).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(!report.findings.is_empty(), expected, "{reader}");
    }
}

#[test]
fn address_formation_preserves_pointer_index_and_dereference_reads() {
    for (reader, expected_fields) in [
        ("int *read() { return &value; }", vec![]),
        ("int **read() { return &pointer; }", vec![]),
        ("int *read() { return &slots[0]; }", vec![]),
        ("int *read() { return &*slots; }", vec![]),
        ("int *read() { return &*(&value); }", vec![]),
        ("int *read() { return &(&value)[0]; }", vec![]),
        ("int *read() { return &slots[index]; }", vec!["index"]),
        (
            "int *read() { return &pointer[index]; }",
            vec!["pointer", "index"],
        ),
        ("int read() { return *(&value); }", vec!["value"]),
        ("int read() { return (&value)[0]; }", vec!["value"]),
    ] {
        let files = parse_cpp_files(vec![CppFile {
            path: "address.hpp".into(),
            source: format!(
                "struct State {{ int value; int *pointer; int index; int slots[4]; {reader} }};"
            ),
        }]);
        let records = collect_cpp_structs(&files, "address", 64);
        let evidence = collect_cpp_evidence(&files, &records);
        let actual = evidence
            .iter()
            .flat_map(|e| &e.items)
            .filter(|item| {
                item.access_kind.is_some() && item.function_name.as_deref() == Some("read")
            })
            .filter_map(|item| item.field_name.as_deref())
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(actual, expected_fields.into_iter().collect(), "{reader}");
    }
}

#[test]
fn allocation_risk_cannot_borrow_repetition_only_from_a_reader() {
    for (write, expected) in [("store(0)", false), ("fetch_add(1)", true)] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("state.hpp"),
            format!(
                r#"
            struct State {{ std::atomic<int> thread_index; }};
            void change(State *s) {{ s->thread_index.{write}; }}
            void launch() {{
                auto s = std::make_shared<State>();
                std::thread worker([s] {{ while (s->thread_index.load()) {{}} }});
                change(s.get());
                worker.join();
            }}
        "#
            ),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::IndependentAllocations]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("State")),
            expected,
            "{write}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn anonymous_namespace_keeps_exact_member_and_construction_ownership() {
    let files = parse_cpp_files(vec![CppFile {
        path: "anonymous.cpp".into(),
        source: "namespace Outer { namespace { struct State { std::atomic<int> counter; State() { counter.store(0); } void update() { counter.fetch_add(1); } }; } }".into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    assert_eq!(records[0].qualified_name, "Outer::State");
    assert!(facts[0].items.iter().any(|a| a.function_name.as_deref() == Some("update") && a.access_kind == Some(false_sharing_detector::cpp_detection::types::CppAccessKind::ReadModifyWrite) && !a.in_record_constructor));
    assert!(
        facts[0]
            .items
            .iter()
            .any(|a| a.function_name.as_deref() == Some("State")
                && a.initialization_phase
                && a.in_record_constructor)
    );
}

#[test]
fn cross_file_api_type_references_require_matching_lexical_scope() {
    for (path, prefix, suffix, reference, expected_api) in [
        (
            "state.cpp",
            "",
            "",
            "struct State; void observe(State &value);",
            true,
        ),
        ("state.hpp", "", "", "void observe(State &value);", true),
        (
            "state.cpp",
            "",
            "",
            "void observe(int State, int &value);",
            false,
        ),
        (
            "state.cpp",
            "struct Outer {",
            "};",
            "struct State {}; void observe(State &value);",
            false,
        ),
        (
            "state.hpp",
            "namespace A {",
            "}",
            "namespace B { void observe(State &value); }",
            false,
        ),
        (
            "state.hpp",
            "namespace A {",
            "}",
            "namespace A { void observe(State &value); }",
            true,
        ),
        (
            "state.hpp",
            "namespace A {",
            "}",
            "void observe(A::State &value);",
            true,
        ),
        (
            "state.hpp",
            "namespace A {",
            "}",
            "namespace B { void observe(::A::State &value); }",
            true,
        ),
        (
            "state.hpp",
            "namespace A {",
            "}",
            "namespace A {} namespace B { void observe(State &value); }",
            false,
        ),
    ] {
        let files = parse_cpp_files(vec![
            CppFile {
                path: path.into(),
                source: format!(
                    "{prefix} struct State {{ std::atomic<int> count; int payload; }}; {suffix}"
                ),
            },
            CppFile {
                path: "other.cpp".into(),
                source: reference.into(),
            },
        ]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        let index = records
            .iter()
            .position(|record| record.name == "State")
            .unwrap();
        assert_eq!(
            facts[index]
                .api_items
                .iter()
                .any(|item| item.file == "other.cpp"),
            expected_api,
            "{path} {prefix} {reference}: {:#?}",
            facts[index]
        );
    }
}

#[test]
fn opaque_type_api_preserves_risk_but_unrelated_nested_name_does_not() {
    for (prefix, suffix, expected) in [("", "", true), ("struct Owner {", "};", false)] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("state.cpp"), format!(
            "{prefix}\nstruct State {{\nstd::atomic<int> count;\nint payload;\nvoid update() {{ count.fetch_add(1); }}\nvoid set(int value) {{ payload = value; }}\n}};\n{suffix}"
        )).unwrap();
        fs::write(
            root.path().join("api.hpp"),
            "struct State;\nvoid Poll(State &value);\n",
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|finding| finding.struct_name.as_deref() == Some("State")),
            expected,
            "{prefix}: {report:#?}"
        );
    }
}

#[test]
fn raii_guard_acquisition_is_a_mutex_write_not_a_pointer_slot_write() {
    for (member, statement, expected) in [
        ("std::mutex mutex;", "std::lock_guard guard(s.mutex);", true),
        ("std::mutex mutex;", "lock_guard guard(s.mutex);", true),
        (
            "std::shared_mutex mutex;",
            "std::shared_lock guard(s.mutex);",
            true,
        ),
        (
            "std::shared_mutex mutex;",
            "std::shared_lock<std::shared_mutex> guard{s.mutex};",
            true,
        ),
        (
            "std::shared_mutex mutex;",
            "std::shared_lock guard(s.mutex, std::defer_lock);",
            false,
        ),
        (
            "std::shared_mutex mutex;",
            "std::shared_lock guard(s.mutex, std::adopt_lock);",
            false,
        ),
        (
            "std::shared_mutex *mutex;",
            "std::shared_lock guard(*s.mutex);",
            false,
        ),
        (
            "std::shared_mutex &mutex;",
            "std::shared_lock guard(s.mutex);",
            false,
        ),
        (
            "std::shared_mutex mutex;",
            "custom::shared_lock guard(s.mutex);",
            false,
        ),
        (
            "std::mutex mutex;",
            "std::unique_lock<std::mutex> guard{s.mutex};",
            true,
        ),
        (
            "std::mutex mutex;",
            "std::unique_lock guard(s.mutex, std::defer_lock);",
            false,
        ),
        ("std::mutex mutex;", "consume(s.mutex);", false),
        (
            "std::mutex *mutex;",
            "std::lock_guard guard(*s.mutex);",
            false,
        ),
    ] {
        let source = format!(
            "struct State {{ {member} int peer; }};\nvoid work(State& s) {{ {statement} }}\nstd::vector<State> states;"
        );
        let files = parse_cpp_files(vec![CppFile {
            path: "guard.hpp".into(),
            source: source.clone(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        assert_eq!(facts[0].items.iter().any(|a| a.field_name.as_deref() == Some("mutex") && a.access_kind == Some(false_sharing_detector::cpp_detection::types::CppAccessKind::ReadModifyWrite)), expected, "{statement}: {:?}", facts[0]);
        let root = tempdir().unwrap();
        fs::write(root.path().join("guard.hpp"), source).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[
                RuleId::ContiguousElements,
                RuleId::IndependentAllocations,
            ]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("State")),
            expected,
            "{statement}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn unqualified_most_vexing_guard_binds_the_mutex_member() {
    let files = parse_cpp_files(vec![CppFile {
        path: "guard.hpp".into(),
        source: r#"
using std::lock_guard;
struct State {
    std::mutex mutex;
    int peer;
    void work() { lock_guard lock(mutex); }
};
"#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    assert!(facts[0].items.iter().any(|item| {
        item.field_name.as_deref() == Some("mutex")
            && item.access_kind
                == Some(
                    false_sharing_detector::cpp_detection::types::CppAccessKind::ReadModifyWrite,
                )
    }));
}

#[test]
fn shared_guard_updates_parent_mutex_without_serializing_shared_holders() {
    let files = parse_cpp_files(vec![CppFile {
        path: "parent.hpp".into(),
        source: r#"
struct Parent {
    std::shared_mutex gate;
    std::atomic<int> count;
    int peer;
};
struct Child {
    Parent *parent;
    std::atomic<bool> initialized;
    void prepare() {
        if (initialized.load()) return;
        std::shared_lock guard(parent->gate);
        parent->count.fetch_add(1);
        initialized.store(true);
    }
};
"#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    let parent = records.iter().position(|r| r.name == "Parent").unwrap();
    let accesses = &facts[parent].items;
    assert!(accesses.iter().any(|a|
        a.field_name.as_deref() == Some("gate")
        && a.access_kind == Some(false_sharing_detector::cpp_detection::types::CppAccessKind::ReadModifyWrite)
        && a.through_raw_pointer
        && !a.initialization_phase));
    // Multiple children can share the parent. Shared ownership neither makes
    // the parent's lock a once-only initialization nor serializes its holders.
    assert!(accesses.iter().any(|a|
        a.field_name.as_deref() == Some("count")
        && a.access_kind == Some(false_sharing_detector::cpp_detection::types::CppAccessKind::ReadModifyWrite)
        && a.guard_ids.is_empty()));
}

#[test]
fn adjacent_object_sync_evidence_must_belong_to_a_written_field() {
    for (write, expected) in [
        ("value++;", false),
        ("flag.fetch_add(1);", true),
        (
            "\n#pragma omp parallel for\nfor (int i=0; i<32; ++i) { value++; }\n",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("state.hpp"), format!("struct State {{ std::atomic<int> flag; int value; void update() {{ {write} }} }};\nstd::vector<State> states;\n")).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[
                RuleId::ContiguousElements,
                RuleId::IndependentAllocations,
            ]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("State")),
            expected,
            "{write}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn nested_namespace_spelling_preserves_layout_and_member_identity() {
    let files = parse_cpp_files(vec![CppFile {
        path: "nested_namespace.hpp".into(),
        source: "namespace outer::inner { struct State { std::atomic<int> counter; void *peer; void update() { counter.fetch_add(1); } }; }\nstruct Wrapper { outer::inner::State item; };".into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let index = records.iter().position(|r| r.name == "State").unwrap();
    assert_eq!(records[index].qualified_name, "outer::inner::State");
    let facts = collect_cpp_evidence(&files, &records);
    assert!(facts[index].items.iter().any(|a| a.field_name.as_deref() == Some("counter") && a.access_kind == Some(false_sharing_detector::cpp_detection::types::CppAccessKind::ReadModifyWrite)));
    let wrapper = records.iter().find(|r| r.name == "Wrapper").unwrap();
    assert!(wrapper.fields[0].is_hot_sync);
}

#[test]
fn embedded_layout_summary_requires_matching_qualified_type() {
    for (inner, property) in [
        ("struct Item { std::atomic<int> count; };", "sync"),
        ("struct alignas(64) Item { long count; };", "alignment"),
    ] {
        let files = parse_cpp_files(vec![CppFile {
            path: "qualified_layout.hpp".into(),
            source: format!(
                "namespace Actual {{ {inner} }}\nstruct Known {{ Actual::Item item; }};\nstruct Unknown {{ Missing::Item item; }};\nstruct Nested {{ Unknown item; }};"
            ),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let field = |name| &records.iter().find(|r| r.name == name).unwrap().fields[0];
        assert!(!field("Unknown").is_hot_sync, "{property}");
        assert!(!field("Unknown").is_cache_padded, "{property}");
        assert_eq!(field("Unknown").estimated_size, None, "{property}");
        assert!(!field("Nested").is_hot_sync, "{property}");
        if property == "sync" {
            assert!(field("Known").is_hot_sync);
        } else {
            assert!(field("Known").is_cache_padded);
            assert_eq!(field("Known").estimated_size, Some(64));
        }
    }
}

#[test]
fn construction_source_rmw_needs_independent_repetition_evidence() {
    for (constructor, runtime, expected) in [
        (
            "State(State&& src) : writer(src.writer.exchange(0)), reader(0) {}",
            "",
            false,
        ),
        (
            "State(State&& src) : writer(src.writer.exchange(0)), reader(0) {}",
            "void update() { writer.fetch_add(1); }",
            true,
        ),
        (
            "State(State&& src) : writer(0), reader(0) { for (int i=0; i<100; ++i) { src.writer.fetch_add(1); } }",
            "",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        let source = format!(
            "struct State {{ std::atomic<int> writer; void *reader;\n{constructor}\n{runtime}\nvoid *observe() {{ return reader; }}\n}};"
        );
        fs::write(root.path().join("state.hpp"), &source).unwrap();
        let files = parse_cpp_files(vec![CppFile {
            path: "state.hpp".into(),
            source,
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        assert!(facts[0].items.iter().any(|a| a.field_name.as_deref() == Some("writer") && a.access_kind == Some(false_sharing_detector::cpp_detection::types::CppAccessKind::ReadModifyWrite) && !a.initialization_phase), "source-object mutation must not be reclassified as fresh initialization");
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("State")),
            expected,
            "{constructor} / {runtime}: {:#?}",
            report.findings
        );
    }
}

#[test]
fn local_callback_guard_proof_removes_only_the_fully_guarded_pair() {
    for (extra_call, expected) in [("", false), ("change();", true)] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("candidate.hpp"),
            format!(
                r#"
            std::mutex mutex;
            struct State {{ std::atomic<int> counter; void *peer; }};
            void update(State& state) {{
                auto change = [&] {{
                    state.counter++;
                }};
                {{
                    std::lock_guard guard(mutex);
                    change();
                }}
                {extra_call}
            }}
            void *observe(State& state) {{
                std::lock_guard guard(mutex);
                return state.peer;
            }}
        "#
            ),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("State")),
            expected,
            "extra_call={extra_call}, findings={:#?}",
            report.findings
        );
    }
}

#[test]
fn embedded_size_propagation_preserves_internal_and_trailing_padding() {
    let files = parse_cpp_files(vec![CppFile {
        path: "embedded.hpp".into(),
        source: r#"
            struct Inner { char first; uint64_t word; char last; };
            struct Middle { Inner inner; char tail; };
            struct Outer { Middle middle; uint64_t next; };
        "#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let inner = records.iter().find(|r| r.name == "Inner").unwrap();
    let middle = records.iter().find(|r| r.name == "Middle").unwrap();
    let outer = records.iter().find(|r| r.name == "Outer").unwrap();
    assert_eq!(inner.total_estimated_size, Some(24));
    assert_eq!(middle.fields[0].estimated_size, Some(24));
    assert_eq!(middle.total_estimated_size, Some(32));
    assert_eq!(outer.fields[0].estimated_size, Some(32));
    assert_eq!(outer.fields[1].offset, Some(32));
    assert_eq!(outer.total_estimated_size, Some(40));

    for (members, expected) in [
        ("Inner one;", true),
        ("Inner one; Inner two; Inner three;", false),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("candidate.hpp"),
            format!(
                "struct Inner {{ char first; uint64_t word; char last; }};\n\
             struct Bridge {{ {members} }};\n\
             struct Target {{ std::atomic<int> writer; Bridge gap; void *reader;\n\
             void update() {{ writer.fetch_add(1); }}\n\
             void *observe() {{ return reader; }}\n}};"
            ),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("Target")),
            expected,
            "members={members}, findings={:#?}",
            report.findings
        );
    }
}

#[test]
fn memset_address_does_not_publish_value_storage_but_pointer_rebinding_still_ends_freshness() {
    use false_sharing_detector::cpp_detection::initialization::collect_initialization_facts;
    for (declaration, call, expected) in [
        ("State object;", "memset(&object, 0, sizeof(object));", true),
        (
            "State object;",
            "std::memset((&object), 0, sizeof(object));",
            true,
        ),
        ("State object;", "publish(&object);", false),
        (
            "State object;",
            "vendor::memset(&object, 0, sizeof(object));",
            false,
        ),
        (
            "State object;",
            "saved = memset(&object, 0, sizeof(object));",
            false,
        ),
        (
            "State *object = malloc(sizeof(State));",
            "memset(&object, 0, sizeof(object));",
            false,
        ),
        (
            "State *object = malloc(sizeof(State));",
            "memset(&object->count, 0, sizeof(object->count));",
            true,
        ),
    ] {
        let pointer = declaration.contains('*');
        let mutation = if pointer {
            "object->count++;"
        } else {
            "object.count++;"
        };
        let source = format!(
            "struct State {{ int count; }};\nvoid *saved;\nvoid run() {{\n{declaration}\n{call}\n{mutation}\n}}"
        );
        let offset = source.find(mutation).unwrap();
        let files = parse_cpp_files(vec![CppFile {
            path: "memory.cpp".into(),
            source,
        }]);
        let ranges = collect_initialization_facts(&files);
        let covered = ranges["memory.cpp"]
            .iter()
            .any(|range| range.receiver == "object" && range.begin <= offset && offset < range.end);
        assert_eq!(covered, expected, "call={call}, ranges={ranges:#?}");
    }
}

#[test]
fn raw_sizeof_allocation_needs_a_known_nonzero_cache_line_remainder() {
    for (extent, expected) in [("6", true), ("8", false), ("LIMIT", false)] {
        let files = parse_cpp_files(vec![CppFile {
            path: "allocation.c".into(),
            source: format!(
                "typedef struct Sample {{ double bins[{extent}]; }} Sample;\n\
                 Sample *create(void) {{\n\
                 Sample *result = aligned_alloc(64, sizeof(Sample));\n\
                 return result;\n}}"
            ),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let evidence = collect_cpp_evidence(&files, &records);
        let storage = evidence
            .iter()
            .flat_map(|set| &set.items)
            .find(|item| item.kind == CppEvidenceKind::AllocatorObjectStorage)
            .expect("allocation storage must remain recorded even with unknown size");
        assert_eq!(
            storage
                .description
                .contains("[unrounded aligned_alloc size]"),
            expected,
            "extent={extent}, records={records:#?}, storage={storage:#?}"
        );
    }
}

#[test]
fn lexical_typedef_and_using_supply_layout_and_holder_type_without_sibling_aliases() {
    let files = parse_cpp_files(vec![CppFile {
        path: "typedefs.hpp".into(),
        source: r#"
        typedef unsigned long long Count;
        using SavedCount = Count;
        using Weak = std::weak_ptr<int>;
        struct State { SavedCount counter; Weak holder; };
        namespace sibling { using Mystery = uint64_t; }
        struct Unknown { Mystery counter; };
    "#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let state = records.iter().find(|r| r.name == "State").unwrap();
    assert_eq!(state.fields[0].estimated_size, Some(8));
    assert_eq!(state.fields[1].estimated_size, Some(16));
    assert_eq!(state.fields[1].ty_str, "std::weak_ptr<int>");
    let unknown = records.iter().find(|r| r.name == "Unknown").unwrap();
    assert_eq!(unknown.fields[0].estimated_size, None);
}

#[test]
fn alias_target_is_bound_before_inner_scope_shadowing() {
    let files = parse_cpp_files(vec![CppFile {
        path: "binding.hpp".into(),
        source: r#"
            using Original = std::atomic<int>;
            using Saved = Original;
            using Plain = std::bitset<64>;
            using SavedPlain = Plain;
            namespace inner {
                using Original = std::bitset<64>;
                using Plain = std::atomic<int>;
                struct State { Saved counter; Original plain; SavedPlain quiet; };
            }
        "#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let state = records.iter().find(|r| r.name == "State").unwrap();
    assert!(
        state.fields[0].is_atomic,
        "outer alias must retain its bound target"
    );
    assert!(!state.fields[1].is_atomic && !state.fields[1].is_hot_sync);
    assert!(
        !state.fields[2].is_atomic && !state.fields[2].is_hot_sync,
        "inner atomic alias must not contaminate an outer plain alias"
    );
}

#[test]
fn enclosing_namespace_alias_shadows_unrelated_sync_record() {
    for (target, hot) in [("std::bitset<64>", false), ("std::atomic<int>", true)] {
        let files = parse_cpp_files(vec![CppFile {
            path: "aliases.hpp".into(),
            source: format!(
                r#"
                namespace unrelated {{ struct Flags {{ std::mutex mutex; }}; }}
                namespace local {{
                    using Flags = {target};
                    struct State {{ Flags flags; }};
                }}
            "#
            ),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let state = records.iter().find(|r| r.name == "State").unwrap();
        assert_eq!(
            state.fields[0].is_atomic || state.fields[0].is_hot_sync,
            hot
        );
    }
}

#[test]
fn namespace_alias_visibility_excludes_siblings_and_later_declarations() {
    let files = parse_cpp_files(vec![CppFile {
        path: "visibility.hpp".into(),
        source: r#"
            struct Flags { std::atomic<int> count; };
            namespace unrelated { using Flags = std::bitset<64>; }
            namespace local {
                struct Before { Flags flags; };
                using Flags = std::bitset<64>;
                struct After { Flags flags; };
                struct InnerState {
                    using Flags = std::atomic<int>;
                    Flags flags;
                };
            }
        "#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    for (name, expected) in [("Before", true), ("After", false), ("InnerState", true)] {
        let field = &records.iter().find(|r| r.name == name).unwrap().fields[0];
        assert_eq!(field.is_atomic || field.is_hot_sync, expected, "{name}");
    }
}

#[test]
fn overloaded_assignment_declarations_do_not_allocate_fields() {
    let files = parse_cpp_files(vec![CppFile {
        path: "operators.hpp".into(),
        source: r#"
        class Handle {
        public:
            Handle & operator=(Handle && other) noexcept;
            Handle & operator=(const Handle &) = delete;
            bool operator==(const Handle &) const;
            int & value();
            int * pointer();
            int (ordinary)();
            int (*factory())(int);
        private:
            int descriptor;
            std::atomic<int> count;
        };
        "#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let record = records.iter().find(|r| r.name == "Handle").unwrap();
    assert_eq!(
        record
            .fields
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        ["descriptor", "count"]
    );
}

#[test]
fn member_initializers_with_calls_do_not_turn_fields_into_methods() {
    let files = parse_cpp_files(vec![CppFile {
        path: "initializers.cpp".into(),
        source: r#"
        struct State {
            unsigned long counter = register_object(this);
            int capacity{get_capacity()};
            int slots[sizeof(long)];
            int (&callback)(int);
            int (*callback_ptr)(int);
            int method(int value);
        };
        "#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let state = records.iter().find(|r| r.name == "State").unwrap();
    let names: Vec<_> = state.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(
        names,
        ["counter", "capacity", "slots", "callback", "callback_ptr"]
    );
    assert_eq!(state.public_methods, ["method"]);
}

#[test]
fn nested_type_declarations_do_not_allocate_outer_fields() {
    let files = parse_cpp_files(vec![CppFile {
        path: "nested.cpp".into(),
        source: r#"
        struct Outer {
            struct Request { int payload; };
            enum Phase { Ready, Done };
            class Forward;
            struct Item { int value; } item;
            int counter;
        };
        "#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let outer = records.iter().find(|r| r.name == "Outer").unwrap();
    let names: Vec<_> = outer.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, ["item", "counter"]);
    assert!(
        records
            .iter()
            .any(|r| r.name == "Request" && r.fields.len() == 1)
    );
}

fn shared_records(source: &str) -> Vec<String> {
    let files = parse_cpp_files(vec![CppFile {
        path: "candidate.cpp".to_string(),
        source: source.to_string(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    collect_cpp_evidence(&files, &records)
        .iter()
        .zip(&records)
        .filter(|(evidence, _)| {
            evidence
                .items
                .iter()
                .any(|item| item.kind == CppEvidenceKind::SharedOwnership)
        })
        .map(|(_, record)| record.name.clone())
        .collect()
}

#[test]
fn annotated_data_members_are_not_annotation_calls_or_parameters() {
    let files = parse_cpp_files(vec![CppFile {
        path: "annotations.cpp".into(),
        source: r#"
        struct State {
            int mutex;
            size_t bytes GUARDED_BY(mutex) = 0;
            std::vector<int> values GUARDED_BY(mutex);
            void update(int count) REQUIRES(mutex);
            int plain;
        };
        "#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let record = records.iter().find(|r| r.name == "State").unwrap();
    let names: Vec<_> = record.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, ["mutex", "bytes", "values", "plain"]);
}

#[test]
fn shared_owner_binds_its_pointee_not_neighboring_signature_types() {
    let records = shared_records(
        r#"
        struct Result { int counter; int flags; };
        struct Key { int counter; int state; };
        Result build(const std::shared_ptr<Key>& key, Result options) {
            Result result;
            result.flags = options.flags;
            return result;
        }
        "#,
    );
    assert_eq!(records, ["Key"]);
}

#[test]
fn shared_owner_recovers_multiline_pointees_and_direct_factories() {
    let records = shared_records(
        r#"
        struct Result { int counter; int flags; };
        struct Key { int counter; int state; };
        std::shared_ptr<
            Key
        > key;
        auto result = std::make_shared<Result>();
        "#,
    );
    assert_eq!(records, ["Result", "Key"]);
}

#[test]
fn shared_owner_does_not_bind_nested_container_elements_or_wrapped_factory_results() {
    let records = shared_records(
        r#"
        struct Element { int counter; int state; };
        std::shared_ptr<std::vector<Element>> elements;
        auto converted = convert(std::make_shared<Element>());
        "#,
    );
    assert!(records.is_empty(), "{records:?}");
}

fn has_counter_finding(body: &str) -> bool {
    let source = format!(
        r#"
        #include <memory>
        #include <mutex>
        int global_mutex;
        int other_mutex;
        struct Counters {{
            int hits;
            int misses;
            void update(bool condition) {{
                {body}
            }}
        }};
        std::shared_ptr<Counters> shared;
        "#,
    );
    let root = tempdir().expect("create fixture directory");
    fs::write(root.path().join("candidate.cpp"), source).expect("write C++ fixture");
    // Test lock/ownership semantics independently of the default evidence policy.
    let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    options.cpp_include_speculative = true;
    let report = analyze_cpp_path_with_options(root.path(), &options);
    report
        .findings
        .iter()
        .any(|finding| finding.has_candidate(CandidateKind::FieldGroup))
}

#[test]
fn whole_pair_explicit_lock_protects_both_fields() {
    assert!(!has_counter_finding(
        "pthread_mutex_lock(&global_mutex);\nhits += 1;\nmisses += 1;\npthread_mutex_unlock(&global_mutex);"
    ));
    assert!(has_counter_finding("hits += 1;\nmisses += 1;"));
}

#[test]
fn checked_lock_and_exiting_error_unlock_preserve_common_guard() {
    assert!(!has_counter_finding(
        "if (pthread_mutex_lock(&global_mutex)) throw Error();\nhits += 1;\nif (condition) {\npthread_mutex_unlock(&global_mutex);\nthrow Error();\n}\nmisses += 1;\npthread_mutex_unlock(&global_mutex);"
    ));
    assert!(has_counter_finding(
        "if (pthread_mutex_lock(&global_mutex)) log_error();\nhits += 1;\nmisses += 1;"
    ));
    assert!(has_counter_finding(
        "pthread_mutex_lock(&global_mutex);\nif (condition) {\npthread_mutex_unlock(&global_mutex);\n}\nhits += 1;\nmisses += 1;"
    ));
}

#[test]
fn sequential_algorithm_callback_inherits_guard_but_parallel_or_unknown_does_not() {
    assert!(!has_counter_finding(
        "std::lock_guard guard(global_mutex);\nstd::erase_if(items, [this](auto item) {\nhits += 1;\nmisses += 1;\nreturn false;\n});"
    ));
    assert!(!has_counter_finding(
        "std::lock_guard guard(global_mutex);\nstd::for_each(begin, end, [this](auto item) {\nhits += 1;\nmisses += 1;\n});"
    ));
    assert!(has_counter_finding(
        "std::lock_guard guard(global_mutex);\nstd::for_each(std::execution::par, begin, end, [this](auto item) {\nhits += 1;\nmisses += 1;\n});"
    ));
    assert!(has_counter_finding(
        "std::lock_guard guard(global_mutex);\ncustom::erase_if(items, [this](auto item) {\nhits += 1;\nmisses += 1;\nreturn false;\n});"
    ));
    assert!(has_counter_finding(
        "std::lock_guard guard(global_mutex);\nstd::erase_if(items, [this](auto item) {\nstd::thread([this] {\nhits += 1;\nmisses += 1;\n}).detach();\nreturn false;\n});"
    ));
}

#[test]
fn one_sided_or_conditional_lock_does_not_serialize_the_pair() {
    assert!(has_counter_finding(
        "pthread_mutex_lock(&global_mutex);\nhits += 1;\npthread_mutex_unlock(&global_mutex);\nmisses += 1;"
    ));
    assert!(has_counter_finding(
        "if (condition) pthread_mutex_lock(&global_mutex);\nhits += 1;\nmisses += 1;"
    ));
    assert!(has_counter_finding(
        "pthread_mutex_lock(&global_mutex);\nif (condition) pthread_mutex_unlock(&global_mutex);\nhits += 1;\nmisses += 1;"
    ));
}

#[test]
fn unique_lock_release_or_transfer_ends_a_protection_witness() {
    assert!(has_counter_finding(
        "std::unique_lock guard(global_mutex);\nguard.unlock();\nhits += 1;\nmisses += 1;"
    ));
    assert!(has_counter_finding(
        "std::unique_lock guard(global_mutex);\nconsume(std::move(guard));\nhits += 1;\nmisses += 1;"
    ));
    assert!(has_counter_finding(
        "std::unique_lock guard(global_mutex);\nif (condition) guard.unlock();\nhits += 1;\nmisses += 1;"
    ));
    assert!(has_counter_finding(
        "std::unique_lock guard(global_mutex);\nguard = std::unique_lock(other_mutex);\nhits += 1;\nmisses += 1;"
    ));
}

#[test]
fn per_invocation_mutex_and_outer_lambda_lock_do_not_protect_shared_fields() {
    assert!(has_counter_finding(
        "int local_mutex;\nstd::lock_guard guard(local_mutex);\nhits += 1;\nmisses += 1;"
    ));
    assert!(has_counter_finding(
        "std::lock_guard guard(global_mutex);\nstd::thread([this] {\nhits += 1;\nmisses += 1;\n}).detach();"
    ));
}

#[test]
fn writer_neighbor_enumerates_distinct_access_pairs_instead_of_only_the_first_peer() {
    for cache_line_size in [32, 64, 128] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("state.hpp"),
            r#"
struct State {
    std::atomic<int> counter;
    int first;
    int second;
    int unused;
    void increment() { counter.fetch_add(1); }
    int read_first() const { return first; }
    int read_second() const { return second; }
};
void run(State &s) {
    std::thread writer([&] { for (int i=0; i<100; ++i) s.increment(); });
    std::thread reader([&] { for (int i=0; i<100; ++i) consume(s.read_first(), s.read_second()); });
    writer.join(); reader.join();
}
"#,
        )
        .unwrap();
        let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
        options.cache_line_size = cache_line_size;
        let report = analyze_cpp_path_with_options(root.path(), &options);
        for peer in ["first", "second"] {
            assert!(
                report.findings.iter().any(|f| {
                    f.field_list.contains(&"counter".to_string())
                        && f.field_list.contains(&peer.to_string())
                }),
                "missing counter/{peer} at {cache_line_size}: {:#?}",
                report.findings
            );
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
fn inline_member_calls_recover_plain_writes_and_implicit_receivers() {
    for (effect, body, expected) in [
        ("value = 1;", "state.touch();", true),
        ("value++;", "this->state.touch();", true),
        ("consume(value);", "state.touch();", false),
        ("value = 1;", "Inner state; state.touch();", false),
        (
            "auto deferred = [this] { value = 1; };",
            "state.touch();",
            false,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("objects.hpp"),
            format!(
                r#"
struct Inner {{ int value; void touch() {{ {effect} }} }};
struct Outer {{
    Inner state;
    std::atomic<int> flag;
    void change() {{ {body} }}
    int read() {{ return flag.load(); }}
}};
"#
            ),
        )
        .unwrap();
        let files = parse_cpp_files(vec![CppFile {
            path: "objects.hpp".into(),
            source: fs::read_to_string(root.path().join("objects.hpp")).unwrap(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        let outer = records.iter().position(|r| r.name == "Outer").unwrap();
        let written = facts[outer].items.iter().any(|a| a.field_name.as_deref() == Some("state") && matches!(a.access_kind, Some(false_sharing_detector::cpp_detection::types::CppAccessKind::Write | false_sharing_detector::cpp_detection::types::CppAccessKind::ReadModifyWrite)));
        assert_eq!(written, expected, "{effect} {body}\n{facts:#?}");
    }
}

#[test]
fn object_stride_keeps_body_proven_inline_reads_with_a_real_writer() {
    for (getter, write, expected) in [
        ("return payload;", "counter.fetch_add(1);", true),
        ("return 7;", "counter.fetch_add(1);", false),
        ("return payload;", "consume(counter.load());", false),
    ] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("objects.hpp"),
            format!(
                r#"
struct Inner {{ int payload; int get() const {{ {getter} }} }};
struct Unit {{
    std::atomic<int> counter;
    Inner info;
    Inner unused;
    void update() {{ {write} consume(info.get()); }}
}};
Unit units[8];
"#
            ),
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
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("Unit")
                    && f.field_list.contains(&"info".into())
                    && f.field_list.contains(&"counter".into())),
            expected,
            "{getter} {write}\n{report:#?}"
        );
        assert!(
            report
                .findings
                .iter()
                .all(|f| !f.field_list.contains(&"unused".into()))
        );
    }
}

#[test]
fn same_named_value_fields_remain_bound_to_nested_accesses() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("same_name.hpp"),
        r#"
namespace Fixture {
struct Board {
    int value;
    void touch() { value++; }
};
struct Task {
    std::atomic<int> counter;
    Board Board {};
    void update() {
        Board.touch();
        counter.fetch_add(1);
    }
};
Task tasks[8];
}
"#,
    )
    .unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]),
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.struct_name.as_deref() == Some("Task")
                && finding.field_list.contains(&"Board".into())
                && finding.field_list.contains(&"counter".into())
        }),
        "{report:#?}"
    );
}

#[test]
fn adjacent_object_pairs_use_cross_boundary_offsets() {
    for cache_line_size in [32, 64, 128] {
        let root = tempdir().unwrap();
        let source = format!(
            r#"
struct Entry {{
    std::atomic<int> observed;
    char gap_a[{cache_line_size}];
    std::atomic<int> interior;
    char gap_b[{cache_line_size}];
    std::atomic<int> written;
    void update() {{ written.fetch_add(1); }}
    int read() {{ return observed.load() + interior.load(); }}
}};
Entry entries[16];
"#
        );
        let path = root.path().join("entries.hpp");
        let options = AnalysisOptions {
            cache_line_size,
            ..AnalysisOptions::with_rules(&[
                RuleId::ContiguousElements,
                RuleId::IndependentAllocations,
            ])
        };
        fs::write(&path, &source).unwrap();
        let report = analyze_cpp_path_with_options(root.path(), &options);
        let pair = report
            .findings
            .iter()
            .find(|f| f.struct_name.as_deref() == Some("Entry"))
            .expect("tail and next object's head may share a block");
        assert!(
            pair.field_list.contains(&"observed".into())
                && pair.field_list.contains(&"written".into()),
            "{pair:#?}"
        );
        assert!(!pair.field_list.contains(&"interior".into()));
        for safe in [
            source.replace(
                "struct Entry",
                &format!("struct alignas({cache_line_size}) Entry"),
            ),
            source.replace("written.fetch_add(1);", "consume(written.load());"),
            source.replace(
                "return observed.load() + interior.load();",
                "return interior.load();",
            ),
        ] {
            fs::write(&path, safe).unwrap();
            assert!(
                analyze_cpp_path_with_options(root.path(), &options)
                    .findings
                    .is_empty()
            );
        }
    }
}

#[test]
fn unknown_object_size_can_have_a_proved_cross_object_member_gap() {
    let root = tempdir().unwrap();
    let path = root.path().join("entries.hpp");
    let source = r#"
struct Base { virtual ~Base() = default; };
struct Entry : Base {
    Entry();
    char prefix[32];
    Unknown payload;
    std::atomic<int> count;
    Unknown extra;
    char suffix[32];
    void update() { count.fetch_add(1); }
};
Entry entries[8];
"#;
    for (block, expected_risk) in [(32, false), (64, false), (128, true)] {
        fs::write(&path, source).unwrap();
        let options = AnalysisOptions {
            cache_line_size: block,
            ..AnalysisOptions::with_rules(&[
                RuleId::ContiguousElements,
                RuleId::IndependentAllocations,
            ])
        };
        let report = analyze_cpp_path_with_options(root.path(), &options);
        assert_eq!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("Entry")),
            expected_risk,
            "B={block}: {report:#?}"
        );
    }
    for unsafe_or_unknown in [
        source
            .replace("char prefix[32];", "char prefix[1];")
            .replace("char suffix[32];", "char suffix[1];"),
        source.replace("Unknown payload;", "[[no_unique_address]] Unknown payload;"),
        source.replace("Unknown payload;", "Unknown& payload;"),
        source
            .replace(
                "struct Entry : Base",
                "using Alias = Unknown&;\nstruct Entry : Base",
            )
            .replace("Unknown payload;", "Alias payload;"),
        source.replace("Unknown payload;", "unsigned flags : 3; Unknown payload;"),
        source.replace("char prefix[32];", "#if WIDE\nchar prefix[32];\n#endif"),
        source.replace("Unknown payload;", "private: Unknown payload; public:"),
    ] {
        fs::write(&path, &unsafe_or_unknown).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[
                RuleId::ContiguousElements,
                RuleId::IndependentAllocations,
            ]),
        );
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("Entry")),
            "{unsafe_or_unknown}\n{report:#?}"
        );
    }
    // Large internal padding cannot isolate the tail from the next head.
    fs::write(
        &path,
        source
            .replace("char prefix[32];", "std::atomic<int> head;")
            .replace("char suffix[32];", "std::atomic<int> tail;")
            .replace(
                "count.fetch_add(1);",
                "head.fetch_add(1); tail.fetch_add(1);",
            ),
    )
    .unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]),
    );
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.struct_name.as_deref() == Some("Entry"))
    );
}

#[test]
fn c_atomic_record_retains_padding_with_sizeof_array_bound() {
    for (bound, expected_size) in [
        ("128 - sizeof(int64_t)", Some(120)),
        ("(128 - sizeof(uint64_t))", Some(120)),
        ("32 - sizeof(uint64_t)", Some(24)),
        ("128 - sizeof(Unknown)", None),
        ("8 - sizeof(uint64_t) - 1", None),
    ] {
        let files = parse_cpp_files(vec![CppFile {
            path: "queue.h".into(),
            source: format!(
                "typedef struct {{\n_Atomic(int64_t) front;\nchar gap[{bound}];\n_Atomic(int64_t) back;\n_Atomic(void *) storage;\n}} Queue;"
            ),
        }]);
        let records = collect_cpp_structs(&files, "sample", 64);
        let record = records.iter().find(|r| r.name == "Queue").unwrap();
        let gap = record
            .fields
            .iter()
            .find(|f| f.name == "gap")
            .expect("array declaration must survive C11 fallback");
        assert_eq!(gap.estimated_size, expected_size, "{bound}: {record:#?}");
    }
}

#[test]
fn c_atomic_queue_padding_separates_only_the_repaired_pair() {
    for block in [32, 64, 128] {
        for (padding, separated) in [("", false), ("char gap[128 - sizeof(int64_t)];", true)] {
            let root = tempdir().unwrap();
            fs::write(
                root.path().join("queue.h"),
                format!(
                    r#"
typedef struct {{
 _Atomic(int64_t) front;
 {padding}
 _Atomic(int64_t) back;
 _Atomic(int64_t) other;
}} Queue;
void front_write(Queue *q) {{
 for (int i=0; i<1000; ++i) {{
 __atomic_fetch_add(&q->front, 1, __ATOMIC_RELAXED);
 }}
}}
void back_write(Queue *q) {{
 for (int i=0; i<1000; ++i) {{
 __atomic_fetch_add(&q->back, 1, __ATOMIC_RELAXED);
 }}
}}
void other_write(Queue *q) {{
 for (int i=0; i<1000; ++i) {{
 __atomic_fetch_add(&q->other, 1, __ATOMIC_RELAXED);
 }}
}}
"#
                ),
            )
            .unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
            options.cache_line_size = block;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            let pair = |a: &str, b: &str| {
                report.findings.iter().any(|f| {
                    f.field_list.iter().any(|n| n == a) && f.field_list.iter().any(|n| n == b)
                })
            };
            assert_eq!(
                pair("front", "back"),
                !separated,
                "{block} {padding}: {report:#?}"
            );
            let files = parse_cpp_files(vec![CppFile {
                path: "queue.h".into(),
                source: fs::read_to_string(root.path().join("queue.h")).unwrap(),
            }]);
            let records = collect_cpp_structs(&files, "sample", block);
            let queue = records.iter().find(|r| r.name == "Queue").unwrap();
            assert!(
                false_sharing_detector::cpp_detection::layout::fields_may_share_cache_line(
                    queue,
                    &["back".into(), "other".into()]
                ),
                "padding must not isolate the unrepaired adjacent pair: {block} {padding} {queue:#?}"
            );
        }
    }
}

#[test]
fn grouped_record_does_not_borrow_an_unrelated_reviewable_pair() {
    let root = tempdir().unwrap();
    fs::write(
        root.path().join("state.hpp"),
        r#"
struct Sample {
    long *payload;
    char gap[48];
    double scale;
    std::atomic<uint64_t> count;
};
void init(Sample *s, long *p) { s->payload = p; s->scale = 1.0; }
long *read_payload(Sample *s) { return s->payload; }
double read_scale(Sample *s) { return s->scale; }
void update(Sample *s) { for (int i=0; i<1000; ++i) { s->count.fetch_add(1); } }
"#,
    )
    .unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.field_list.contains(&"scale".into())
                && f.field_list.contains(&"count".into())),
        "retain the supported adjacent risk: {report:#?}"
    );
    assert!(
        !report
            .findings
            .iter()
            .any(|f| f.field_list.contains(&"payload".into())
                && f.field_list.contains(&"count".into())),
        "do not turn a grouped field union into a repaired-pair witness: {report:#?}"
    );
}

#[test]
fn inline_effect_does_not_create_accesses_on_same_named_members() {
    use false_sharing_detector::cpp_detection::types::CppAccessKind;
    for cache_line_size in [32, 64, 128] {
        for call in ["state.touch();", "this->state.touch();"] {
            let files = parse_cpp_files(vec![CppFile {
                path: "receivers.hpp".into(),
                source: format!(
                    r#"
struct Inner {{ std::atomic<int> value; void touch() {{ value.fetch_add(1); }} }};
struct Untouched {{ Inner state; int peer; int read() {{ return peer; }} }};
struct Active {{ Inner state; void update() {{ {call} }} }};
void external(Active* object) {{ object->state.touch(); }}
void unknown(Missing* object) {{ object->state.touch(); }}
"#
                ),
            }]);
            let records = collect_cpp_structs(&files, "fixture", cache_line_size);
            let facts = collect_cpp_evidence(&files, &records);
            let untouched = records.iter().position(|r| r.name == "Untouched").unwrap();
            let active = records.iter().position(|r| r.name == "Active").unwrap();
            assert!(
                !facts[untouched]
                    .items
                    .iter()
                    .any(|a| a.field_name.as_deref() == Some("state") && a.access_kind.is_some()),
                "{call}: {:?}",
                facts[untouched]
            );
            for function in ["update", "external"] {
                assert!(
                    facts[active]
                        .items
                        .iter()
                        .any(|a| a.function_name.as_deref() == Some(function)
                            && a.kind == CppEvidenceKind::InlineMemberAccess
                            && a.access_kind == Some(CppAccessKind::ReadModifyWrite)),
                    "{call} {function}: {:?}",
                    facts[active]
                );
            }
            assert!(
                !facts[active]
                    .items
                    .iter()
                    .any(|a| a.function_name.as_deref() == Some("unknown")
                        && a.access_kind.is_some())
            );
        }
    }
}

#[test]
fn inline_effect_cannot_borrow_another_receiver_read_on_the_same_line() {
    use false_sharing_detector::cpp_detection::types::CppAccessKind;
    let files = parse_cpp_files(vec![CppFile {
        path: "calls.hpp".into(),
        source: r#"
struct Inner { int value; void touch() { value++; } };
struct Holder { Inner state; };
void mixed(Holder* known, Missing* unknown) { consume(known->state); unknown->state.touch(); }
void actual(Holder* known) { known->state.touch(); }
"#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    let owner = records.iter().position(|r| r.name == "Holder").unwrap();
    assert!(
        !facts[owner]
            .items
            .iter()
            .any(|a| a.function_name.as_deref() == Some("mixed")
                && matches!(
                    a.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                ))
    );
    assert!(
        facts[owner]
            .items
            .iter()
            .any(|a| a.function_name.as_deref() == Some("actual")
                && a.access_kind == Some(CppAccessKind::ReadModifyWrite))
    );
}

#[test]
fn inline_method_effect_stays_in_the_receivers_storage_domain() {
    use false_sharing_detector::cpp_detection::types::CppAccessKind;
    for (field, body, expected) in [
        ("std::vector<int> payload;", "payload[0]++;", false),
        ("std::vector<int> payload;", "payload.clear();", true),
        ("int payload[4];", "payload[0]++;", true),
        ("std::array<int, 4> payload;", "payload[0]++;", true),
    ] {
        let files = parse_cpp_files(vec![CppFile {
            path: "domains.hpp".into(),
            source: format!(
                "struct Inner {{ {field} void touch() {{ {body} }} }};\nstruct Outer {{ Inner state; void update() {{ state.touch(); }} }};"
            ),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        let outer = records.iter().position(|r| r.name == "Outer").unwrap();
        assert_eq!(
            facts[outer]
                .items
                .iter()
                .any(|a| a.field_name.as_deref() == Some("state")
                    && matches!(
                        a.access_kind,
                        Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                    )),
            expected,
            "{field} {body}: {:?}",
            facts[outer]
        );
    }
}

#[test]
fn included_aliases_and_fixed_enums_complete_layout_in_the_declaring_namespace() {
    for block in [32, 64, 128] {
        let files = parse_cpp_files(vec![
            CppFile {
                path: "/project/include/math/point.hpp".into(),
                source: r#"
                #ifndef POINT_HPP
                #define POINT_HPP
                namespace geometry { struct Point { double x, y, z; }; using Direction = Point; }
                #endif
            "#
                .into(),
            },
            CppFile {
                path: "/project/include/state.hpp".into(),
                source: r#"
                #include "math/point.hpp"
                namespace sibling { using Direction = char; }
                namespace geometry {
                    enum class Kind { left, right };
                    struct State { Point position; Direction direction; double energy, time, weight;
                        int group, surface; Kind kind; int64_t parent, child; };
                }
            "#
                .into(),
            },
        ]);
        let records = collect_cpp_structs(&files, "fixture", block);
        let state = records.iter().find(|r| r.name == "State").unwrap();
        assert_eq!(state.total_estimated_size, Some(104), "{state:#?}");
        assert_eq!(state.fields[1].ty_str, "geometry::Point");
        assert_eq!(state.fields[7].estimated_size, Some(4));
    }
}

#[test]
fn enum_layout_needs_a_fixed_underlying_type_and_respects_scope() {
    let files = parse_cpp_files(vec![CppFile {
        path: "enums.hpp".into(),
        source: r#"
        using Byte = unsigned char;
        enum class Small : Byte { one };
        enum class Default { one };
        enum Plain { one };
        namespace sibling { enum class Hidden : uint64_t { one }; }
        struct Enums { Small small; Default normal; Plain unknown; Hidden invisible; };
        namespace nested {
            enum class Small : uint64_t { one };
            struct Inner { Small large; ::Small small; };
        }
    "#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let fields = &records.iter().find(|r| r.name == "Enums").unwrap().fields;
    assert_eq!(
        fields.iter().map(|f| f.estimated_size).collect::<Vec<_>>(),
        vec![Some(1), Some(4), None, None]
    );
    let fields = &records.iter().find(|r| r.name == "Inner").unwrap().fields;
    assert_eq!(
        fields.iter().map(|f| f.estimated_size).collect::<Vec<_>>(),
        vec![Some(8), Some(1)]
    );
}

#[test]
fn included_type_binding_rejects_ambiguous_conditional_and_unincluded_aliases() {
    for (include, headers, expected) in [
        (
            "#include \"types.hpp\"",
            vec![
                ("/project/a/types.hpp", "using Count = uint64_t;"),
                ("/project/b/types.hpp", "using Count = uint32_t;"),
            ],
            None,
        ),
        (
            "",
            vec![("/project/types.hpp", "using Count = uint64_t;")],
            None,
        ),
        (
            "#include \"types.hpp\"",
            vec![(
                "/project/types.hpp",
                "#ifdef LARGE\nusing Count = uint64_t;\n#else\nusing Count = uint32_t;\n#endif",
            )],
            None,
        ),
        (
            "#include \"types.hpp\"",
            vec![("/project/types.hpp", "using Count = uint64_t;")],
            Some(8),
        ),
    ] {
        let mut files = headers
            .into_iter()
            .map(|(path, source)| CppFile {
                path: path.into(),
                source: source.into(),
            })
            .collect::<Vec<_>>();
        files.push(CppFile {
            path: "/project/test.cpp".into(),
            source: format!("{include}\nstruct State {{ Count counter; }};"),
        });
        let files = parse_cpp_files(files);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let field = &records.iter().find(|r| r.name == "State").unwrap().fields[0];
        assert_eq!(field.estimated_size, expected, "{include}: {field:#?}");
    }
}

#[test]
fn included_alias_target_is_frozen_before_inner_shadowing_and_preserves_pointer_layers() {
    let files = parse_cpp_files(vec![
        CppFile { path: "/project/types.hpp".into(), source: "namespace api { template<class T> struct Storage { int values[16]; }; using Handle = Storage<int>; }".into() },
        CppFile { path: "/project/use.cpp".into(), source: "#include \"types.hpp\"\nnamespace api { namespace inner { struct Storage { char byte; }; struct State { const Handle *storage; }; } }".into() },
    ]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let field = &records.iter().find(|r| r.name == "State").unwrap().fields[0];
    assert!(
        field.ty_str.starts_with("api::Storage<int> *"),
        "{field:#?}"
    );
    assert_eq!(field.estimated_size, Some(8));
}

#[test]
fn type_include_budget_discards_partial_bindings_and_later_includes_are_not_visible() {
    let files = parse_cpp_files(vec![
        CppFile { path: "/project/types.hpp".into(), source: "using Count = uint64_t;".into() },
        CppFile { path: "/project/use.cpp".into(), source: "struct Before { Count counter; };\n#include \"types.hpp\"\nstruct After { Count counter; };".into() },
    ]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    assert_eq!(
        records.iter().find(|r| r.name == "Before").unwrap().fields[0].estimated_size,
        None
    );
    assert_eq!(
        records.iter().find(|r| r.name == "After").unwrap().fields[0].estimated_size,
        Some(8)
    );

    let mut sources = (0..27)
        .map(|i| CppFile {
            path: format!("/project/chain{i}.hpp"),
            source: format!(
                "{}\n#include \"chain{}.hpp\"\n",
                if i == 0 {
                    "using Count = uint64_t;"
                } else {
                    ""
                },
                i + 1
            ),
        })
        .collect::<Vec<_>>();
    sources.push(CppFile {
        path: "/project/use.cpp".into(),
        source: "#include \"chain0.hpp\"\nstruct State { Count counter; };".into(),
    });
    let files = parse_cpp_files(sources);
    let records = collect_cpp_structs(&files, "fixture", 64);
    assert_eq!(
        records.iter().find(|r| r.name == "State").unwrap().fields[0].estimated_size,
        None,
        "an exhausted include traversal must not keep partial type evidence"
    );
}

#[test]
fn source_constant_record_alignment_respects_interference_size_and_build_overrides() {
    let root = tempdir().unwrap();
    let file = root.path().join("slots.cpp");
    fs::write(
        &file,
        r#"
        static constexpr int Boundary = 64;
        struct alignas(Boundary) Slot {
            std::atomic<unsigned> value;
            void bump() { value.fetch_add(1); }
        };
        Slot slots[8];
        void update(int worker_id) { slots[worker_id].bump(); }
    "#,
    )
    .unwrap();
    for (size, flags, expected) in [
        (32, vec![], false),
        (64, vec![], false),
        (128, vec![], true),
        (64, vec!["-DUNRELATED=1"], false),
        (64, vec!["-DBoundary=16"], true),
        (64, vec!["/DBoundary=16"], true),
        (64, vec!["-Dconstexpr="], true),
        (64, vec!["/FIopaque.h"], true),
    ] {
        let args = std::iter::once("clang++")
            .chain(flags.iter().copied())
            .chain(["-c", "slots.cpp"])
            .collect::<Vec<_>>();
        fs::write(
            root.path().join("compile_commands.json"),
            serde_json::json!([{"directory":root.path(),"file":file,"arguments":args}]).to_string(),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions {
                cache_line_size: size,
                ..AnalysisOptions::with_rules(&[
                    RuleId::ContiguousElements,
                    RuleId::IndependentAllocations,
                ])
            },
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "B={size} {flags:?}: {report:#?}"
        );
    }
}

#[test]
fn record_accesses_recover_bound_global_mutex_macros() {
    for block in [32, 64, 128] {
        for (right_guard, outside_write, expected) in [
            ("serial", false, false),
            ("other", false, true),
            ("serial", true, true),
        ] {
            let root = tempdir().unwrap();
            fs::write(root.path().join("locks.h"), "#define MAKE_MUTEX(x) pthread_mutex_t x##_mutex = PTHREAD_MUTEX_INITIALIZER\n#define TAKE(x) pthread_mutex_lock(&x##_mutex)\n#define GIVE(x) pthread_mutex_unlock(&x##_mutex)\n").unwrap();
            let source = format!(
                "#include \"locks.h\"\nMAKE_MUTEX(serial);\nMAKE_MUTEX(other);\nstruct State {{\nstd::atomic<int> left;\nstd::atomic<int> right;\nvoid first() {{\nTAKE(serial);\nleft.fetch_add(1);\nGIVE(serial);\n}}\nvoid second() {{\nTAKE({right_guard});\nright.fetch_add(1);\nGIVE({right_guard});\n{}\n}}\n}};\n",
                if outside_write {
                    "right.fetch_add(1);"
                } else {
                    ""
                }
            );
            fs::write(root.path().join("sample.hpp"), source).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
            options.cache_line_size = block;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "B={block} {right_guard} outside={outside_write}: {report:#?}"
            );
        }
    }
}

#[test]
fn macro_locked_record_prefix_does_not_hide_an_unlocked_access() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("sample.hpp"), format!("#define TAKE(x) pthread_mutex_lock(&x)\n#define GIVE(x) pthread_mutex_unlock(&x)\npthread_mutex_t serial;\nstruct State {{ std::atomic<int> count;\nvoid locked() {{\nTAKE(serial);\n{}\nGIVE(serial);\n}}\nvoid unlocked() {{ count.fetch_add(1); }}\n}};\nState items[32];\n", "count.fetch_add(1);\n".repeat(20))).unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::ContiguousElements, RuleId::IndependentAllocations]),
    );
    assert!(
        report
            .findings
            .iter()
            .any(|f| f.struct_name.as_deref() == Some("State")),
        "{report:#?}"
    );
}

#[test]
fn macro_mutex_identity_and_visibility_are_required_for_record_protection() {
    for (declaration, release, expected) in [
        ("pthread_mutex_t gate;", "GIVE(gate);", false),
        ("__thread pthread_mutex_t gate;", "GIVE(gate);", true),
        ("pthread_mutex_t *gate;", "GIVE(gate);", true),
        ("pthread_mutex_t gate;", "MAY_RELEASE(gate);", true),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("sample.hpp"), format!("#define TAKE(x) pthread_mutex_lock(&x)\n#define GIVE(x) pthread_mutex_unlock(&x)\n#define MAY_RELEASE(x) do {{ GIVE(x); }} while(0)\n{declaration}\nstruct State {{ std::atomic<int> left, right;\nvoid first() {{\nTAKE(gate);\nleft++;\nGIVE(gate);\n}}\nvoid second() {{\nTAKE(gate);\n{}\nright++;\nGIVE(gate);\n}}\n}};\n", if release.starts_with("MAY") {release} else {""})).unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{declaration} {release}: {report:#?}"
        );
    }

    let root = tempdir().unwrap();
    fs::write(
        root.path().join("locks.h"),
        "#define TAKE(x) pthread_mutex_lock(&x)\n#define GIVE(x) pthread_mutex_unlock(&x)\n",
    )
    .unwrap();
    fs::write(
        root.path().join("state.h"),
        "struct State { std::atomic<int> left; std::atomic<int> right; };\n",
    )
    .unwrap();
    for (file, function, field) in [
        ("left.cpp", "left_writer", "left"),
        ("right.cpp", "right_writer", "right"),
    ] {
        fs::write(root.path().join(file), format!("#include \"locks.h\"\n#include \"state.h\"\nstatic pthread_mutex_t gate;\nvoid {function}(State &object) {{\nTAKE(gate);\nobject.{field}++;\nGIVE(gate);\n}}\n")).unwrap();
    }
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(
        !report.findings.is_empty(),
        "distinct translation-unit locks: {report:#?}"
    );
}
#[test]
fn unrelated_record_fields_do_not_disable_a_supported_access_pair() {
    use false_sharing_detector::{
        cpp_detection::analyze_cpp_path_with_options,
        types::{AnalysisOptions, RuleId},
    };
    for block in [32, 64, 128] {
        for count in [128, 129, 200] {
            let root = tempfile::tempdir().unwrap();
            let fields = (0..count - 2)
                .map(|i| format!("int unused_{i};\n"))
                .collect::<String>();
            let source = format!(
                "#include <atomic>\nclass State {{ std::atomic<int> left; std::atomic<int> right;\n{fields}public:\nvoid one() {{ left.fetch_add(1); }}\nvoid two() {{ right.fetch_add(1); }}\n}};\n"
            );
            std::fs::write(root.path().join("state.hpp"), source).unwrap();
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions {
                    cache_line_size: block,
                    ..AnalysisOptions::with_rules(&[RuleId::SameObjectFields])
                },
            );
            assert!(!report.analysis_incomplete, "{report:#?}");
            assert!(
                report
                    .findings
                    .iter()
                    .any(|finding| finding.field_list == ["left", "right"]),
                "fields={count}, B={block}, {report:#?}"
            );
        }
    }
}
