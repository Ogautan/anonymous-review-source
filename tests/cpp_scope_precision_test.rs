use false_sharing_detector::cpp_detection::evidence::collect_cpp_evidence;
use false_sharing_detector::cpp_detection::layout::collect_cpp_structs;
use false_sharing_detector::cpp_detection::parser::parse_cpp_files;
use false_sharing_detector::cpp_detection::types::{CppEvidenceItem, CppFile};
use false_sharing_detector::types::RuleId;

#[test]
fn requested_root_and_ancestors_do_not_change_cpp_discovery() {
    use false_sharing_detector::cpp_detection::{
        analyze_cpp_path_with_options, looks_like_cpp_project,
    };
    use false_sharing_detector::types::AnalysisOptions;
    use std::fs;
    let temporary = tempfile::tempdir().unwrap();
    for location in [
        "project",
        "build/project",
        "tests/project",
        "dist",
        "vendor",
    ] {
        let root = temporary.path().join(location);
        fs::create_dir_all(&root).unwrap();
        let source = "struct State { std::atomic<int> left; std::atomic<int> right; };\nvoid one(State* s) { s->left.fetch_add(1); }\nvoid two(State* s) { s->right.fetch_add(1); }\nvoid run(State* s) {\nstd::thread a(one,s);\nstd::thread b(two,s);\n}\n";
        fs::write(root.join("record.cpp"), source).unwrap();
        for ignored in ["build", "vendor", "tests"] {
            let directory = root.join(ignored);
            fs::create_dir(&directory).unwrap();
            fs::write(directory.join("ignored.cpp"), "not valid C++").unwrap();
        }
        assert!(looks_like_cpp_project(&root), "{location}");
        let report = analyze_cpp_path_with_options(
            &root,
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(report.scanned_files, 1, "{location}: {report:#?}");
        assert!(!report.analysis_incomplete, "{report:#?}");
        assert!(!report.findings.is_empty(), "{location}: {report:#?}");
    }
}

#[test]
fn same_object_fields_do_not_combine_disjoint_value_receivers() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    use std::fs;
    for block in [32, 64, 128] {
        for (receiver, expected) in [("second", false), ("first", true), ("alias", true)] {
            let root = tempfile::tempdir().unwrap();
            let source = format!(
                r#"
#include <atomic>
#include <thread>
namespace {{
struct alignas(128) State {{ std::atomic<unsigned long> a{{0}}, b{{0}}; }};
State first, second;
State& alias = first;
void left() {{ for (int k=0;k<10000;++k) first.a.fetch_add(1); }}
void right() {{ for (int k=0;k<10000;++k) {receiver}.b.fetch_add(1); }}
}}
int main() {{ std::thread x(left), y(right); x.join(); y.join(); }}
"#
            );
            fs::write(root.path().join("main.cpp"), &source).unwrap();
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions {
                    cache_line_size: block,
                    ..AnalysisOptions::with_rules(&[RuleId::SameObjectFields])
                },
            );
            assert!(!report.analysis_incomplete, "{report:#?}");
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "B={block}: {source}\n{report:#?}"
            );
        }
    }
}

#[test]
fn extern_declarations_in_different_files_can_name_the_same_object() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    let root = tempfile::tempdir().unwrap();
    std::fs::write(
        root.path().join("state.hpp"),
        "struct State { std::atomic<int> a{0}, b{0}; };\n",
    )
    .unwrap();
    std::fs::write(
        root.path().join("left.cpp"),
        "#include \"state.hpp\"\nextern State shared;\nvoid left() { shared.a.fetch_add(1); }\n",
    )
    .unwrap();
    std::fs::write(root.path().join("right.cpp"),
        "#include \"state.hpp\"\nextern State shared;\nvoid right() { shared.b.fetch_add(1); }\nvoid run() { std::thread x(left), y(right); x.join(); y.join(); }\n").unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(!report.analysis_incomplete, "{report:#?}");
    assert!(!report.findings.is_empty(), "{report:#?}");
}

#[test]
fn independent_execution_evidence_stays_with_its_object_pair() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    for (receiver, expected) in [("second", false), ("first", true)] {
        let root = tempfile::tempdir().unwrap();
        std::fs::write(
            root.path().join("main.cpp"),
            format!(
                r#"
#include <atomic>
#include <thread>
namespace {{
struct alignas(128) State {{ std::atomic<int> a{{0}}, b{{0}}; }};
State first, second;
void both() {{ first.a.fetch_add(1); first.b.fetch_add(1); }}
void only_b() {{ {receiver}.b.fetch_add(1); }}
}}
int main() {{ std::thread x(both), y(only_b); x.join(); y.join(); }}
"#
            ),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(!report.findings.is_empty(), expected, "{report:#?}");
    }
}

fn accesses(body: &str) -> Vec<CppEvidenceItem> {
    let files = parse_cpp_files(vec![CppFile {
        path: "candidate.hpp".into(),
        source: format!("struct Counters {{ int hits; int misses; }};\n{body}"),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    collect_cpp_evidence(&files, &records)
        .into_iter()
        .flat_map(|facts| facts.items)
        .filter(|item| item.access_kind.is_some())
        .collect()
}

#[test]
fn chained_callback_does_not_borrow_parallelism_from_its_receiver() {
    for continuation in ["then", "then_wrapped", "finally"] {
        let facts = accesses(&format!(
            r#"
void update(Counters& current) {{
    parallel_for_each(items, [&] {{
        current.hits++;
    }}).{continuation}([&] {{
        current.misses++;
    }});
}}
"#
        ));
        assert!(
            facts.iter().any(|item| {
                item.field_name.as_deref() == Some("hits") && item.in_concurrent_context
            }),
            "parallel callback: {facts:#?}"
        );
        assert!(
            facts
                .iter()
                .any(|item| { item.field_name.as_deref() == Some("misses") }),
            "continuation access: {facts:#?}"
        );
        assert!(
            facts
                .iter()
                .filter(|item| { item.field_name.as_deref() == Some("misses") })
                .all(|item| !item.in_concurrent_context),
            "{continuation}: {facts:#?}"
        );
    }
}

#[test]
fn chained_callback_keeps_its_own_parallel_callee_or_enclosing_thread() {
    for body in [
        "make_scheduler().parallel_for_each(items, [&] { current.hits++; current.misses++; });",
        "std::thread worker([&] {\n parallel_for_each(items, [] {}).then([&] {\n current.hits++; current.misses++;\n });\n }); worker.join();",
        "thread_pool.enqueue([&] { current.hits++; current.misses++; });",
    ] {
        let facts = accesses(&format!("void update(Counters& current) {{\n{body}\n}}"));
        for field in ["hits", "misses"] {
            assert!(
                facts.iter().any(|item| {
                    item.field_name.as_deref() == Some(field) && item.in_concurrent_context
                }),
                "{body}: {facts:#?}"
            );
        }
    }
}

#[test]
fn same_object_warning_requires_parallelism_in_the_selected_callback() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    use std::fs;
    use tempfile::tempdir;

    for block in [32, 64, 128] {
        for parallel in [false, true] {
            let callback = "parallel_for_each(items, [] {}).then_wrapped([this] {\n hits++;\n });";
            let body = if parallel {
                format!("std::thread worker([this] {{\n{callback}\n}}); worker.join();")
            } else {
                callback.to_owned()
            };
            let root = tempdir().unwrap();
            fs::write(root.path().join("callbacks.hpp"), format!(
                "class Counters {{ int hits; int misses; public:\n void update() {{\n{body}\n}}\n int inspect() {{ return misses; }}\n}};"
            )).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
            options.cache_line_size = block;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert!(!report.analysis_incomplete, "{report:#?}");
            assert_eq!(
                report
                    .findings
                    .iter()
                    .any(|f| f.struct_name.as_deref() == Some("Counters")),
                parallel,
                "block={block}, parallel={parallel}: {report:#?}"
            );
        }
    }
}

#[test]
fn by_value_record_parameters_have_invocation_local_inline_storage() {
    for (parameter, receiver, expected) in [
        ("Counters current", "current", true),
        ("Counters current = {}", "current", true),
        ("Counters& current", "current", false),
        ("Counters* current", "(*current)", false),
        ("Counters current[8]", "current[0]", false),
        ("std::span<Counters> current", "current[0]", false),
    ] {
        let facts = accesses(&format!(
            "void update({parameter}) {{ {receiver}.hits++; {receiver}.misses++; }}"
        ));
        assert!(!facts.is_empty(), "{parameter}");
        assert!(
            facts
                .iter()
                .all(|a| a.through_nonescaping_local == expected),
            "{parameter}: {facts:#?}"
        );
    }
}

#[test]
fn escaping_value_parameters_are_not_assumed_private() {
    for use_site in [
        "publish(&current); current.hits++;",
        "publish(current); current.hits++;",
        "std::thread worker([&] { current.hits++; }); worker.join();",
    ] {
        let facts = accesses(&format!("void update(Counters current) {{ {use_site} }}"));
        assert!(!facts.is_empty(), "{use_site}");
        assert!(
            facts.iter().all(|a| !a.through_nonescaping_local),
            "{use_site}: {facts:#?}"
        );
    }
}

#[test]
fn opaque_parameter_wrapper_does_not_imply_private_payload() {
    let files = parse_cpp_files(vec![CppFile {
        path: "candidate.hpp".into(),
        source: "struct View { std::span<int> values; int cursor; };\nvoid update(View copy, int index) { copy.cursor++; copy.values[index]++; }\n".into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    assert!(
        facts[0]
            .items
            .iter()
            .any(|a| a.field_name.as_deref() == Some("cursor") && !a.through_nonescaping_local)
    );
    assert!(facts[0].items.iter().any(|a| a.kind
        == false_sharing_detector::cpp_detection::types::CppEvidenceKind::ContiguousElementAccess
        && !a.through_nonescaping_local));
}

#[test]
fn value_parameter_ownership_uses_the_bound_declaration_and_constructor_contract() {
    for (special_member, expected) in [
        ("", true),
        ("Counters(const Counters&) { publish(this); }", false),
        ("Counters(const Counters&);", false),
    ] {
        let files = parse_cpp_files(vec![
            CppFile { path: "state.hpp".into(), source: format!(
                "struct Counters {{ int hits; int misses; {special_member} }};"
            ) },
            CppFile { path: "worker.cpp".into(), source:
                "#include \"state.hpp\"\nvoid update(Counters copy) { copy.hits++; copy.misses++; }".into() },
        ]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        let accesses = facts[0]
            .items
            .iter()
            .filter(|a| a.function_name.as_deref() == Some("update") && a.access_kind.is_some())
            .collect::<Vec<_>>();
        assert!(!accesses.is_empty());
        assert!(
            accesses
                .iter()
                .all(|a| a.through_nonescaping_local == expected),
            "{special_member}: {accesses:#?}"
        );
    }
}

#[test]
fn unrelated_tls_declaration_does_not_exclude_same_named_parameters() {
    let facts = accesses(
        "void unrelated() { thread_local Counters current; }\nvoid first(Counters* current) { current->hits++; }\nvoid second(Counters* current) { current->misses++; }",
    );
    assert_eq!(facts.len(), 2, "{facts:#?}");
    assert!(facts.iter().all(|item| !item.through_thread_local));
}

#[test]
fn unrelated_stack_local_does_not_exclude_same_named_global() {
    let facts = accesses(
        "Counters current;\nvoid unrelated() { Counters current; }\nvoid first() { current.hits++; }\nvoid second() { current.misses++; }",
    );
    assert_eq!(facts.len(), 2, "{facts:#?}");
    assert!(facts.iter().all(|item| !item.through_nonescaping_local));
}

#[test]
fn inner_tls_scope_ends_before_the_outer_parameter_use() {
    let facts = accesses(
        "void update(Counters* current) {\n{ thread_local Counters current; current.hits++; }\ncurrent->misses++;\n}",
    );
    assert!(
        facts
            .iter()
            .any(|item| item.field_name.as_deref() == Some("hits") && item.through_thread_local)
    );
    assert!(
        facts
            .iter()
            .any(|item| item.field_name.as_deref() == Some("misses") && !item.through_thread_local)
    );
}

#[test]
fn actual_tls_value_and_unescaped_stack_value_keep_their_exclusions() {
    for (declaration, tls) in [
        ("thread_local Counters current;", true),
        ("Counters current;", false),
    ] {
        let facts = accesses(&format!(
            "void update() {{\n{declaration}\ncurrent.hits++;\ncurrent.misses++;\n}}"
        ));
        assert_eq!(facts.len(), 2, "{facts:#?}");
        assert!(facts.iter().all(|item| if tls {
            item.through_thread_local
        } else {
            item.through_nonescaping_local
        }));
    }
}

#[test]
fn address_escape_on_the_declaration_line_ends_local_ownership_proof() {
    let facts = accesses(
        "void update() {\nCounters current; publish(&current); current.hits++;\ncurrent.misses++;\n}",
    );
    assert!(!facts.is_empty());
    assert!(facts.iter().all(|item| !item.through_nonescaping_local));
}

#[test]
fn implicit_lambda_capture_and_unknown_member_publication_are_not_nonescape_proofs() {
    for body in [
        "std::thread([&] { current.hits++; current.misses++; }).join();",
        "publish(current); current.hits++; current.misses++;",
        "current.publish(); current.hits++; current.misses++;",
    ] {
        let facts = accesses(&format!("void update() {{\nCounters current;\n{body}\n}}"));
        assert!(!facts.is_empty(), "{body}");
        assert!(
            facts.iter().all(|item| !item.through_nonescaping_local),
            "{body}: {facts:#?}"
        );
    }
}

#[test]
fn tls_pointer_storage_does_not_make_its_pointee_thread_local() {
    let facts = accesses(
        "Counters* shared;\nthread_local Counters* current = shared;\nvoid update() { current->hits++; current->misses++; }",
    );
    assert_eq!(facts.len(), 2, "{facts:#?}");
    assert!(facts.iter().all(|item| !item.through_thread_local));
}

#[test]
fn address_escape_of_tls_value_does_not_prove_exclusive_thread_ownership() {
    let facts = accesses(
        "thread_local Counters current;\nvoid publish_current() { publish(&current); }\nvoid update() { current.hits++; current.misses++; }",
    );
    assert!(!facts.is_empty());
    assert!(facts.iter().all(|item| !item.through_thread_local));
}

#[test]
fn condition_variable_wait_restores_only_a_bound_standard_lock() {
    for (cv_type, lock_type, wait, protected) in [
        (
            "std::condition_variable",
            "std::unique_lock",
            "cv.wait(lock);",
            true,
        ),
        (
            "std::condition_variable",
            "std::unique_lock",
            "cv.wait(lock, [this] { return ready; });",
            true,
        ),
        (
            "std::condition_variable",
            "std::unique_lock",
            "cv.wait_for(lock, std::chrono::milliseconds(1));",
            true,
        ),
        (
            "std::condition_variable",
            "std::unique_lock",
            "cv.wait_until(lock, std::chrono::steady_clock::now());",
            true,
        ),
        (
            "Unknown",
            "std::unique_lock",
            "cv.wait_for(lock, std::chrono::milliseconds(1));",
            false,
        ),
        (
            "std::condition_variable",
            "Custom_unique_lock",
            "cv.wait_until(lock, deadline);",
            false,
        ),
        ("Unknown", "std::unique_lock", "cv.wait(lock);", false),
        (
            "std::condition_variable",
            "Custom_unique_lock",
            "cv.wait(lock);",
            false,
        ),
        (
            "std::condition_variable",
            "std::unique_lock",
            "unknown(lock);",
            false,
        ),
        (
            "std::condition_variable",
            "std::unique_lock",
            "cv.wait(lock); lock.unlock();",
            false,
        ),
        (
            "std::condition_variable",
            "std::unique_lock",
            "cv.wait(lock, [&] { lock.unlock(); return true; });",
            false,
        ),
    ] {
        let source = format!(
            r#"
struct State {{
    std::mutex gate;
    {cv_type} cv;
    bool ready;
    int value;
    void consume() {{
        {lock_type} lock(gate);
        {wait}
        value++;
    }}
}};
"#
        );
        let files = parse_cpp_files(vec![CppFile {
            path: "wait.hpp".into(),
            source,
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let facts = collect_cpp_evidence(&files, &records);
        let value = facts
            .iter()
            .flat_map(|facts| &facts.items)
            .find(|item| item.field_name.as_deref() == Some("value") && item.access_kind.is_some())
            .unwrap();
        assert_eq!(
            value.guard_ids.contains(&"gate".to_owned()),
            protected,
            "cv={cv_type}, lock={lock_type}, wait={wait}: {value:?}"
        );
    }
}

#[test]
fn condition_variable_wait_binds_a_cross_file_receiver() {
    let files = parse_cpp_files(vec![
        CppFile {
            path: "state.hpp".into(),
            source: "struct State { int value; std::mutex gate; std::condition_variable cv; };"
                .into(),
        },
        CppFile {
            path: "worker.cpp".into(),
            source: r#"
struct Worker {
    State & parent;
    void consume() {
        std::unique_lock lock(parent.gate);
        parent.cv.wait(lock);
        parent.value++;
    }
};
"#
            .into(),
        },
    ]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    let value = facts
        .iter()
        .flat_map(|facts| &facts.items)
        .find(|item| item.field_name.as_deref() == Some("value") && item.access_kind.is_some())
        .unwrap();
    assert!(
        value.guard_ids.contains(&"parent.gate".to_owned()),
        "{value:?}"
    );
}

#[test]
fn condition_wait_predicate_uses_the_matching_lock_without_protecting_escapes() {
    for wait_method in [
        "wait(lock,",
        "wait_for(lock, std::chrono::milliseconds(1),",
        "wait_until(lock, std::chrono::steady_clock::now(),",
    ] {
        for size in [32, 64, 128] {
            for (cv_type, predicate, expected) in [
                ("std::condition_variable", "return value != 0;", false),
                ("Unknown", "return value != 0;", true),
                (
                    "std::condition_variable",
                    "lock.unlock();\n return value != 0;",
                    true,
                ),
                (
                    "std::condition_variable",
                    "unknown(lock);\n return value != 0;",
                    true,
                ),
                (
                    "std::condition_variable",
                    "queue([this] { return value != 0; });\n return true;",
                    true,
                ),
            ] {
                let root = tempfile::tempdir().unwrap();
                let source = format!(
                    r#"
struct State {{
    std::atomic<int> counter;
    int value;
    alignas(128) std::mutex gate;
    alignas(128) {cv_type} cv;
    void update() {{
        std::lock_guard lock(gate);
        counter.fetch_add(1);
    }}
    void consume() {{
        std::unique_lock lock(gate);
        cv.{wait_method} [this, &lock] {{
            {predicate}
        }});
    }}
}};
"#
                );
                std::fs::write(root.path().join("wait.hpp"), source).unwrap();
                let mut options = false_sharing_detector::types::AnalysisOptions::with_rules(&[
                    RuleId::SameObjectFields,
                ]);
                options.cache_line_size = size;
                let report = false_sharing_detector::cpp_detection::analyze_cpp_path_with_options(
                    root.path(),
                    &options,
                );
                assert!(!report.analysis_incomplete, "{report:#?}");
                assert_eq!(
                    report.findings.iter().any(|finding| {
                        finding.field_list.contains(&"counter".to_owned())
                            && finding.field_list.contains(&"value".to_owned())
                    }),
                    expected,
                    "method={wait_method}, size={size}, cv={cv_type}, predicate={predicate}: {report:#?}"
                );
            }
        }
    }
}

#[test]
fn wait_receiver_does_not_borrow_its_predicates_mutex_protection() {
    let files = parse_cpp_files(vec![CppFile {
        path: "wait.hpp".into(),
        source: r#"
struct State {
    std::mutex gate;
    std::condition_variable cv;
    int value;
    void consume() {
        std::unique_lock lock(gate);
        cv.wait(lock, [this] { return value != 0; });
    }
};
"#
        .into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    for (field, protected) in [("cv", false), ("value", true)] {
        let items = facts
            .iter()
            .flat_map(|facts| &facts.items)
            .filter(|item| item.field_name.as_deref() == Some(field) && item.access_kind.is_some())
            .collect::<Vec<_>>();
        assert!(!items.is_empty(), "missing {field}");
        assert!(
            items
                .iter()
                .all(|item| item.guard_ids.contains(&"gate".to_owned()) == protected),
            "{field}: {items:?}"
        );
    }
}

#[test]
fn preprocessor_replacements_are_not_global_storage_declarations() {
    use false_sharing_detector::cpp_detection::evidence::collect_static_hot_state_candidates;

    let source = r#"
#define GET_BLOCK(p, i) p[i]
#define DECLARE_COUNTERS \
    int counters[8]; \
    {
// mutex_slots[4];
#if FEATURE
std::atomic<int> actual_counters[8];
#else
std::atomic<int> alternative_counters[8];
#endif
namespace nested {
std::mutex actual_locks[8];
}
"#;
    for size in [32, 64, 128] {
        let files = parse_cpp_files(vec![CppFile {
            path: "storage.hpp".into(),
            source: source.into(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", size);
        let candidates = collect_static_hot_state_candidates(&files, &records, size);
        let names = candidates
            .iter()
            .filter_map(|candidate| candidate.field_name.as_deref())
            .collect::<std::collections::HashSet<_>>();
        for phantom in ["p", "counters", "mutex_slots"] {
            assert!(!names.contains(phantom), "{phantom}: {names:?}");
        }
        for actual in ["actual_counters", "alternative_counters", "actual_locks"] {
            assert!(names.contains(actual), "{actual}: {names:?}");
        }
    }
}

#[test]
fn static_array_accessors_respect_block_local_shadowing() {
    use false_sharing_detector::cpp_detection::evidence::collect_static_hot_state_candidates;
    for (body, expected) in [
        ("auto* counters = input;\nreturn &counters[index];", false),
        (
            "std::atomic<int>* counters;\ncounters = input;\nreturn &counters[index];",
            false,
        ),
        ("return &counters[index];", true),
        ("auto* counters = input;\nreturn &::counters[index];", false),
        (
            "{\nauto* counters = input;\ncounters[index]++;\n}\nreturn &counters[index];",
            true,
        ),
        (
            "auto* counters = ::counters;\nreturn &counters[index];",
            true,
        ),
        ("return &counters[index];\nauto* counters = input;", true),
    ] {
        for size in [32, 64, 128] {
            let files = parse_cpp_files(vec![CppFile {
                path: "storage.hpp".into(),
                source: format!(
                    "std::atomic<int> counters[8];\nstd::atomic<int>* select(std::atomic<int>* input, int index) {{\n{body}\n}}\n"
                ),
            }]);
            let records = collect_cpp_structs(&files, "fixture", size);
            let candidates = collect_static_hot_state_candidates(&files, &records, size);
            assert!(
                candidates
                    .iter()
                    .any(|c| c.field_name.as_deref() == Some("counters"))
            );
            if body.contains("return &::counters") {
                // Preserve the existing qualified read evidence; qualification
                // is not yet recognized as a mutable partition accessor.
                assert!(candidates.iter().any(|c| c.access_kind.is_some()));
            }
            assert_eq!(
                candidates.iter().any(|c| c.has_partitioned_index_evidence),
                expected,
                "{body}: {candidates:?}"
            );
        }
    }
}

#[test]
fn source_discovery_does_not_exclude_a_project_filename_prefix() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    for filename in ["state.cpp", "sparse_attention_v2_state.cpp"] {
        let root = tempfile::tempdir().unwrap();
        std::fs::write(
            root.path().join(filename),
            "int slots[8];\nvoid run() { slots[omp_get_thread_num()]++; }",
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::ContiguousElements]),
        );
        assert_eq!(report.scanned_files, 1, "{report:#?}");
        assert!(!report.findings.is_empty(), "{report:#?}");
    }
}

#[test]
fn separate_inline_workers_keep_their_value_object_pair() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    for (receiver, expected) in [("second", false), ("first", true)] {
        let root = tempfile::tempdir().unwrap();
        std::fs::write(
            root.path().join("main.cpp"),
            format!(
                r#"
#include <atomic>
#include <thread>
namespace {{
struct alignas(128) State {{ std::atomic<int> a{{0}}, b{{0}}; }};
State first, second;
void run() {{
 std::thread x([] {{ for(int i=0;i<1000;++i) first.a.fetch_add(1); }}), y([] {{ for(int i=0;i<1000;++i) {receiver}.b.fetch_add(1); }});
 x.join(); y.join();
}}
}}
int main() {{ run(); }}
"#
            ),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(!report.findings.is_empty(), expected, "{report:#?}");
    }
}
