use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
use false_sharing_detector::types::RuleId;
use false_sharing_detector::types::{AnalysisOptions, Report};
use std::fs;
use tempfile::tempdir;

fn analyze(source: &str, cache_line_size: usize, speculative: bool) -> Report {
    let root = tempdir().unwrap();
    fs::write(root.path().join("roles.hpp"), source).unwrap();
    let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
    options.cache_line_size = cache_line_size;
    options.cpp_include_speculative = speculative;
    analyze_cpp_path_with_options(root.path(), &options)
}

#[test]
fn named_thread_entries_do_not_depend_on_declaration_line_breaks() {
    for threads in [
        "\n std::thread a(one,s);\n std::thread b(two,s);\n",
        "std::thread a(one,s); std::thread b(two,s);",
        "std::thread a(one,s), b(two,s);",
        "std::thread a{one,s}; std::thread b{two,s};",
        "std::thread a(\n one,s\n); std::thread b(\n two,s\n);",
        "std::thread a(/* entry */ one, /* receiver */ s); std::thread b(/* entry */ two, s);",
        "std::thread a{ /* entry */ one, s }; std::thread b{ /* entry */ two, s };",
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("entries.cpp"), format!(
            "#include <atomic>\n#include <thread>\nstruct State {{ std::atomic<int> first; std::atomic<int> second; }};\nvoid one(State *s) {{ s->first.fetch_add(1); }}\nvoid two(State *s) {{ s->second.fetch_add(1); }}\nvoid run(State *s) {{ {threads} a.join(); b.join(); }}"
        )).unwrap();
        for cache_line_size in [32, 64, 128] {
            let report = analyze_cpp_path_with_options(
                root.path(),
                &AnalysisOptions {
                    cache_line_size,
                    ..AnalysisOptions::with_rules(&[RuleId::SameObjectFields])
                },
            );
            assert!(!report.analysis_incomplete, "{report:#?}");
            assert!(!report.findings.is_empty(), "{threads}: {report:#?}");
            let finding = &report.findings[0];
            for field in ["first", "second"] {
                assert!(
                    finding
                        .access_evidence
                        .iter()
                        .any(|access| access.field_name.as_deref() == Some(field)
                            && access.in_concurrent_context)
                );
            }
        }
    }
}

#[test]
fn thread_spelling_in_a_string_does_not_make_named_functions_concurrent() {
    let root = tempdir().unwrap();
    fs::write(root.path().join("entries.cpp"),
        "#include <atomic>\nstruct State { std::atomic<int> first; std::atomic<int> second; };\nvoid one(State *s) { s->first.fetch_add(1); }\nvoid two(State *s) { s->second.fetch_add(1); }\nvoid run() { const char *message = \"std::thread worker(one)\"; }"
    ).unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(report.findings.is_empty(), "{report:#?}");
}

#[test]
fn private_scalar_leaf_preserves_entry_lock_across_builtin_operations() {
    for size in [32, 64, 128] {
        for (body, protected) in [
            ("int old = value; value += 1; return old + value;", true),
            ("this->value++; return this->value;", true),
            (
                "int result = 0; for (int i = 0; i < 3; ++i) { result += value; } return result;",
                true,
            ),
            ("if (value > 0) { value -= 1; } return value;", true),
            ("gate.unlock(); value++; return value;", false),
            ("unknown(); value++; return value;", false),
            ("Custom local; value++; return value;", false),
            ("int result = conversion; return value + result;", false),
            // An inner primitive must not hide a later user conversion.
            (
                "{ int conversion = 0; } int result = conversion; return value + result;",
                false,
            ),
        ] {
            for (guard, expected) in [("gate", !protected), ("other_gate", true)] {
                let source = format!(
                    r#"
std::mutex gate;
std::mutex other_gate;
struct Custom {{ operator int(); ~Custom(); }};
class State {{
    std::atomic<int> counter;
    int value;
    Custom conversion;
    int view() {{ {body} }}
public:
    void update() {{
        std::lock_guard lock(gate);
        counter.fetch_add(1);
    }}
    int inspect() {{
        std::lock_guard lock({guard});
        return view();
    }}
}};
"#
                );
                let report = analyze(&source, size, false);
                assert_eq!(
                    !report.findings.is_empty(),
                    expected,
                    "size={size}, guard={guard}, body={body}, {report:#?}"
                );
            }
        }
    }
}

#[test]
fn private_scalar_reader_inherits_only_guards_held_at_every_call() {
    for size in [32, 64, 128] {
        for (extra, guard, getter, expected) in [
            ("", "gate", "int view() { return value; }", false),
            (
                "int unguarded() { return view(); }",
                "gate",
                "int view() { return value; }",
                true,
            ),
            ("", "other_gate", "int view() { return value; }", true),
            ("", "gate", "public: int view() { return value; }", true),
            (
                "",
                "gate",
                "int view() { gate.unlock(); return value; }",
                true,
            ),
        ] {
            let source = format!(
                r#"
std::mutex gate;
std::mutex other_gate;
class State {{
    std::atomic<int> counter;
    int value;
    {getter}
public:
    void update() {{
        std::lock_guard lock(gate);
        counter.fetch_add(1);
    }}
    int inspect() {{
        std::lock_guard lock({guard});
        return view();
    }}
    {extra}
}};
"#
            );
            let report = analyze(&source, size, false);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "size={size}, guard={guard}, getter={getter}, extra={extra}, {report:#?}"
            );
        }
    }
}

#[test]
fn scalar_reader_lock_inheritance_rejects_local_guards_and_unlocked_calls() {
    for inspect in [
        "int inspect(std::mutex & gate) {\n std::lock_guard lock(gate);\n return view();\n }",
        "int inspect() {\n std::mutex gate;\n std::lock_guard lock(gate);\n return view();\n }",
        "int inspect() {\n {\n std::lock_guard lock(gate);\n view();\n }\n return view();\n }",
        "int inspect() {\n std::unique_lock lock(gate);\n lock.unlock();\n return view();\n }",
    ] {
        let source = format!(
            r#"
std::mutex gate;
class State {{
    std::atomic<int> counter;
    int value;
    int view() {{ return value; }}
public:
    void update() {{
        std::lock_guard lock(gate);
        counter.fetch_add(1);
    }}
    {inspect}
}};
"#
        );
        assert!(
            !analyze(&source, 64, false).findings.is_empty(),
            "{inspect}"
        );
    }
}

#[test]
fn runtime_entry_roles_check_locks_on_the_actual_cross_field_conflict() {
    for size in [32, 64, 128] {
        for (guard, expected) in [("gate", false), ("other_gate", true)] {
            let source = format!(
                r#"
std::mutex gate;
std::mutex other_gate;
struct State {{
    std::atomic<int> counter;
    int value;
    void update() {{
        std::lock_guard<std::mutex> lock(gate);
        counter.fetch_add(1);
    }}
    int inspect() {{
        int observed = counter.load();
        std::lock_guard<std::mutex> lock({guard});
        return value + observed;
    }}
}};
"#
            );
            assert_eq!(
                !analyze(&source, size, false).findings.is_empty(),
                expected,
                "size={size}, guard={guard}"
            );
            assert!(!analyze(&source, size, true).findings.is_empty());
        }
    }
}

#[test]
fn conditional_self_calls_open_only_the_bound_records_helpers() {
    for branching_entry in [
        "void run(bool choose) { if (choose) advance(); else observe(); }",
        "void run(bool choose) { if (choose) return; advance(); observe(); }",
    ] {
        let source = format!(
            r#"
class Coupled {{
    std::atomic<int> counter;
    int value;
    void advance() {{ counter.fetch_add(1); }}
    int observe() {{ return value; }}
public:
    void run() {{ advance(); observe(); }}
}};
class Conditional {{
    std::atomic<int> counter;
    int value;
    void advance() {{ counter.fetch_add(1); }}
    int observe() {{ return value; }}
public:
    {branching_entry}
}};
"#
        );
        let report = analyze(&source, 64, false);
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("Coupled"))
        );
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("Conditional"))
        );
        assert!(
            analyze(&source, 64, true)
                .findings
                .iter()
                .any(|f| f.struct_name.as_deref() == Some("Coupled"))
        );
    }
}

#[test]
fn local_data_addresses_do_not_escape_unrelated_same_named_methods() {
    for unrelated in [
        "void unrelated(int advance) { consume(&advance); }",
        "void unrelated() { int advance = 0; consume(&(advance)); }",
        "void unrelated(int advance) { consume(advance); }",
    ] {
        let source = format!(
            r#"
class State {{
    std::atomic<int> left;
    int right;
    void advance() {{ left.fetch_add(1); }}
    int observe() {{ return right; }}
public:
    void run() {{ advance(); observe(); }}
}};
{unrelated}
"#
        );
        assert!(
            analyze(&source, 64, false).findings.is_empty(),
            "{unrelated}"
        );
        assert!(!analyze(&source, 64, true).findings.is_empty());
    }
}

#[test]
fn a_local_same_name_does_not_hide_a_qualified_member_callback() {
    let source = r#"
class State {
    std::atomic<int> left;
    int right;
    void advance() { left.fetch_add(1); }
public:
    auto callback(int advance) { consume(&advance); return &State::advance; }
    int observe() { return right; }
};
"#;
    assert!(!analyze(source, 64, false).findings.is_empty());
}

#[test]
fn decltype_member_addresses_do_not_create_runtime_callbacks() {
    for (declaration, expected) in [
        ("using Callback = decltype(&State::advance);", false),
        ("auto callback() { return &State::advance; }", true),
    ] {
        let source = format!(
            r#"
class State {{
    std::atomic<int> left;
    int right;
    void advance() {{ left.fetch_add(1); }}
    int observe() {{ return right; }}
public:
    {declaration}
    void run() {{ advance(); observe(); }}
}};
"#
        );
        assert_eq!(
            !analyze(&source, 64, false).findings.is_empty(),
            expected,
            "{declaration}"
        );
    }
}

#[test]
fn primitive_local_addresses_do_not_publish_a_constructor_receiver() {
    for (construction, expected) in [
        (
            "State() { int status = 0; query(&status); adjust(); }",
            false,
        ),
        ("State(int status) { query(&(status)); adjust(); }", false),
        ("State() { using Self = decltype(this); adjust(); }", false),
        (
            "State() { using Result = decltype(publish(this)); adjust(); }",
            false,
        ),
        ("State() { query(&right); adjust(); }", true),
        ("State(int &status) { query(&status); adjust(); }", true),
        (
            "State() { int status = 0; { int &status = right; query(&status); } adjust(); }",
            true,
        ),
        (
            "State() { int status = 0;\n#define status right\n query(&status); adjust();\n#undef status\n }",
            true,
        ),
        (
            "State() { State *self = this; query(&self); adjust(); }",
            true,
        ),
    ] {
        let source = format!(
            r#"
class State {{
    std::atomic<int> left;
    int right;
    void adjust() {{ left.fetch_add(1); }}
public:
    {construction}
    int read() {{ return right; }}
}};
"#
        );
        assert_eq!(
            !analyze(&source, 64, false).findings.is_empty(),
            expected,
            "{construction}"
        );
    }
}

#[test]
fn private_helpers_share_their_runtime_entry_instead_of_inventing_thread_roles() {
    for size in [32, 64, 128] {
        for (entries, expected) in [
            ("void run() { advance(); observe(); }", false),
            (
                "void write() { advance(); } int read() { return observe(); }",
                true,
            ),
            ("void run() { forward(); }", false),
            (
                "void write() { forward(); } int read() { return observe(); }",
                true,
            ),
        ] {
            let source = format!(
                r#"
class State {{
    std::atomic<int> left;
    int right;
    void advance() {{ left.fetch_add(1); }}
    int observe() {{ return right; }}
    void forward() {{ advance(); observe(); }}
public:
    {entries}
}};
"#
            );
            assert_eq!(
                !analyze(&source, size, false).findings.is_empty(),
                expected,
                "{size}: {entries}"
            );
            assert!(
                !analyze(&source, size, true).findings.is_empty(),
                "broad candidate retained: {entries}"
            );
        }
    }
}

#[test]
fn parenthesized_self_receivers_preserve_coupled_and_independent_entries() {
    for receiver in ["this->", "(this)->", "(*this).", "(*(this))."] {
        for (separate, expected) in [(false, false), (true, true)] {
            let entry = if separate {
                format!(
                    "void write() {{ {receiver}advance(); }} int read() {{ return {receiver}observe(); }}"
                )
            } else {
                format!("void run() {{ {receiver}advance(); {receiver}observe(); }}")
            };
            let source = format!(
                r#"
class State {{
    std::atomic<int> left;
    int right;
    void advance() {{ left.fetch_add(1); }}
    int observe() {{ return right; }}
public:
    {entry}
}};
"#
            );
            assert_eq!(
                !analyze(&source, 64, false).findings.is_empty(),
                expected,
                "{receiver}: {entry}"
            );
            assert!(!analyze(&source, 64, true).findings.is_empty());
        }
    }
}

#[test]
fn lifecycle_only_helpers_do_not_overlap_an_unrelated_runtime_reader_by_default() {
    for (lifecycle, extra, expected) in [
        ("State() { adjust(); }", "", false),
        ("~State() { adjust(); }", "", false),
        ("~State() { adjust(); }", "void reset() { adjust(); }", true),
        (
            "State() { register_callback([this] { adjust(); }); }",
            "",
            true,
        ),
        (
            "~State() { register_callback([this] { adjust(); }); }",
            "",
            true,
        ),
    ] {
        let source = format!(
            r#"
class State {{
    std::atomic<int> left;
    int right;
    void adjust() {{ left.fetch_add(1); }}
public:
    {lifecycle}
    {extra}
    int read() {{ return right; }}
}};
"#
        );
        let report = analyze(&source, 64, false);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{lifecycle} {extra}: {:?}",
            report.findings
        );
    }
}

#[test]
fn destruction_does_not_hide_other_receivers_or_explicit_worker_access() {
    for source in [
        "struct State { std::atomic<int> left; int right; int read() { return right; } }; struct Lease { State* shared; ~Lease() { shared->left.fetch_add(1); } };",
        "class State { std::atomic<int> left; int right; void adjust() { left.fetch_add(1); } public: ~State() { std::thread worker([this] { adjust(); }); worker.join(); } int read() { return right; } };",
    ] {
        assert!(!analyze(source, 64, false).findings.is_empty(), "{source}");
    }
}

#[test]
fn separate_public_methods_and_escaped_private_methods_remain_potential_roles() {
    for methods in [
        "public: void advance() { left.fetch_add(1); } int observe() { return right; }",
        "void advance() { left.fetch_add(1); } public: auto callback() { return &State::advance; } int observe() { return right; }",
        "protected: void advance() { left.fetch_add(1); } public: int observe() { return right; }",
    ] {
        let source = format!("class State {{ std::atomic<int> left; int right; {methods} }};");
        assert!(
            !analyze(&source, 64, false).findings.is_empty(),
            "{methods}"
        );
    }
}

#[test]
fn out_of_line_private_definitions_follow_declared_visibility_and_public_callers() {
    for (entries, expected) in [
        ("void run() { advance(); observe(); }", false),
        (
            "void run() { advance(); } int read() { return observe(); }",
            true,
        ),
    ] {
        let root = tempdir().unwrap();
        fs::write(root.path().join("state.hpp"), format!("class State {{ std::atomic<int> left; int right; void advance(); int observe(); public: {entries} }}; ")).unwrap();
        fs::write(root.path().join("state.cpp"), "#include \"state.hpp\"\nvoid State::advance() { left.fetch_add(1); }\nint State::observe() { return right; }").unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{entries}: {:?}",
            report.findings
        );
    }
}

#[test]
fn published_receivers_and_initializer_callbacks_do_not_supply_closed_lifetimes() {
    for construction in [
        "State() { publish(this); adjust(); }",
        "State() { publish((this)); (*this).adjust(); }",
        "State() { publish((*this)); (this)->adjust(); }",
        "State() : token(register_owner(this)) { adjust(); }",
        "State() : token(register_callback([this] { adjust(); })) {}",
        "~State() { publish(this); adjust(); }",
    ] {
        let source = format!(
            "class State {{ std::atomic<int> left; int right; int token; void adjust() {{ left.fetch_add(1); }} public: {construction} int read() {{ return right; }} }};"
        );
        assert!(
            !analyze(&source, 64, false).findings.is_empty(),
            "{construction}"
        );
    }
}

#[test]
fn qualified_self_calls_and_recursive_forwarding_keep_runtime_roots() {
    for entry in [
        "void write() { State::advance(); }",
        "void write() { forward(); }",
    ] {
        let source = format!(
            "class State {{ std::atomic<int> left; int right; void advance() {{ left.fetch_add(1); }} void forward() {{ if (ready()) forward(); else advance(); }} public: {entry} int read() {{ return right; }} }};"
        );
        assert!(!analyze(&source, 64, false).findings.is_empty(), "{entry}");
    }
}

#[test]
fn oversized_member_graph_keeps_the_unresolved_candidate() {
    let methods = (0..257)
        .map(|i| format!("void unused_{i}() {{}}\n"))
        .collect::<String>();
    let source = format!(
        "class State {{ std::atomic<int> left; int right; void advance() {{ left.fetch_add(1); }} int observe() {{ return right; }} {methods} public: void run() {{ advance(); observe(); }} }};"
    );
    assert!(
        !analyze(&source, 64, false).findings.is_empty(),
        "the closure limit must not be interpreted as no runtime callers"
    );
}

#[test]
fn entry_roles_are_exposed_without_changing_the_callee_source_identity() {
    let source = "class State { std::atomic<int> left; int right; void advance() { left.fetch_add(1); } int observe() { return right; } public: void write() { advance(); } int read() { return observe(); } };";
    let report = analyze(source, 64, false);
    assert!(!report.findings.is_empty());
    let evidence = report
        .findings
        .iter()
        .flat_map(|f| &f.access_evidence)
        .collect::<Vec<_>>();
    assert!(evidence.iter().any(|a| {
        a.function_name.as_deref() == Some("advance")
            && a.semantic_contexts
                .iter()
                .any(|c| c.starts_with("cpp_runtime_entry:") && c.contains("State::write@"))
    }));
    assert!(
        evidence.iter().all(|a| a.file != "cpp_runtime_entry"),
        "projected roles must never be serialized as source files"
    );
}

#[test]
fn constructor_overloads_and_destructor_do_not_collide_as_runtime_entries() {
    for extra in ["", "void reset() { adjust(); }"] {
        let source = format!(
            r#"
class State {{
    std::atomic<int> left;
    int right;
    void adjust() {{ left.fetch_add(1); }}
public:
    State() {{ adjust(); }}
    State(int value) {{ adjust(); }}
    ~State() {{ adjust(); }}
    int read() {{ return right; }}
    {extra}
}};
"#
        );
        assert_eq!(
            !analyze(&source, 64, false).findings.is_empty(),
            !extra.is_empty(),
            "{extra}"
        );
    }
}

#[test]
fn local_callable_shadows_do_not_create_member_call_edges() {
    let source = r#"
class State {
    std::atomic<int> left;
    int right;
public:
    void writer(void (*reader)()) { reader(); left.fetch_add(1); }
    int reader(void (*writer)()) { writer(); return right; }
};
"#;
    assert!(!analyze(source, 64, false).findings.is_empty());
}

#[test]
fn publication_in_a_private_helper_keeps_lifetime_overlap_unresolved() {
    let source = "class State { std::atomic<int> left; int right; void adjust() { publish(this); left.fetch_add(1); } public: State() { adjust(); } int read() { return right; } };";
    assert!(!analyze(source, 64, false).findings.is_empty());
}

#[test]
fn templated_private_calls_do_not_become_unreachable_by_omission() {
    let source = "class State { std::atomic<int> left; int right; template<class T> void adjust() { left.fetch_add(1); } public: void write() { adjust<int>(); } int read() { return right; } };";
    assert!(!analyze(source, 64, false).findings.is_empty());
}

#[test]
fn alternative_runtime_branches_are_not_a_coupled_role() {
    let source = "class State { std::atomic<int> left; int right; void advance() { left.fetch_add(1); } int observe() { return right; } public: int run(bool update) { if (update) { advance(); return 0; } else { return observe(); } } };";
    assert!(!analyze(source, 64, false).findings.is_empty());
}

#[test]
fn early_returns_do_not_turn_partial_invocations_into_coupled_roles() {
    let source = "class State { std::atomic<int> left; int right; void advance() { left.fetch_add(1); } int observe() { return right; } public: int run(bool update) { if (!update) return observe(); advance(); return observe(); } };";
    assert!(!analyze(source, 64, false).findings.is_empty());
}

#[test]
fn short_circuit_calls_remain_distinct_possible_roles() {
    for expression in [
        "update && advance() || observe()",
        "update and advance() or observe()",
    ] {
        let source = format!(
            "class State {{ std::atomic<int> left; int right; bool advance() {{ left.fetch_add(1); return true; }} bool observe() {{ return right; }} public: bool run(bool update) {{ return {expression}; }} }};"
        );
        assert!(
            !analyze(&source, 64, false).findings.is_empty(),
            "{expression}"
        );
    }
}

#[test]
fn overloaded_entries_on_one_line_keep_distinct_source_identities() {
    let source = "class State { std::atomic<int> left; int right; void advance() { left.fetch_add(1); } int observe() { return right; } public: void run(int) { advance(); } int run(double) { return observe(); } };";
    assert!(!analyze(source, 64, false).findings.is_empty());
}

#[test]
fn unrelated_object_and_callback_calls_do_not_open_private_roles() {
    for extra in [
        "struct Other { void advance(); int observe(); }; void unrelated(Other& o) { o.advance(); o.observe(); }",
        "struct Other { void advance(); int observe(); void run() { queue([this] { advance(); observe(); }); } };",
        "struct Other { void advance(); int observe(); void run(Other& o) { o.advance(); o.observe(); } };",
    ] {
        for size in [32, 64, 128] {
            let source = format!(
                r#"
class Coupled {{
    std::atomic<int> counter;
    int value;
    void advance() {{ counter.fetch_add(1); }}
    int observe() {{ return value; }}
public:
    void run() {{ advance(); observe(); }}
}};
{extra}
"#
            );
            let report = analyze(&source, size, false);
            assert!(
                !report
                    .findings
                    .iter()
                    .any(|f| f.struct_name.as_deref() == Some("Coupled")),
                "{extra}: {report:#?}"
            );
            assert!(!analyze(&source, size, true).findings.is_empty());
        }
    }
}

#[test]
fn private_calls_keep_same_class_nested_class_friend_and_address_escapes() {
    for extra in [
        "public: void other(Coupled& o) { o.advance(); }",
        "public: void callback() { queue([this] { advance(); }); }",
        "public: struct Nested { void other(Coupled& o) { o.advance(); } };",
        "friend void other(Coupled&);",
        "public: auto callback() { return &Coupled::advance; }",
        "public: void writer() { advance(); } int reader() { return observe(); }",
    ] {
        let source = format!(
            r#"
class Coupled {{
    std::atomic<int> counter;
    int value;
    void advance() {{ counter.fetch_add(1); }}
    int observe() {{ return value; }}
public:
    void run() {{ advance(); observe(); }}
    {extra}
}};
"#
        );
        assert!(!analyze(&source, 64, false).findings.is_empty(), "{extra}");
    }
}

#[test]
fn conditional_private_helpers_need_runtime_reachability() {
    for body in [
        "if (ready()) return; counter.fetch_add(1);",
        "if (ready()) advance();",
        "while (ready()) advance();",
    ] {
        for (entry, expected) in [
            ("State() { prepare(); }", false),
            ("~State() { prepare(); }", false),
            ("State() { prepare(); } void update() { prepare(); }", true),
            (
                "State() { prepare(); } auto callback() { return &State::prepare; }",
                true,
            ),
        ] {
            let source = format!(
                r#"
class State {{
    std::atomic<int> counter;
    int value;
    void advance() {{ counter.fetch_add(1); }}
    void prepare() {{ {body} }}
public:
    {entry}
    int observe() {{ return value; }}
}};
"#
            );
            assert_eq!(
                !analyze(&source, 64, false).findings.is_empty(),
                expected,
                "{body}, {entry}"
            );
        }
    }
}

#[test]
fn out_of_line_nested_methods_keep_access_to_enclosing_private_helpers() {
    for member in ["", "int token;"] {
        let root = tempdir().unwrap();
        fs::write(
            root.path().join("state.hpp"),
            format!(
                r#"
namespace Domain {{
class State {{
    std::atomic<int> counter;
    int value;
    void advance() {{ counter.fetch_add(1); }}
    int observe() {{ return value; }}
public:
    struct Nested {{ {member} void write(State&); }};
    void run() {{ advance(); observe(); }}
}};
}}
"#
            ),
        )
        .unwrap();
        fs::write(
            root.path().join("state.cpp"),
            "namespace Domain { void State::Nested::write(State& state) { state.advance(); } }",
        )
        .unwrap();
        let options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
        assert!(
            !analyze_cpp_path_with_options(root.path(), &options)
                .findings
                .is_empty(),
            "{member}"
        );
    }
}

#[test]
fn visibility_rewriting_macros_prevent_private_entry_closure() {
    let source = r#"
#define private public
class State {
private:
    std::atomic<int> counter;
    int value;
    void advance() { counter.fetch_add(1); }
    int observe() { return value; }
public:
    void run() { advance(); observe(); }
};
void external(State& state) { state.advance(); }
"#;
    assert!(!analyze(source, 64, false).findings.is_empty());
}
