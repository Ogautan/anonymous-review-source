use false_sharing_detector::cpp_detection::initialization::{
    FreshInitializationRange, collect_initialization_facts,
};
use false_sharing_detector::cpp_detection::parser::parse_cpp_files;
use false_sharing_detector::cpp_detection::types::CppFile;
use false_sharing_detector::types::RuleId;

fn ranges(source: &str) -> Vec<FreshInitializationRange> {
    let files = parse_cpp_files(vec![CppFile {
        path: "candidate.cpp".to_string(),
        source: source.to_string(),
    }]);
    collect_initialization_facts(&files)
        .remove("candidate.cpp")
        .unwrap()
}

fn covers(ranges: &[FreshInitializationRange], source: &str, marker: &str) -> bool {
    let offset = source.find(marker).expect("marker exists");
    ranges
        .iter()
        .any(|range| range.contains("p", range.declaration, offset))
}

#[test]
fn automatic_scalar_storage_is_private_until_its_first_handoff() {
    let source = r#"
        struct State { int hits; int misses; void log(); };
        void create() {
            State p;
            unrelated_work();
            p.hits = 1;
            p.misses = 2;
            p.log();
            p.hits++;
        }
    "#;
    let facts = ranges(source);
    assert!(covers(&facts, source, "p.hits = 1"), "{facts:?}");
    assert!(covers(&facts, source, "p.misses = 2"));
    assert!(!covers(&facts, source, "p.hits++"));
}

#[test]
fn empty_constructor_with_literal_scalar_initializers_does_not_publish_local_storage() {
    let source = r#"
        class Logger {
            struct Entry {
                enum Stage { Start, Stop };
                Entry() : result(0) {}
                int64_t result;
                uint32_t hits;
                uint8_t misses;
                void log(void *file) { consume(this, file); }
            };
            void write(Entry::Stage stage);
        };
        void Logger::write(Entry::Stage stage) {
            Entry p;
            p.hits = 1;
            p.misses = 2;
            p.log(file);
            p.hits++;
        }
    "#;
    let facts = ranges(source);
    assert!(covers(&facts, source, "p.hits = 1"), "{facts:?}");
    assert!(covers(&facts, source, "p.misses = 2"));
    assert!(!covers(&facts, source, "p.hits++"));
}

#[test]
fn automatic_storage_requires_a_proved_nonpublishing_constructor_and_members() {
    for definition in [
        "State() { publish(this); } int hits; int misses;",
        "State() : hits(publish(this)), misses(0) {} int hits; int misses;",
        "State() : State(0) {} State(int) {} int hits; int misses;",
        "int hits = publish(this); int misses;",
        "Worker worker; int hits; int misses;",
        "State(); int hits; int misses;",
        "State(int unused = publish_global()) {} int hits; int misses;",
        "virtual void work(); int hits; int misses;",
    ] {
        let source = format!(
            "struct Worker {{ Worker() {{ publish(this); }} }}; struct State {{ {definition} }}; void f() {{ State p; p.hits = 1; p.misses = 2; }}"
        );
        assert!(!covers(&ranges(&source), &source, "p.hits"), "{definition}");
    }
    let base = "struct Base { Base(){publish(this);} }; struct State: Base {int hits; int misses;}; void f(){State p; p.hits = 1;}";
    assert!(!covers(&ranges(base), base, "p.hits"));
}

#[test]
fn automatic_values_end_at_alias_address_capture_and_member_reference_calls() {
    for handoff in [
        "State &alias = p;",
        "auto address = &p;",
        "(void)&p;",
        "unknown(p);",
        "unknown(p.hits);",
        "auto callback = [&p] { return p.hits; };",
        "auto callback = [=] { return p.hits; };",
    ] {
        let source = format!(
            "struct State {{ int hits; int misses; }}; void f() {{ State p; p.hits = 1; {handoff} p.misses = 2; }}"
        );
        let facts = ranges(&source);
        // Captured returns are conservatively rejected along with NRVO until a
        // result-slot analysis can distinguish their lifetime from this object.
        if !handoff.contains("return") {
            assert!(
                covers(&facts, &source, "p.hits = 1"),
                "{handoff}: {facts:?}"
            );
        }
        assert!(!covers(&facts, &source, "p.misses"), "{handoff}: {facts:?}");
    }
}

#[test]
fn automatic_values_cannot_be_revisited_after_a_loop_handoff() {
    let source = "struct State { int hits; int misses; }; void f() { State p; while(active) { p.hits = 1; publish(&p); } }";
    assert!(!covers(&ranges(source), source, "p.hits"));
    let fresh_each_turn = "struct State { int hits; int misses; }; void f() { while(active) { State p; p.hits = 1; publish(&p); } }";
    assert!(covers(&ranges(fresh_each_turn), fresh_each_turn, "p.hits"));
    let nonlocal_jump = "struct State { int hits; int misses; }; void f() { State p; setjmp(env); p.hits = 1; publish(&p); longjmp(env, 1); }";
    assert!(!covers(&ranges(nonlocal_jump), nonlocal_jump, "p.hits"));
}

#[test]
fn automatic_value_return_does_not_assume_a_fresh_caller_result_slot() {
    for value in ["p", "std::move(p)", "(State&&)p"] {
        let source = format!(
            "struct State {{ int hits; int misses; }}; State f() {{ State p; p.hits = 1; p.misses = 2; return {value}; }}"
        );
        assert!(!covers(&ranges(&source), &source, "p.hits"), "{value}");
    }
}

#[test]
fn automatic_ranges_exclude_existing_reference_static_array_and_ambiguous_storage() {
    for declaration in [
        "State &p = existing",
        "static State p",
        "const static State p",
        "thread_local State p",
        "extern State p",
        "State p[2]",
        "State p = existing",
    ] {
        let source = format!(
            "struct State {{ int hits; int misses; }}; void f() {{ {declaration}; p.hits = 1; }}"
        );
        assert!(
            !covers(&ranges(&source), &source, "p.hits"),
            "{declaration}"
        );
    }
    let ambiguous = "namespace one { struct State { int hits; }; } namespace two { struct State { State(){publish(this);} int hits; }; } void f(){ State p; p.hits = 1; }";
    assert!(!covers(&ranges(ambiguous), ambiguous, "p.hits"));
}

#[test]
fn automatic_storage_does_not_assume_macro_or_alias_type_spellings_are_scalar() {
    for redirect in [
        "using int64_t = Worker;",
        "typedef Worker int64_t;",
        "#define int64_t Worker\n",
    ] {
        let source = format!(
            "struct Worker {{ Worker(){{publish(this);}} }}; {redirect}\nstruct State {{ int64_t hits; int misses; }}; void f() {{ State p; p.hits = 1; }}"
        );
        assert!(!covers(&ranges(&source), &source, "p.hits"), "{redirect}");
    }
    let source = "struct State { int hits; int misses; }; struct Worker { Worker(){publish(this);} int hits; }; void f() { typedef Worker State; State p; p.hits = 1; }";
    assert!(!covers(&ranges(source), source, "p.hits"));
    let scalar = "typedef unsigned long uint32_t; struct State { uint32_t hits; int misses; }; void f(){State p; p.hits = 1;}";
    assert!(covers(&ranges(scalar), scalar, "p.hits"));
    let nontrivial = "struct int64_t { int64_t(){publish(this);} }; struct State { int64_t hits; int misses; }; void f(){State p; p.hits = 1;}";
    assert!(!covers(&ranges(nontrivial), nontrivial, "p.hits"));
    let unrelated_alias = "struct Worker { Worker(){publish(this);} }; using Pointee = Worker; void other(){using result = Worker;} struct State { State():result(0){} int result; Pointee *ptr; int hits; }; void f(){State p; p.hits = 1;}";
    assert!(covers(&ranges(unrelated_alias), unrelated_alias, "p.hits"));
}

#[test]
fn automatic_value_ranges_reach_access_evidence_without_hiding_post_handoff_writes() {
    use false_sharing_detector::cpp_detection::evidence::collect_cpp_evidence;
    use false_sharing_detector::cpp_detection::layout::collect_cpp_structs;
    let source = r#"
        struct State { int hits; int misses; State():hits(0){} void log(); };
        void f() {
            State p;
            p.hits = 1;
            p.misses = 2;
            p.log(); p.hits++;
        }
    "#;
    let files = parse_cpp_files(vec![CppFile {
        path: "candidate.cpp".to_string(),
        source: source.to_string(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let evidence = collect_cpp_evidence(&files, &records);
    assert!(
        evidence[0]
            .items
            .iter()
            .any(|item| item.field_name.as_deref() == Some("hits")
                && item.description.contains("p.hits = 1")
                && item.initialization_phase),
        "{evidence:#?}"
    );
    assert!(
        evidence[0]
            .items
            .iter()
            .any(|item| item.field_name.as_deref() == Some("hits")
                && item.description.contains("p.hits++")
                && !item.initialization_phase),
        "{evidence:#?}"
    );
}

#[test]
fn source_macro_implicit_local_capture_ends_automatic_initialization() {
    let source = r#"
        #define HIDDEN() publish(&p)
        #define WRAP() HIDDEN()
        struct State { int hits; int misses; };
        void f() { State p; p.hits = 1; WRAP(); p.misses = 2; }
    "#;
    let facts = ranges(source);
    assert!(covers(&facts, source, "p.hits"));
    assert!(!covers(&facts, source, "p.misses"), "{facts:?}");
    let unrelated = r#"
        #define OTHER(p) consume(p)
        struct State { int hits; int misses; };
        void f() { State p; OTHER(other_object); p.hits = 1; }
    "#;
    assert!(covers(&ranges(unrelated), unrelated, "p.hits"));
}

#[test]
fn fresh_malloc_writes_end_at_the_exact_publication_byte() {
    let source = r#"
        struct State { int hits; int misses; };
        State *global;
        State *create() {
            State *p = (State *)malloc(sizeof(State));
            p->hits = 1; global = p; p->misses = 2;
            return p;
        }
    "#;
    let facts = ranges(source);
    assert!(covers(&facts, source, "p->hits"));
    assert!(!covers(&facts, source, "p->misses"));
}

#[test]
fn simple_allocation_wrappers_and_macros_are_proved_from_other_files() {
    let source = r#"
        #include "allocation.h"
        struct State { int hits; int misses; };
        State *create() {
            State *p = ZEROED(State);
            p->hits = 1;
            p->misses = 2;
            return p;
        }
    "#;
    let files = parse_cpp_files(vec![
        CppFile {
            path: "allocation.h".to_string(),
            source: "#define ZEROED(type) (type *)(checked_zero(sizeof(type)))\n".to_string(),
        },
        CppFile {
            path: "allocation.c".to_string(),
            source: r#"
            void *checked_zero(size_t size) {
                void *allocation;
                if (size == 0) return nullptr;
                allocation = calloc(size, 1);
                if (!allocation) abort();
                return allocation;
            }
        "#
            .to_string(),
        },
        CppFile {
            path: "candidate.cpp".to_string(),
            source: source.to_string(),
        },
    ]);
    let facts = collect_initialization_facts(&files)
        .remove("candidate.cpp")
        .unwrap();
    assert!(covers(&facts, source, "p->hits"), "{facts:?}");
    assert!(covers(&facts, source, "p->misses"));
}

#[test]
fn wrapper_that_publishes_storage_cannot_prove_fresh_unpublished_result() {
    let source = r#"
        struct State { int hits; int misses; };
        void *published;
        void *allocate(size_t size) {
            void *allocation = malloc(size);
            published = allocation;
            return allocation;
        }
        State *create() {
            State *p = (State *)allocate(sizeof(State));
            p->hits = 1;
            p->misses = 2;
            return p;
        }
    "#;
    assert!(!covers(&ranges(source), source, "p->hits"));
}

#[test]
fn allocation_names_and_unknown_constructors_are_not_freshness_proofs() {
    for initializer in [
        "new State",
        "realloc(global, sizeof(State))",
        "unknown_allocate()",
        "external::malloc(sizeof(State))",
    ] {
        let source = format!(
            "struct State {{ int hits; int misses; }}; State *global; void create() {{ State *p = (State *){initializer}; p->hits = 1; p->misses = 2; }}"
        );
        assert!(
            !covers(&ranges(&source), &source, "p->hits"),
            "{initializer}"
        );
    }
}

#[test]
fn possible_alias_callback_and_unknown_reference_callee_end_initialization() {
    for escape in [
        "auto alias = p;",
        "unknown(p);",
        "unknown(p->hits);",
        "auto callback = [=] { return p->hits; };",
        "free(p);",
        "p = global;",
    ] {
        let source = format!(
            "struct State {{ int hits; int misses; }}; State *global; void create() {{ State *p = (State *)malloc(sizeof(State)); p->hits = 1; {escape} p->misses = 2; }}"
        );
        let facts = ranges(&source);
        assert!(
            covers(&facts, &source, "p->hits = 1"),
            "{escape}: {facts:?}"
        );
        assert!(!covers(&facts, &source, "p->misses"), "{escape}: {facts:?}");
    }
}

#[test]
fn a_loop_can_revisit_earlier_writes_after_publication() {
    let source = r#"
        struct State { int hits; int misses; };
        void create() {
            State *p = (State *)malloc(sizeof(State));
            while (active) {
                p->hits = 1;
                publish(p);
            }
        }
    "#;
    assert!(!covers(&ranges(source), source, "p->hits"));
    let per_iteration = r#"
        struct State { int hits; int misses; };
        void create() {
            while (active) {
                State *p = (State *)malloc(sizeof(State));
                p->hits = 1;
                publish(p);
            }
        }
    "#;
    assert!(covers(&ranges(per_iteration), per_iteration, "p->hits"));
}

#[test]
fn conditional_allocation_cannot_initialize_an_already_published_pointer() {
    let source = r#"
        struct State { int hits; int misses; };
        State *global;
        void update() {
            State *p = global;
            if (condition) p = (State *)malloc(sizeof(State));
            p->hits = 1;
            p->misses = 2;
        }
    "#;
    assert!(!covers(&ranges(source), source, "p->hits"));
}

#[test]
fn shadowed_receivers_require_the_exact_declaration_identity() {
    let source = r#"
        struct State { int hits; int misses; };
        State *global;
        void create() {
            State *p = (State *)malloc(sizeof(State));
            p->hits = 1;
            {
                State *p = global;
                p->misses = 2;
            }
        }
    "#;
    let facts = ranges(source);
    let shadow_declaration = source.find("State *p = global").unwrap();
    let shadow_access = source.find("p->misses").unwrap();
    assert!(
        !facts
            .iter()
            .any(|range| range.contains("p", shadow_declaration, shadow_access))
    );
}

#[test]
fn standard_memory_operations_are_synchronous_but_local_callable_names_are_not() {
    let source = r#"
        struct State { int hits; int misses; };
        void create() {
            State *p = (State *)calloc(1, sizeof(State));
            memset(p, 0, sizeof(State));
            p->hits = 1;
        }
    "#;
    assert!(covers(&ranges(source), source, "p->hits"));
    let shadow = source.replace(
        "void create()",
        "void create(void (*memset)(void *, int, size_t))",
    );
    assert!(!covers(&ranges(&shadow), &shadow, "p->hits"));
}

#[test]
fn published_same_line_accesses_are_runtime_evidence() {
    use false_sharing_detector::cpp_detection::evidence::collect_cpp_evidence;
    use false_sharing_detector::cpp_detection::layout::collect_cpp_structs;
    let source = r#"
        #define ALLOC_RECORD(type) ((type *)calloc(1, sizeof(type)))
        struct State { int counter; int state; };
        State *published;
        State *make() {
            State *value = ALLOC_RECORD(State);
            value->counter = 1;
            value->state = 2;
            published = value; value->counter++; value->state++;
            return value;
        }
        int first(State *value) { return value->counter; }
        int second(State *value) { return value->state; }
    "#;
    let files = parse_cpp_files(vec![CppFile {
        path: "candidate.cpp".to_string(),
        source: source.to_string(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let evidence = collect_cpp_evidence(&files, &records);
    for field in ["counter", "state"] {
        assert!(
            evidence[0].items.iter().any(|item| {
                item.field_name.as_deref() == Some(field)
                    && item.description.contains("published = value")
                    && !item.initialization_phase
            }),
            "{evidence:#?}"
        );
    }
}

#[test]
fn macro_statements_and_ambiguous_allocator_names_do_not_prove_freshness() {
    let fixture = |definitions: &str, call: &str| {
        format!(
            "struct State {{ int hits; int misses; }}; State *global;\n{definitions}\nvoid create() {{ State *p = (State *){call}; p->hits = 1; }}"
        )
    };
    for (definitions, call) in [
        (
            "#define ALLOC(type) malloc(sizeof(type)); global = p",
            "ALLOC(State)",
        ),
        ("#define malloc shared_allocator", "malloc(sizeof(State))"),
        (
            "#define ALLOC(type) malloc(sizeof(type))\n#undef ALLOC",
            "ALLOC(State)",
        ),
        (
            "#define ALLOC(type) malloc(sizeof(type))\nvoid *ALLOC(size_t);",
            "ALLOC(State)",
        ),
        (
            "void *allocate(size_t n) { return malloc(n); }\nnamespace other { void *allocate(size_t); }",
            "allocate(sizeof(State))",
        ),
        (
            "#define ALLOC(malloc) malloc(sizeof(State))",
            "ALLOC(unknown_allocator)",
        ),
    ] {
        let source = fixture(definitions, call);
        assert!(
            !covers(&ranges(&source), &source, "p->hits"),
            "{definitions}"
        );
    }
}

#[test]
fn allocation_macro_requires_an_unconditional_resolved_include_before_use() {
    let write = "State *p = (State *)ALLOC(State); p->hits = 1;";
    let header = "#define ALLOC(type) ((type *)calloc(1, sizeof(type)))\n";
    for (prefix, expected) in [
        ("#include \"allocation.h\"\n", true),
        ("", false),
        ("#include <allocation.h>\n", false),
        ("#if FEATURE\n#include \"allocation.h\"\n#endif\n", false),
        ("#include \"missing/allocation.h\"\n", false),
        ("#include \"../allocation.h\"\n", false),
    ] {
        let source = format!(
            "{prefix}struct State {{ int hits; int misses; }}; void create() {{ {write} }}"
        );
        let files = parse_cpp_files(vec![
            CppFile {
                path: "allocation.h".to_string(),
                source: header.to_string(),
            },
            CppFile {
                path: "candidate.cpp".to_string(),
                source: source.clone(),
            },
        ]);
        let facts = collect_initialization_facts(&files)
            .remove("candidate.cpp")
            .unwrap();
        assert_eq!(covers(&facts, &source, "p->hits"), expected, "{prefix}");
    }
    let source = format!(
        "struct State {{ int hits; int misses; }}; void before() {{ {write} }}\n#include \"allocation.h\"\nvoid after() {{ State *p = ALLOC(State); p->misses = 2; }}"
    );
    let files = parse_cpp_files(vec![
        CppFile {
            path: "allocation.h".to_string(),
            source: header.to_string(),
        },
        CppFile {
            path: "candidate.cpp".to_string(),
            source: source.clone(),
        },
    ]);
    let facts = collect_initialization_facts(&files)
        .remove("candidate.cpp")
        .unwrap();
    assert!(!covers(&facts, &source, "p->hits"));
    assert!(covers(&facts, &source, "p->misses"));
}

#[test]
fn header_guards_preserve_macro_visibility_but_configuration_conditions_do_not() {
    for (header, prefix, expected) in [
        (
            "#ifndef ALLOCATION_H\n#define ALLOCATION_H\n#define ALLOC(type) ((type*)calloc(1, sizeof(type)))\n#endif",
            "",
            true,
        ),
        (
            "#ifndef ALLOCATION_H\n#define ALLOCATION_H\n#define ALLOC(type) ((type*)calloc(1, sizeof(type)))\n#endif",
            "#define ALLOCATION_H\n",
            false,
        ),
        (
            "#ifndef ALLOCATION_H\n#define ALLOCATION_H\n#define ALLOC(type) ((type*)calloc(1, sizeof(type)))\n#endif",
            "#undef ALLOCATION_H\n",
            false,
        ),
        (
            "#if CONFIG\n#define ALLOC(type) ((type*)calloc(1, sizeof(type)))\n#endif",
            "",
            false,
        ),
        (
            "#ifndef ALLOCATION_H\n#define ALLOCATION_H\n#if CONFIG\n#define ALLOC(type) ((type*)calloc(1, sizeof(type)))\n#endif\n#endif",
            "",
            false,
        ),
        (
            "#ifndef ALLOCATION_H\n#define OTHER_H\n#define ALLOC(type) ((type*)calloc(1, sizeof(type)))\n#endif",
            "",
            false,
        ),
    ] {
        let source = format!(
            "{prefix}#include \"allocation.h\"\nstruct State {{ int hits; }};\nvoid create() {{ State *p = ALLOC(State); p->hits = 1; }}"
        );
        let files = parse_cpp_files(vec![
            CppFile {
                path: "allocation.h".to_owned(),
                source: header.to_owned(),
            },
            CppFile {
                path: "candidate.cpp".to_owned(),
                source: source.clone(),
            },
        ]);
        let facts = collect_initialization_facts(&files)
            .remove("candidate.cpp")
            .unwrap();
        assert_eq!(
            covers(&facts, &source, "p->hits"),
            expected,
            "{header} {prefix}: {facts:?}"
        );
    }
}

#[test]
fn colliding_header_guards_do_not_establish_allocation_macro_visibility() {
    let source = "#include \"allocation.h\"\nstruct State { int hits; };\nvoid create() { State *p = ALLOC(State); p->hits = 1; }";
    let files = parse_cpp_files(vec![
        CppFile { path: "allocation.h".to_owned(), source: "#ifndef SHARED_GUARD\n#define SHARED_GUARD\n#define ALLOC(type) ((type*)calloc(1, sizeof(type)))\n#endif".to_owned() },
        CppFile { path: "other.h".to_owned(), source: "#ifndef SHARED_GUARD\n#define SHARED_GUARD\nvoid other();\n#endif".to_owned() },
        CppFile { path: "candidate.cpp".to_owned(), source: source.to_owned() },
    ]);
    let facts = collect_initialization_facts(&files)
        .remove("candidate.cpp")
        .unwrap();
    assert!(!covers(&facts, source, "p->hits"));
}

#[test]
fn macro_definition_order_and_conditional_definition_remain_unknown() {
    let source = r#"
        struct State { int hits; int misses; };
        void before() { State *p = (State *)ALLOC(State); p->hits = 1; }
        #define ALLOC(type) ((type *)malloc(sizeof(type)))
        void after() { State *p = ALLOC(State); p->misses = 2; }
    "#;
    let facts = ranges(source);
    assert!(!covers(&facts, source, "p->hits"));
    assert!(covers(&facts, source, "p->misses"));
    let conditional = source.replace(
        "#define ALLOC(type) ((type *)malloc(sizeof(type)))",
        "#if FEATURE\n#define ALLOC(type) ((type *)malloc(sizeof(type)))\n#endif",
    );
    assert!(!covers(&ranges(&conditional), &conditional, "p->misses"));
}

#[test]
fn transitive_includes_work_without_propagating_through_an_include_cycle() {
    let source = "#include \"middle.h\"\nstruct State { int hits; int misses; }; void create() { State *p = (State *)ALLOC(State); p->hits = 1; }";
    let middle = "#include \"allocation.h\"\n";
    let header = "#define ALLOC(type) ((type *)calloc(1, sizeof(type)))\n";
    let files = parse_cpp_files(vec![
        CppFile {
            path: "allocation.h".to_string(),
            source: header.to_string(),
        },
        CppFile {
            path: "middle.h".to_string(),
            source: middle.to_string(),
        },
        CppFile {
            path: "candidate.cpp".to_string(),
            source: source.to_string(),
        },
    ]);
    assert!(covers(
        &collect_initialization_facts(&files)["candidate.cpp"],
        source,
        "p->hits"
    ));
    let cyclic = format!("#pragma once\n#include \"candidate.cpp\"\n{header}");
    let files = parse_cpp_files(vec![
        CppFile {
            path: "allocation.h".to_string(),
            source: cyclic,
        },
        CppFile {
            path: "middle.h".to_string(),
            source: middle.to_string(),
        },
        CppFile {
            path: "candidate.cpp".to_string(),
            source: source.to_string(),
        },
    ]);
    assert!(!covers(
        &collect_initialization_facts(&files)["candidate.cpp"],
        source,
        "p->hits"
    ));
}

#[test]
fn static_allocation_wrapper_summary_is_confined_to_its_definition_file() {
    let source = "struct State { int hits; int misses; }; void create() { State *p = (State *)allocate(sizeof(State)); p->hits = 1; }";
    let wrapper = "static\nvoid *allocate(size_t size) { return calloc(1, size); }\n";
    let owner_source = format!("{wrapper}{source}");
    let files = parse_cpp_files(vec![
        CppFile {
            path: "owner.cpp".to_string(),
            source: owner_source.clone(),
        },
        CppFile {
            path: "unrelated.cpp".to_string(),
            source: source.to_string(),
        },
    ]);
    let facts = collect_initialization_facts(&files);
    assert!(covers(&facts["owner.cpp"], &owner_source, "p->hits"));
    assert!(!covers(&facts["unrelated.cpp"], source, "p->hits"));
}

#[test]
fn nonalias_allocation_attributes_are_distinct_from_size_and_deallocator_annotations() {
    for (declaration, expected) in [
        (
            "__attribute__((malloc, alloc_size(1))) void *reserve(size_t n);",
            true,
        ),
        ("void *reserve(size_t n) __attribute__((__malloc__));", true),
        ("[[gnu::malloc]] void *reserve(size_t n);", true),
        (
            "__attribute__((malloc, malloc(release, 1))) void *reserve(size_t n);",
            true,
        ),
        (
            "__attribute__((malloc(release, 1))) void *reserve(size_t n);",
            false,
        ),
        (
            "__attribute__((alloc_size(1), returns_nonnull)) void *reserve(size_t n);",
            false,
        ),
        (
            "__attribute__((warning(\"malloc\"))) void *reserve(size_t n);",
            false,
        ),
        ("void *reserve(size_t n __attribute__((malloc)));", false),
        ("__attribute__((malloc)) void *(*reserve)(size_t n);", false),
    ] {
        let source = format!(
            "{declaration}\nstruct State {{ int hits; int misses; }};\nvoid create() {{\nState *p = (State *)reserve(sizeof(State));\np->hits = 1;\npublish(p);\np->misses = 2;\n}}\n"
        );
        let facts = ranges(&source);
        assert_eq!(
            covers(&facts, &source, "p->hits"),
            expected,
            "{declaration}: {facts:?}"
        );
        assert!(
            !covers(&facts, &source, "p->misses"),
            "publication must end freshness"
        );
    }
}

#[test]
fn allocation_attribute_contracts_require_visible_unambiguous_declarations() {
    let declaration = "__attribute__((malloc)) void *reserve(size_t n);\n";
    for (header, prefix, extra, expected) in [
        (
            declaration.to_owned(),
            "#include \"contract.h\"\n",
            "",
            true,
        ),
        (
            format!("#ifndef CONTRACT_H\n#define CONTRACT_H\n{declaration}#endif\n"),
            "#include \"contract.h\"\n",
            "",
            true,
        ),
        (declaration.to_owned(), "", "", false),
        (
            format!("#if FEATURE\n{declaration}#endif\n"),
            "#include \"contract.h\"\n",
            "",
            false,
        ),
        (
            declaration.to_owned(),
            "#if FEATURE\n#include \"contract.h\"\n#endif\n",
            "",
            false,
        ),
        (
            declaration.to_owned(),
            "#define __attribute__(x)\n#include \"contract.h\"\n",
            "",
            false,
        ),
        (
            declaration.to_owned(),
            "#define malloc inert\n#include \"contract.h\"\n",
            "",
            false,
        ),
        (
            declaration.to_owned(),
            "#define malloc(n) other(n)\n#include \"contract.h\"\n",
            "",
            true,
        ),
        (
            declaration.to_owned(),
            "#include \"contract.h\"\n",
            "namespace other { void *reserve(size_t); }",
            false,
        ),
        (
            declaration.to_owned(),
            "#include \"contract.h\"\n",
            "void *reserve(const char *);",
            false,
        ),
        (
            declaration.to_owned(),
            "#include \"contract.h\"\n",
            "void *reserve_alias;\n#define reserve(x) reserve_alias",
            false,
        ),
    ] {
        let source = format!(
            "{prefix}{extra}\nstruct State {{ int hits; int misses; }};\nvoid create() {{\nState *p = (State *)reserve(sizeof(State));\np->hits = 1;\n}}\n"
        );
        let files = parse_cpp_files(vec![
            CppFile {
                path: "contract.h".into(),
                source: header,
            },
            CppFile {
                path: "candidate.cpp".into(),
                source: source.clone(),
            },
        ]);
        let facts = collect_initialization_facts(&files)
            .remove("candidate.cpp")
            .unwrap();
        assert_eq!(
            covers(&facts, &source, "p->hits"),
            expected,
            "{source}: {facts:?}"
        );
    }
    for source in [
        format!(
            "struct State {{ int hits; }};\nvoid create() {{ State *p = (State *)reserve(32); p->hits = 1; }}\n{declaration}"
        ),
        format!(
            "{declaration}\nstruct State {{ int hits; }};\nvoid create(void *(*reserve)(size_t)) {{ State *p = (State *)reserve(32); p->hits = 1; }}"
        ),
    ] {
        assert!(!covers(&ranges(&source), &source, "p->hits"), "{source}");
    }
}

#[test]
fn attribute_contracts_do_not_borrow_macro_state_from_unrelated_translation_units() {
    let source = "#include \"contract.h\"\nstruct State { int hits; };\nvoid create() { State *p = (State *)reserve(32); p->hits = 1; }\n";
    for (include, expected) in [
        ("", true),
        ("#if FEATURE\n#include \"override.h\"\n#endif\n", false),
    ] {
        let source = format!("{include}{source}");
        let files = parse_cpp_files(vec![
            CppFile {
                path: "contract.h".into(),
                source: "__attribute__((malloc)) void *reserve(size_t);\n".into(),
            },
            CppFile {
                path: "override.h".into(),
                source: "#define __attribute__(x)\n".into(),
            },
            CppFile {
                path: "unrelated.cpp".into(),
                source: "#include \"override.h\"\n".into(),
            },
            CppFile {
                path: "candidate.cpp".into(),
                source: source.clone(),
            },
        ]);
        let facts = collect_initialization_facts(&files)
            .remove("candidate.cpp")
            .unwrap();
        assert_eq!(
            covers(&facts, &source, "p->hits"),
            expected,
            "{source}: {facts:?}"
        );
    }
}

#[test]
fn allocator_contracts_respect_compile_command_overrides_and_publication() {
    use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
    use false_sharing_detector::types::AnalysisOptions;
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("candidate.cpp");
    let source = r#"
        __attribute__((malloc)) void *reserve(size_t n);
        struct State { void (*hits)(void*); void *misses; };
        void callback(void*);
        void *payload;
        void writer() {
            State *p = (State *)reserve(sizeof(State));
            p->hits = callback;
            p->misses = payload;
            publish(p);
        }
        void reader(State *p) {
            p->hits(p->misses);
        }
        void run() {
            std::thread a(writer);
            a.join();
        }
    "#;
    std::fs::write(&path, source).unwrap();
    for (flags, expected) in [
        (vec!["-DUNRELATED=1"], false),
        (vec!["-D__attribute__(x)="], true),
        (vec!["-D", "__attribute__(x)="], true),
        (vec!["-Dreserve=shared"], true),
        (vec!["-Umalloc"], true),
        (vec!["-include", "config.h"], true),
        (vec!["@options.rsp"], true),
    ] {
        let args = std::iter::once("clang++")
            .chain(flags.iter().copied())
            .chain(["-c", "candidate.cpp"])
            .collect::<Vec<_>>();
        let command =
            serde_json::json!([{"directory": root.path(), "file": path, "arguments": args}]);
        std::fs::write(
            root.path().join("compile_commands.json"),
            command.to_string(),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(
            root.path(),
            &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
        );
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{flags:?}: {report:#?}"
        );
    }
    std::fs::remove_file(root.path().join("compile_commands.json")).unwrap();
    // A fresh result stops being private as soon as a call can publish it.
    std::fs::write(
        &path,
        source.replace("p->hits = callback;", "publish(p);\np->hits = callback;"),
    )
    .unwrap();
    let report = analyze_cpp_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::SameObjectFields]),
    );
    assert!(!report.findings.is_empty(), "{report:#?}");
}

#[test]
fn unresolved_rhs_does_not_erase_a_bound_initialization_or_shared_write() {
    use false_sharing_detector::cpp_detection::{
        evidence::collect_cpp_evidence, layout::collect_cpp_structs,
    };
    let source = r#"
        __attribute__((malloc)) void *reserve(size_t n);
        struct State { int hits; int misses; };
        struct KnownName { int payload; };
        struct Job { Unknown inner; };
        void create(Job *job) {
            State *p = (State *)reserve(sizeof(State));
            p->hits = job->inner.payload;
            publish(p);
            p->misses = job->inner.payload;
        }
    "#;
    let files = parse_cpp_files(vec![CppFile {
        path: "candidate.cpp".into(),
        source: source.into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let evidence = collect_cpp_evidence(&files, &records);
    let owner = records.iter().position(|r| r.name == "State").unwrap();
    let accesses = evidence[owner]
        .items
        .iter()
        .filter(|e| e.access_kind.is_some())
        .collect::<Vec<_>>();
    assert!(
        accesses
            .iter()
            .any(|e| e.field_name.as_deref() == Some("hits"))
    );
    assert!(
        accesses
            .iter()
            .filter(|e| e.field_name.as_deref() == Some("hits"))
            .all(|e| e.initialization_phase),
        "{accesses:#?}"
    );
    assert!(
        accesses
            .iter()
            .any(|e| e.field_name.as_deref() == Some("misses") && !e.initialization_phase),
        "{accesses:#?}"
    );
}
