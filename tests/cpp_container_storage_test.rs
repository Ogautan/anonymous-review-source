use false_sharing_detector::types::RuleId;
use std::fs;

use false_sharing_detector::cpp_detection::analyze_cpp_path_with_options;
use false_sharing_detector::types::{AnalysisOptions, CandidateKind};
use tempfile::tempdir;

fn analyze(source: &str, rule: CandidateKind) -> false_sharing_detector::types::Report {
    // Project a discovery method for these focused regressions; public selection uses relations.
    let mut report = {
        let directory = tempdir().unwrap();
        fs::write(directory.path().join("candidate.hpp"), source).unwrap();
        analyze_cpp_path_with_options(
            directory.path(),
            &AnalysisOptions::with_rules(
                &false_sharing_detector::types::ALL_RULES
                    .into_iter()
                    .filter(|relation| rule.supports(*relation))
                    .collect::<Vec<_>>(),
            ),
        )
    };
    report.findings.retain(|finding| {
        [rule].iter().any(|kind| {
            finding.candidate_kind == *kind || finding.related_candidate_kinds.contains(kind)
        })
    });
    report
}

#[test]
fn separate_container_fields_keep_separate_storage_pair_groups() {
    let report = analyze(
        "struct Metrics {\n std::vector<std::atomic<int>> counters;\n std::vector<std::atomic<int>> slots;\n void update(unsigned worker_id) {\n counters[worker_id].fetch_add(1);\n slots[worker_id].fetch_add(1);\n }\n};",
        CandidateKind::ContainerElements,
    );
    assert!(!report.analysis_incomplete, "{report:#?}");
    assert_eq!(report.findings.len(), 2, "{report:#?}");
    assert_ne!(
        report.findings[0].finding_group_id,
        report.findings[1].finding_group_id
    );
    for finding in report.findings {
        assert_eq!(finding.field_list.len(), 1, "{finding:#?}");
        let field = &finding.field_list[0];
        let pattern = finding.static_pattern.as_ref().unwrap();
        assert!(
            pattern
                .witness_locations
                .iter()
                .all(|location| location.starts_with(&format!("{field}["))
                    || location.contains(&format!(".{field}["))),
            "{finding:#?}"
        );
    }
}

#[test]
fn container_and_element_member_paths_share_one_backing_storage_group() {
    let report = analyze(
        "struct Entry { std::atomic<int> value; };\nstruct Metrics {\n std::vector<Entry> counters;\n void update(unsigned worker_id) { counters[worker_id].value.fetch_add(1); }\n};",
        CandidateKind::ContainerElements,
    );
    assert!(!report.analysis_incomplete, "{report:#?}");
    assert_eq!(report.findings.len(), 1, "{report:#?}");
    assert!(
        report.findings[0]
            .field_list
            .iter()
            .any(|field| field == "counters[].value")
    );
}

#[test]
fn payload_recurrence_is_not_borrowed_from_vector_header_mutation() {
    for (operation, expected) in [("store(value)", false), ("fetch_add(value)", true)] {
        let source = format!(
            r#"
struct Owner {{
    std::vector<std::atomic<int>> slots;
    void exchange(std::vector<std::atomic<int>>& other) {{ slots.swap(other); }}
    void update(int index, int value) {{ slots[index].{operation}; }}
}};
"#
        );
        assert_eq!(
            !analyze(&source, CandidateKind::ContainerElements)
                .findings
                .is_empty(),
            expected,
            "{operation}"
        );
    }
}

#[test]
fn container_elements_payload_index_uses_runtime_identity_in_a_preprocessor_configuration() {
    let source = r#"
struct Entry { int value; };
struct Owner {
    std::vector<Entry> slots;
    void update(int column) {
#ifdef PARALLEL_BUILD
        int position = omp_get_thread_num();
#else
        int position = 0;
#endif
        slots[position].value++;
    }
};
"#;
    assert!(
        !analyze(source, CandidateKind::ContainerElements)
            .findings
            .is_empty()
    );
    for source in [
        source.replace(
            "slots[position].value++;",
            "position = 0;\nslots[position].value++;",
        ),
        source.replace(
            "slots[position].value++;",
            "int unused = position; slots[column].value++;",
        ),
        source.replace("omp_get_thread_num()", "column"),
        source.replace("struct Entry", "struct alignas(64) Entry"),
    ] {
        assert!(
            analyze(&source, CandidateKind::ContainerElements)
                .findings
                .is_empty(),
            "{source}"
        );
    }
    let direct = source.replace("slots[position]", "slots.at(omp_get_thread_num())");
    assert!(
        !analyze(&direct, CandidateKind::ContainerElements)
            .findings
            .is_empty()
    );
}

#[test]
fn container_elements_cache_spelling_does_not_supply_hot_element_evidence() {
    // Both names pass the pre-existing candidate-discovery gate. This test
    // isolates the removed cache-name-as-payload-evidence shortcut.
    for (element, field) in [("CacheEntry", "cache"), ("Entry", "slots")] {
        let source = format!(
            "struct {element} {{ int value; }}; struct Owner {{ std::vector<{element}> {field}; void prepare(int n) {{ {field}.resize(n); }} }};"
        );
        assert!(
            analyze(&source, CandidateKind::ContainerElements)
                .findings
                .is_empty()
        );
        let ordinary_runtime = format!(
            "struct {element} {{ int value; }}; struct Owner {{ std::vector<{element}> {field}; void update(int worker) {{ {field}[worker].value++; }} }};"
        );
        assert!(
            analyze(&ordinary_runtime, CandidateKind::ContainerElements)
                .findings
                .is_empty()
        );
        let ordinary_runtime = ordinary_runtime.replace("void update(int worker) {", "void update(int count) {\n#pragma omp parallel for\nfor (int worker = 0; worker < count; ++worker)");
        assert!(
            !analyze(&ordinary_runtime, CandidateKind::ContainerElements)
                .findings
                .is_empty()
        );
        let isolated = ordinary_runtime.replace(
            &format!("struct {element}"),
            &format!("struct alignas(64) {element}"),
        );
        assert!(
            analyze(&isolated, CandidateKind::ContainerElements)
                .findings
                .is_empty()
        );
        for payload in [
            "int value; char padding[64];",
            "int value; ExternalPayload payload;",
        ] {
            let wide_or_unknown = ordinary_runtime.replace("int value;", payload);
            assert!(
                analyze(&wide_or_unknown, CandidateKind::ContainerElements)
                    .findings
                    .is_empty()
            );
        }
        let synchronized = source.replace("int value", "std::atomic<int> value");
        let runtime = format!(
            "{synchronized}\nvoid update(Owner& owner, int worker) {{ owner.{field}[worker].value.fetch_add(1); }}"
        );
        assert!(
            !analyze(&runtime, CandidateKind::ContainerElements)
                .findings
                .is_empty(),
            "{element}"
        );
    }
}

#[test]
fn static_data_alignment_of_one_conditional_alias_does_not_protect_another() {
    let source = r#"
        #if PLATFORM_A
        typedef pthread_mutex_t Lock;
        static Lock locks[32];
        #else
        typedef struct { alignas(64) pthread_mutex_t mutex; } Lock;
        static Lock locks[32];
        #endif
        void update(unsigned i) { pthread_mutex_lock(&locks[i]); }
    "#;
    let report = analyze(source, CandidateKind::StaticData);
    assert!(
        !report.findings.is_empty(),
        "branch layout lost: {report:#?}"
    );
    for source in [
        "#if PLATFORM_A\nusing Lock = pthread_mutex_t;\nstatic Lock locks[32];\n#else\nstruct alignas(64) Lock { pthread_mutex_t mutex; };\nstatic Lock locks[32];\n#endif",
        "namespace A { struct Lock { pthread_mutex_t mutex; };\nstatic Lock locks[32]; }\nnamespace B { struct alignas(64) Lock { pthread_mutex_t mutex; };\nstatic Lock locks[32]; }\nusing A::locks;",
    ] {
        let report = analyze(
            &format!("{source}\nvoid update(unsigned i) {{ pthread_mutex_lock(&locks[i]); }}"),
            CandidateKind::StaticData,
        );
        assert!(
            !report.findings.is_empty(),
            "distinct binding {source}: {report:#?}"
        );
    }
    let aligned = analyze(
        "typedef struct { alignas(64) pthread_mutex_t mutex; } Lock;\nstatic Lock locks[32];\nvoid update(unsigned i) { pthread_mutex_lock(&locks[i].mutex); }",
        CandidateKind::StaticData,
    );
    assert!(aligned.findings.is_empty(), "aligned control: {aligned:#?}");
}

#[test]
fn container_elements_atomic_elements_are_distinct_from_their_container_control_block() {
    let report = analyze(
        r#"
        struct Metrics {
            std::vector<std::atomic<int>> counters;
            void update(unsigned worker_id) { counters[worker_id].fetch_add(1); }
        };
    "#,
        CandidateKind::ContainerElements,
    );
    assert!(!report.findings.is_empty(), "{:#?}", report);
    for finding in &report.findings {
        let layout = finding.layout_context.as_ref().unwrap();
        let field = layout
            .fields
            .iter()
            .find(|field| field.name == "counters")
            .unwrap();
        assert!(!field.is_atomic);
        assert!(!field.is_hot_sync);
    }
    let pointers = analyze(
        r#"
        struct Metrics {
            std::vector<std::atomic<int>*> counters;
            void update(unsigned worker_id) { counters[worker_id]->fetch_add(1); }
        };
    "#,
        CandidateKind::ContainerElements,
    );
    assert!(pointers.findings.is_empty(), "{:#?}", pointers.findings);
}

#[test]
fn container_elements_preserves_vector_element_writes_without_claiming_header_mutation() {
    let source = r#"
        struct CacheEntry { int counter; int state; };
        class Store {
            std::vector<CacheEntry> cache;
        public:
            void update(int worker) { cache[worker].counter++; }
            int inspect(int worker) { return cache[worker].state; }
        };
        std::shared_ptr<Store> published;
    "#;
    // A public mutator alone does not establish concurrent element writes.
    assert!(
        analyze(source, CandidateKind::ContainerElements)
            .findings
            .is_empty()
    );
    let parallel = source.replace("void update(int worker) { cache[worker].counter++; }", "void update(int count) {\n#pragma omp parallel for\nfor (int worker = 0; worker < count; ++worker) cache[worker].counter++;\n}");
    let report = analyze(&parallel, CandidateKind::ContainerElements);
    assert!(!report.findings.is_empty(), "{report:#?}");
    assert!(
        report
            .findings
            .iter()
            .flat_map(|finding| &finding.access_evidence)
            .any(|item| {
                item.evidence_kind == "contiguous_element_access"
                    && item.access_mode == "contiguous_element"
                    && item.access_kind.as_deref() == Some("read_modify_write")
            })
    );
    let header = analyze(source, CandidateKind::MixedFields);
    assert!(header.findings.is_empty(), "{header:#?}");
}

#[test]
fn sibling_arrays_tracks_std_array_at_member_mutations_as_element_accesses() {
    let vulnerable = analyze(
        r#"
        struct Counter { std::atomic<unsigned long> value; };
        class Metrics {
            std::array<Counter, 256> request_counters;
            std::array<Counter, 16> error_counters;
        public:
            void request(unsigned kind) { request_counters.at(kind).value++; }
            void error(unsigned kind) { error_counters.at(kind).value++; }
        };
        "#,
        CandidateKind::SiblingArrays,
    );
    assert!(!vulnerable.findings.is_empty(), "{vulnerable:#?}");
    assert!(
        vulnerable
            .findings
            .iter()
            .flat_map(|finding| &finding.access_evidence)
            .any(|item| {
                item.evidence_kind == "contiguous_element_access"
                    && item.access_mode == "contiguous_element"
                    && item.access_kind.as_deref() == Some("read_modify_write")
            })
    );

    let protected = analyze(
        r#"
        struct alignas(64) Counter { unsigned long value; };
        class Metrics {
            std::array<Counter, 256> request_counters;
            std::array<Counter, 16> error_counters;
        public:
            void request(unsigned kind) { request_counters.at(kind).value++; }
            void error(unsigned kind) { error_counters.at(kind).value++; }
        };
        "#,
        CandidateKind::SiblingArrays,
    );
    assert!(protected.findings.is_empty(), "{protected:#?}");
}

#[test]
fn container_elements_does_not_treat_vector_resize_as_partitioned_payload_access() {
    let report = analyze(
        r#"
        struct CacheEntry { std::atomic<int> counter; };
        struct Store {
            std::vector<CacheEntry> cache;
            void initialize(int count) { cache.resize(count); }
        };
        std::shared_ptr<Store> published;
        "#,
        CandidateKind::ContainerElements,
    );
    assert!(report.findings.is_empty(), "{report:#?}");
}

#[test]
fn container_elements_constructor_element_fill_cannot_borrow_runtime_reader_heat() {
    let source = r#"
        struct Entry { std::atomic<int> value; };
        class Store {
            std::vector<Entry> slots;
        public:
            Store() : slots(16) { for (int i = 0; i < 16; ++i) slots[i].value.store(0); }
            int inspect(int worker) { return slots[worker].value.load(); }
            RUNTIME
        };
    "#;
    assert!(
        analyze(
            &source.replace("RUNTIME", ""),
            CandidateKind::ContainerElements
        )
        .findings
        .is_empty()
    );
    let runtime = source.replace(
        "RUNTIME",
        "void update(int worker) { slots[worker].value.fetch_add(1); }",
    );
    assert!(
        !analyze(&runtime, CandidateKind::ContainerElements)
            .findings
            .is_empty()
    );
}

#[test]
fn container_elements_pointer_pointees_and_nested_heap_arrays_are_not_vector_slots() {
    for declaration in [
        "std::vector<CacheEntry*> cache",
        "std::vector<std::vector<CacheEntry>> cache",
    ] {
        let access = if declaration.contains("CacheEntry*") {
            "cache[worker]->counter++"
        } else {
            "cache[worker][0].counter++"
        };
        let source = format!(
            "struct CacheEntry {{ std::atomic<int> counter; }};\n\
             struct Store {{ {declaration}; void work(int worker) {{ {access}; }} }};\n\
             std::shared_ptr<Store> published;"
        );
        let report = analyze(&source, CandidateKind::ContainerElements);
        assert!(report.findings.is_empty(), "{declaration}: {report:#?}");
    }
}

#[test]
fn object_instances_container_type_alias_requires_an_actual_storage_use() {
    let record = r#"
        struct Counter {
            std::atomic<unsigned long> count;
            void update() { for (int i = 0; i < 100; ++i) count.fetch_add(1); }
        };
        using CounterArray = std::vector<Counter>;
        using CounterArrayAlias = CounterArray;
    "#;
    let unused = analyze(record, CandidateKind::ObjectInstances);
    assert!(
        unused.findings.is_empty(),
        "type aliases allocate no objects: {unused:#?}"
    );
    for use_without_storage in [
        "CounterArray *pointer;",
        "extern CounterArray &reference;",
        "CounterArray make_snapshot();",
        "auto bytes = sizeof(CounterArray);",
        "CounterArray *pointers[4];",
    ] {
        let report = analyze(
            &format!("{record}\n{use_without_storage}"),
            CandidateKind::ObjectInstances,
        );
        assert!(
            report.findings.is_empty(),
            "{use_without_storage}: {report:#?}"
        );
    }
    for storage in ["CounterArray counters;", "CounterArrayAlias counters;"] {
        let used = analyze(
            &format!("{record}\n{storage}"),
            CandidateKind::ObjectInstances,
        );
        assert!(
            !used.findings.is_empty(),
            "actual alias storage must survive: {used:#?}"
        );
    }
}

#[test]
fn object_instances_multiline_and_typedef_aliases_are_types_not_allocations() {
    let record = r#"
        struct Counter {
            std::atomic<unsigned long> count;
            void update() { for (int i = 0; i < 100; ++i) count.fetch_add(1); }
        };
    "#;
    for alias in [
        "using CounterArray =\n std::vector<Counter>;",
        "typedef std::vector<Counter> CounterArray;",
        "typedef Counter Element;\nusing CounterArray = std::vector<Element>;",
    ] {
        let unused = analyze(
            &format!("{record}\n{alias}"),
            CandidateKind::ObjectInstances,
        );
        assert!(unused.findings.is_empty(), "{alias}: {unused:#?}");
        let used = analyze(
            &format!("{record}\n{alias}\nCounterArray counters;"),
            CandidateKind::ObjectInstances,
        );
        assert!(!used.findings.is_empty(), "{alias}: {used:#?}");
    }
    for target in [
        "std::vector<Counter>*",
        "std::shared_ptr<std::vector<Counter>>",
        "std::vector<std::vector<Counter>>",
        "std::vector<Counter*>",
    ] {
        let report = analyze(
            &format!("{record}\nusing Wrapper = {target};\nWrapper value;"),
            CandidateKind::ObjectInstances,
        );
        assert!(report.findings.is_empty(), "{target}: {report:#?}");
    }
}

#[test]
fn object_instances_private_local_storage_cannot_borrow_other_instance_hot_writes() {
    let prefix = r#"
        #define REGISTER_OBJECT register_object(this)
        struct Entry {
            unsigned long counter = 0;
            void update() { for (int i = 0; i < 100; ++i) counter++; }
        };
        Entry live;
        void launch() { std::thread([] { live.update(); }).detach(); }
    "#;
    for declaration in ["std::vector<Entry> snapshots;", "Entry snapshots[8];"] {
        let source = format!("{prefix}\nvoid inspect() {{\n{declaration}\n}}\n");
        let report = analyze(&source, CandidateKind::ObjectInstances);
        assert!(report.findings.is_empty(), "{declaration}: {report:#?}");
    }
    for declaration in ["std::vector<Entry> snapshots(8);", "Entry snapshots[8];"] {
        let report = analyze(
            &format!(
                "{prefix}\nvoid inspect() {{\n{declaration}\nfor (int i = 0; i < 8; ++i) snapshots[i].counter++;\n}}"
            ),
            CandidateKind::ObjectInstances,
        );
        assert!(
            report.findings.is_empty(),
            "private element writes: {report:#?}"
        );
    }
    for escape in [
        "publish(snapshots);",
        "std::thread([&] { snapshots[0].update(); }).join();",
    ] {
        let source = format!(
            "{prefix}\nvoid inspect() {{\nstd::vector<Entry> snapshots(8);\n{escape}\n}}\n"
        );
        let report = analyze(&source, CandidateKind::ObjectInstances);
        assert!(
            !report.findings.is_empty(),
            "escape must remain unresolved: {report:#?}"
        );
    }
    for body in [
        "[&] { for (int i = 0; i < 8; ++i) snapshots[i].counter++; }();",
        "([&] { snapshots[0].counter++; })();",
    ] {
        let report = analyze(
            &format!("{prefix}\nvoid inspect() {{\nEntry snapshots[8];\n{body}\n}}"),
            CandidateKind::ObjectInstances,
        );
        assert!(
            report.findings.is_empty(),
            "synchronous lambda: {report:#?}"
        );
    }
    for body in [
        "auto callback = [&] { snapshots[0].counter++; }; publish(callback);",
        "[&] { publish(&snapshots[0]); }();",
        "[&] { std::thread([&] { snapshots[0].counter++; }).join(); }();",
        "auto & value = [&]() -> unsigned long & { return snapshots[0].counter; }(); publish(value);",
        "[&]() -> Task { co_await suspend(); snapshots[0].counter++; }();",
    ] {
        let report = analyze(
            &format!("{prefix}\nvoid inspect() {{\nEntry snapshots[8];\n{body}\n}}"),
            CandidateKind::ObjectInstances,
        );
        assert!(!report.findings.is_empty(), "unproved lambda: {report:#?}");
    }
    for fields in [
        "unsigned long counter = 0; Entry() { publish(this); }",
        "unsigned long counter = 0; Entry /* publication */ () { publish(this); }",
        "unsigned long counter = register_object(this);",
        "unsigned long counter = 0; unsigned long registration = register_object(this);",
        "unsigned long counter = 0; unsigned long registration = REGISTER_OBJECT;",
    ] {
        let source = format!(
            "{}\nvoid inspect() {{\nEntry snapshots[8];\n}}",
            prefix.replace("unsigned long counter = 0;", fields)
        );
        let report = analyze(&source, CandidateKind::ObjectInstances);
        let control = analyze(
            &format!(
                "{}\nEntry exposed[8];",
                prefix.replace("unsigned long counter = 0;", fields)
            ),
            CandidateKind::ObjectInstances,
        );
        assert!(
            !control.findings.is_empty(),
            "control must detect the record: {fields}"
        );
        assert!(
            !report.findings.is_empty(),
            "construction may publish ({fields}): {report:#?}"
        );
    }
}

#[test]
fn container_reports_only_ast_bound_inline_element_member_paths() {
    let source = r#"
struct Entry { int written; int observed; int unused; };
struct Owner {
    std::vector<Entry> slots;
    void update() {
        int position = omp_get_thread_num();
        slots[position].written += slots[position].observed;
    }
};
"#;
    let report = analyze(source, CandidateKind::ContainerElements);
    let finding = report
        .findings
        .iter()
        .find(|f| f.struct_name.as_deref() == Some("Owner"))
        .expect("shared dense element writes");
    for path in ["slots", "slots[].written", "slots[].observed"] {
        assert!(
            finding.field_list.contains(&path.to_string()),
            "missing {path}: {:?}",
            finding.field_list
        );
    }
    assert!(!finding.field_list.iter().any(|p| p.contains("unused")));
    assert!(finding.access_evidence.iter().any(|e| {
        e.semantic_contexts
            .iter()
            .any(|c| c == "cpp_element_member_path:slots[].written")
    }));
    for protected in [
        source.replace("struct Entry", "struct alignas(128) Entry"),
        source.replace(
            "slots[position].written += slots[position].observed;",
            "consume(slots[position].observed);",
        ),
        source
            .replace("std::vector<Entry>", "std::vector<Entry *>")
            .replace("slots[position].", "slots[position]->"),
    ] {
        assert!(
            analyze(&protected, CandidateKind::ContainerElements)
                .findings
                .is_empty(),
            "{protected}"
        );
    }
}

#[test]
fn recovered_nested_element_access_keeps_a_shadowed_member_path() {
    let source = r#"
struct CacheEntry { double sqrtkT; int t; };
struct Owner {
    std::vector<CacheEntry> cache;
    void update(double sqrtkT) {
        int worker = omp_get_thread_num();
        if (sqrtkT != cache[worker].sqrtkT) {
            cache[worker].t = 1;
            cache[worker].sqrtkT = sqrtkT;
        }
    }
};
"#;
    let report = analyze(source, CandidateKind::ContainerElements);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.struct_name.as_deref() == Some("Owner"))
        .expect("indexed cache writes should remain reviewable");
    assert!(
        finding.field_list.contains(&"cache[].sqrtkT".to_string()),
        "missing shadowed nested path: {:?}",
        finding.field_list
    );
    assert!(finding.access_evidence.iter().any(|evidence| {
        evidence
            .semantic_contexts
            .iter()
            .any(|context| context == "cpp_element_member_path:cache[].sqrtkT")
    }));
}

#[test]
fn sibling_array_witnesses_survive_large_owners_without_borrowing_unused_fields() {
    let unrelated = (0..140)
        .map(|i| format!("int unrelated_{i};"))
        .collect::<String>();
    for (second_access, expected) in [
        ("second[position].fetch_add(1);", true),
        ("consume(second[position].load());", false),
        ("", false),
    ] {
        let source = format!(
            r#"
struct Owner {{
    {unrelated}
    std::atomic<int> first[8];
    std::atomic<int> second[8];
    std::atomic<int> unused[8];
    void update() {{
        int position = omp_get_thread_num();
        first[position].fetch_add(1);
        {second_access}
    }}
}};
"#
        );
        let report = analyze(&source, CandidateKind::SiblingArrays);
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{second_access}: {:#?}",
            report.findings
        );
        assert!(
            report
                .findings
                .iter()
                .all(|f| !f.field_list.iter().any(|field| field == "unused"))
        );
    }
}

#[test]
fn sibling_arrays_aligned_owner_does_not_isolate_dense_array_elements() {
    for cache_line_size in [32, 64, 128] {
        let source = format!(
            r#"
struct alignas({cache_line_size}) Metrics {{
    unsigned long received[16];
    unsigned long sent[16];
}};
void receive(Metrics *stats) {{ stats->received[omp_get_thread_num()]++; }}
void send(Metrics *stats) {{ stats->sent[omp_get_thread_num()]++; }}
"#
        );
        let directory = tempdir().unwrap();
        let path = directory.path().join("candidate.cpp");
        let options = AnalysisOptions {
            cache_line_size,
            ..AnalysisOptions::with_rules(&[RuleId::ContiguousElements])
        };
        fs::write(&path, &source).unwrap();
        let report = analyze_cpp_path_with_options(directory.path(), &options);
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.field_list.contains(&"received".into())
                    && f.field_list.contains(&"sent".into())),
            "{report:#?}"
        );
        fs::write(&path, source.replace("omp_get_thread_num()", "0")).unwrap();
        assert!(
            analyze_cpp_path_with_options(directory.path(), &options)
                .findings
                .is_empty()
        );
    }
}

#[test]
fn sibling_arrays_bind_extern_objects_through_direct_includes() {
    let directory = tempdir().unwrap();
    fs::write(
        directory.path().join("metrics.h"),
        r#"
struct Metrics { unsigned long received[16]; unsigned long sent[16]; };
extern Metrics shared;
"#,
    )
    .unwrap();
    let source = r#"
#include "metrics.h"
void update() {
    int position = omp_get_thread_num();
    shared.received[position]++;
    shared.sent[position]++;
}
"#;
    let path = directory.path().join("update.cpp");
    let options = AnalysisOptions::with_rules(&[RuleId::ContiguousElements]);
    for (text, expected) in [
        (source.to_string(), true),
        (source.replace("#include \"metrics.h\"", ""), false),
        (
            source.replace("void update() {", "void update(Unknown shared) {"),
            false,
        ),
        (
            source.replace("void update() {", "void update() { Unknown shared;"),
            false,
        ),
        (source.replace("omp_get_thread_num()", "0"), false),
        (
            source.replace(
                "shared.sent[position]++;",
                "consume(shared.sent[position]);",
            ),
            false,
        ),
    ] {
        fs::write(&path, &text).unwrap();
        let report = analyze_cpp_path_with_options(directory.path(), &options);
        assert_eq!(
            report
                .findings
                .iter()
                .any(|finding| finding.has_candidate(CandidateKind::SiblingArrays)),
            expected,
            "{text}\n{report:#?}"
        );
    }
    fs::write(
        directory.path().join("other.h"),
        "struct Other { int unrelated; }; extern Other shared;",
    )
    .unwrap();
    fs::write(
        &path,
        source.replace(
            "#include \"metrics.h\"",
            "#include \"metrics.h\"\n#include \"other.h\"",
        ),
    )
    .unwrap();
    assert!(
        analyze_cpp_path_with_options(directory.path(), &options)
            .findings
            .iter()
            .all(|finding| !finding.has_candidate(CandidateKind::SiblingArrays))
    );
    fs::write(directory.path().join("other.h"), "extern Unknown shared;").unwrap();
    assert!(
        analyze_cpp_path_with_options(directory.path(), &options)
            .findings
            .iter()
            .all(|finding| !finding.has_candidate(CandidateKind::SiblingArrays))
    );
}
