use false_sharing_detector::{
    analyzer::analyze_path_with_options,
    types::{AnalysisOptions, CandidateKind, ColocationPattern, RuleId},
};
use std::fs;

fn analyze(source: &str, block: usize) -> Vec<false_sharing_detector::types::Finding> {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("lib.rs"), source).unwrap();
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions {
            cache_line_size: block,
            ..AnalysisOptions::with_rules(&[RuleId::IndependentStatics, RuleId::ContiguousElements])
        },
    );
    assert!(!report.analysis_incomplete, "{report:#?}");
    report
        .findings
        .into_iter()
        .filter(|finding| finding.candidate_kind == CandidateKind::StaticData)
        .collect()
}

#[test]
fn static_arrays_require_real_writes_and_distinct_legal_elements() {
    for block in [32, 64, 128] {
        for (length, body, expected) in [
            (0, "", false),
            (1, "", false),
            (2, "", false),
            (0, "VALUES[index].store(1, Ordering::Relaxed);", false),
            (1, "VALUES[index].store(1, Ordering::Relaxed);", false),
            (2, "VALUES[0].store(1, Ordering::Relaxed);", false),
            (2, "VALUES[index].load(Ordering::Relaxed);", false),
            (2, "VALUES[index].store(1, Ordering::Relaxed);", true),
            (
                2,
                "VALUES[0].store(1, Ordering::Relaxed); VALUES[1].load(Ordering::Relaxed);",
                true,
            ),
        ] {
            let source = format!(
                "use std::sync::atomic::{{AtomicU64, Ordering}};\nstatic VALUES: [AtomicU64; {length}] = [const {{ AtomicU64::new(0) }}; {length}];\npub fn access(index: usize) {{ {body} }}"
            );
            assert_eq!(
                !analyze(&source, block).is_empty(),
                expected,
                "B={block}, {source}"
            );
        }
    }
}

#[test]
fn static_element_isolation_uses_source_alignment_and_configured_block() {
    for block in [32, 64, 128] {
        for alignment in [64, 128] {
            for name in ["AtomicSlot", "Slot"] {
                let source = format!(
                    "use std::sync::atomic::{{AtomicU64, Ordering}};\n#[repr(align({alignment}))]\nstruct {name}(AtomicU64);\nstatic VALUES: [{name}; 2] = [const {{ {name}(AtomicU64::new(0)) }}; 2];\npub fn access(index: usize) {{ VALUES[index].0.fetch_add(1, Ordering::Relaxed); }}"
                );
                assert_eq!(
                    !analyze(&source, block).is_empty(),
                    alignment < block,
                    "B={block}, {source}"
                );
            }
        }
    }
}

#[test]
fn singleton_operations_resolve_the_actual_declaration_and_keep_source_sites() {
    for block in [32, 64, 128] {
        for (operations, expected) in [
            (
                "let LEFT: OnceLock<u64> = OnceLock::new(); let RIGHT: OnceLock<u64> = OnceLock::new(); let _ = LEFT.set(1); let _ = RIGHT.get();",
                false,
            ),
            (
                "let _ = hidden::LEFT.set(1); let _ = hidden::RIGHT.get();",
                true,
            ),
            (
                "let handle = &hidden::LEFT; let _ = handle.set(1); let _ = hidden::RIGHT.get();",
                true,
            ),
            (
                "let handle = hidden::LEFT.clone(); let _ = handle.set(1); let _ = hidden::RIGHT.get();",
                false,
            ),
            (
                "let _ = hidden::LEFT.set(1); let _ = &hidden::RIGHT;",
                false,
            ),
            (
                "let handle = &hidden::LEFT; if let Some(handle) = Some(OnceLock::<u64>::new()) { let _ = handle.set(1); } let _ = hidden::RIGHT.get();",
                false,
            ),
            (
                "let handle = &hidden::LEFT; match Some(OnceLock::<u64>::new()) { Some(handle) => { let _ = handle.set(1); }, None => {} } let _ = hidden::RIGHT.get();",
                false,
            ),
        ] {
            let source = format!("use std::sync::OnceLock;\nmod hidden {{\n pub static LEFT: OnceLock<u64> = OnceLock::new();\n pub static RIGHT: OnceLock<u64> = OnceLock::new();\n}}\npub fn access() {{ {operations} }}\n").replace("mod hidden {", "mod hidden { use super::*;");
            let findings = analyze(&source, block);
            assert_eq!(!findings.is_empty(), expected, "B={block}, {source}");
            if let Some(finding) = findings.first() {
                let pattern = finding.static_pattern.as_ref().unwrap();
                assert_eq!(pattern.colocation_pattern, ColocationPattern::StaticStorage);
                assert!(
                    pattern
                        .language_specific_assumptions
                        .contains(&"linker_may_place_independent_statics_in_one_block")
                );
                assert!(
                    pattern
                        .language_specific_assumptions
                        .contains(&"global_storage_may_be_accessed_by_independent_callers")
                );
                assert!(finding.access_evidence.iter().any(|access| access.line == 6
                    && access.field_name.as_deref() == Some("LEFT")
                    && access.access_kind.as_deref() == Some("write")));
                assert!(finding.access_evidence.iter().any(|access| access.line == 6
                    && access.field_name.as_deref() == Some("RIGHT")
                    && access.access_kind.as_deref() == Some("read")));
            }
        }
    }
}

#[test]
fn public_single_file_rules_keep_static_analysis_and_element_layout() {
    for (alignment, expected) in [(8, true), (128, false)] {
        let source = format!(
            "use std::sync::atomic::{{AtomicU64, Ordering}}; #[repr(align({alignment}))] struct Slot(AtomicU64); static VALUES: [Slot; 2] = [const {{ Slot(AtomicU64::new(0)) }}; 2]; pub fn access(index: usize) {{ VALUES[index].0.store(1, Ordering::Relaxed); }}"
        );
        let ast = syn::parse_file(&source).unwrap();
        let findings = false_sharing_detector::rules::apply_file_rules(
            &source,
            "lib.rs",
            &ast,
            None,
            &AnalysisOptions::all_rules(),
        );
        assert_eq!(
            findings
                .iter()
                .any(|finding| finding.candidate_kind == CandidateKind::StaticData),
            expected,
        );
    }
}

#[test]
fn static_reference_accessor_instantiates_constant_indices_at_call_sites() {
    for calls in [
        "slot(0).store(1, Ordering::Relaxed);",
        "slot(0).store(1, Ordering::Relaxed); slot(0).load(Ordering::Relaxed);",
    ] {
        let source = format!(
            "use std::sync::atomic::{{AtomicU64, Ordering}};\nfn slot(index: usize) -> &'static AtomicU64 {{ const LEN: usize = 2; static VALUES: [AtomicU64; LEN] = [const {{ AtomicU64::new(0) }}; LEN]; &VALUES[index % LEN] }}\npub fn access() {{ {calls} }}"
        );
        assert!(analyze(&source, 64).is_empty(), "{source}");
    }
    for calls in [
        "slot(index).store(1, Ordering::Relaxed);",
        "slot(0).store(1, Ordering::Relaxed); slot(1).load(Ordering::Relaxed);",
    ] {
        let source = format!(
            "use std::sync::atomic::{{AtomicU64, Ordering}};\nfn slot(index: usize) -> &'static AtomicU64 {{ const LEN: usize = 2; static VALUES: [AtomicU64; LEN] = [const {{ AtomicU64::new(0) }}; LEN]; &VALUES[index % LEN] }}\npub fn access(index: usize) {{ {calls} }}"
        );
        assert!(!analyze(&source, 64).is_empty(), "{source}");
    }
}

#[test]
fn static_array_constant_bounds_and_zero_sized_elements_are_excluded() {
    for source in [
        "use std::sync::atomic::{AtomicU64, Ordering}; const LENGTH: usize = 1; static VALUES: [AtomicU64; LENGTH] = [const { AtomicU64::new(0) }; LENGTH]; pub fn access(index: usize) { VALUES[index].store(1, Ordering::Relaxed); }",
        "struct SeqLock; impl SeqLock { fn write(&self) {} } static VALUES: [SeqLock; 2] = [SeqLock, SeqLock]; pub fn access(index: usize) { VALUES[index].write(); }",
    ] {
        assert!(analyze(source, 64).is_empty(), "{source}");
    }
}

#[test]
fn qualified_aliases_across_files_supply_singleton_accesses() {
    let root = tempfile::tempdir().unwrap();
    fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='static_aliases'\nversion='0.1.0'\nedition='2024'\n",
    )
    .unwrap();
    fs::create_dir(root.path().join("src")).unwrap();
    fs::write(
        root.path().join("src/lib.rs"),
        "pub mod state; mod caller;\n",
    )
    .unwrap();
    fs::write(root.path().join("src/state.rs"), "use std::sync::OnceLock;\npub static LEFT: OnceLock<u64> = OnceLock::new();\npub static RIGHT: OnceLock<u64> = OnceLock::new();\n").unwrap();
    fs::write(root.path().join("src/caller.rs"), "use crate::state::LEFT as OUTPUT;\nuse crate::state as storage;\npub fn write() { let _ = OUTPUT.set(1); }\npub fn read() { let _ = storage::RIGHT.get(); }\n").unwrap();
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions::with_rules(&[RuleId::IndependentStatics]),
    );
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.candidate_kind == CandidateKind::StaticData)
        .expect("resolved singleton pair");
    assert!(
        finding
            .access_evidence
            .iter()
            .all(|access| access.file.ends_with("caller.rs"))
    );
    assert!(
        finding
            .access_evidence
            .iter()
            .any(|access| access.line == 3)
    );
    assert!(
        finding
            .access_evidence
            .iter()
            .any(|access| access.line == 4)
    );
}

#[test]
fn lazy_reference_coercion_is_an_access_but_an_ordinary_borrow_is_not() {
    for (body, expected) in [
        ("let _ = &FALLBACK;", false),
        ("let _ = PRIMARY.get().unwrap_or(&FALLBACK);", true),
    ] {
        let source = format!(
            "use std::sync::{{OnceLock, LazyLock}};\nstruct Value;\nstatic PRIMARY: OnceLock<Value> = OnceLock::new();\nstatic FALLBACK: LazyLock<Value> = LazyLock::new(|| Value);\npub fn get() {{ let _ = PRIMARY.set(Value); {body} }}"
        );
        assert_eq!(!analyze(&source, 64).is_empty(), expected, "{source}");
    }
}

#[test]
fn declarative_macros_supply_only_evaluated_argument_operations() {
    for (definition, invocation, expected) in [
        (
            "macro_rules! dispatch { (@check, $code:expr) => { stringify!($code) }; ($kind:ty, $code:expr) => { loop { break $code; } }; }",
            "dispatch!(u64, { slot(index).store(1, Ordering::Relaxed); });",
            true,
        ),
        (
            "macro_rules! dispatch { (ignore, $code:expr) => { stringify!($code) }; ($kind:ty, $code:expr) => { loop { break $code; } }; }",
            "dispatch!(ignore, { slot(index).store(1, Ordering::Relaxed); });",
            false,
        ),
        (
            "macro_rules! defer { ($code:expr) => { || $code }; }",
            "let _ = defer!({ slot(index).store(1, Ordering::Relaxed); });",
            false,
        ),
        (
            "macro_rules! discard { ($code:expr) => { let __fs_macro_argument_0 = 0; __fs_macro_argument_0 }; }",
            "let _ = discard!({ slot(index).store(1, Ordering::Relaxed); });",
            false,
        ),
        (
            "",
            "opaque!({ slot(index).store(1, Ordering::Relaxed); });",
            false,
        ),
        (
            "macro_rules! choose { ($left:block, $right:block) => { if true $left else $right }; }",
            "choose!({ slot(index).store(1, Ordering::Relaxed); }, {});",
            true,
        ),
    ] {
        let source = format!(
            "use std::sync::atomic::{{AtomicU64, Ordering}};\nstatic VALUES: [AtomicU64; 2] = [const {{ AtomicU64::new(0) }}; 2];\nfn slot(index: usize) -> &'static AtomicU64 {{ &VALUES[index] }}\n{definition}\npub fn access(index: usize) {{ {invocation} }}"
        );
        let findings = analyze(&source, 64);
        assert_eq!(!findings.is_empty(), expected, "{source}");
        if let Some(finding) = findings.first() {
            assert!(
                finding
                    .access_evidence
                    .iter()
                    .any(|a| a.line == 5 && a.access_kind.as_deref() == Some("write"))
            );
        }
    }
}

#[test]
fn static_scope_resolution_distinguishes_modules_on_the_same_source_line() {
    let source = "mod first { use std::sync::OnceLock; static LEFT: OnceLock<u64> = OnceLock::new(); static RIGHT: OnceLock<u64> = OnceLock::new(); pub fn access() { let _ = LEFT.set(1); let _ = RIGHT.get(); } } mod second { use std::sync::OnceLock; static LEFT: OnceLock<u64> = OnceLock::new(); static RIGHT: OnceLock<u64> = OnceLock::new(); }";
    let findings = analyze(source, 64);
    assert!(!findings.is_empty());
    assert!(
        findings
            .iter()
            .flat_map(|f| &f.access_evidence)
            .all(|access| access
                .semantic_contexts
                .iter()
                .any(|c| c.contains("::first::"))
                && access
                    .semantic_contexts
                    .iter()
                    .all(|c| !c.contains("::second::")))
    );
}

#[test]
fn block_local_statics_on_the_same_line_keep_distinct_storage_identities() {
    let source = "use std::sync::atomic::{AtomicU64, Ordering}; fn one(index: usize) { static VALUES: [AtomicU64; 2] = [const { AtomicU64::new(0) }; 2]; VALUES[index].store(1, Ordering::Relaxed); } fn two(index: usize) { static VALUES: [AtomicU64; 2] = [const { AtomicU64::new(0) }; 2]; VALUES[index].store(1, Ordering::Relaxed); }";
    let findings = analyze(source, 64);
    let identities = findings
        .iter()
        .filter_map(|f| f.storage_identity.as_ref())
        .collect::<std::collections::HashSet<_>>();
    assert_eq!(identities.len(), 2, "{findings:#?}");
}

#[test]
fn static_method_effects_belong_to_the_receiver_storage() {
    for block in [32, 64, 128] {
        let references = "use std::sync::atomic::{AtomicU64, Ordering}; static FIRST: AtomicU64 = AtomicU64::new(0); static SECOND: AtomicU64 = AtomicU64::new(0); static SLOTS: [&AtomicU64; 2] = [&FIRST, &SECOND]; pub fn update(index: usize) { SLOTS[index].store(1, Ordering::Relaxed); }";
        assert!(analyze(references, block).is_empty());
        let referenced_fields = "use std::sync::atomic::{AtomicU64, Ordering}; struct State { value: AtomicU64 } static FIRST: State = State { value: AtomicU64::new(0) }; static SECOND: State = State { value: AtomicU64::new(0) }; static SLOTS: [&State; 2] = [&FIRST, &SECOND]; pub fn update(index: usize) { SLOTS[index].value.store(1, Ordering::Relaxed); }";
        assert!(analyze(referenced_fields, block).is_empty());
        let nested_references = "use std::sync::atomic::{AtomicU64, Ordering}; struct State { value: AtomicU64 } struct Slot { target: &'static State } static FIRST: State = State { value: AtomicU64::new(0) }; static SECOND: State = State { value: AtomicU64::new(0) }; static SLOTS: [Slot; 2] = [Slot { target: &FIRST }, Slot { target: &SECOND }]; pub fn update(index: usize) { SLOTS[index].target.value.store(1, Ordering::Relaxed); }";
        assert!(analyze(nested_references, block).is_empty());
        for (ty, constructor, method) in [
            ("Mutex<AtomicU64>", "Mutex::new(AtomicU64::new(0))", "lock"),
            (
                "RwLock<AtomicU64>",
                "RwLock::new(AtomicU64::new(0))",
                "read",
            ),
            (
                "RwLock<AtomicU64>",
                "RwLock::new(AtomicU64::new(0))",
                "try_read",
            ),
        ] {
            let source = format!(
                "use std::sync::{{Mutex, RwLock, atomic::AtomicU64}}; static VALUES: [{ty}; 2] = [const {{ {constructor} }}; 2]; pub fn access(index: usize) {{ let _ = VALUES[index].{method}(); }}"
            );
            let findings = analyze(&source, block);
            assert!(!findings.is_empty(), "{source}");
            assert!(findings.iter().any(|finding| {
                finding
                    .access_evidence
                    .iter()
                    .any(|access| access.access_kind.as_deref() == Some("read_modify_write"))
            }));
        }
    }
}
