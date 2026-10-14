use false_sharing_detector::analyzer::analyze_path_with_options;
use false_sharing_detector::types::{AnalysisOptions, CandidateKind, RuleId};
use std::fs;

fn container_findings(source: &str, block: usize) -> Vec<false_sharing_detector::types::Finding> {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("lib.rs"), source).unwrap();
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions {
            cache_line_size: block,
            ..AnalysisOptions::with_rules(&[RuleId::ContiguousElements])
        },
    );
    assert!(!report.analysis_incomplete, "{report:#?}");
    report
        .findings
        .into_iter()
        .filter(|finding| finding.candidate_kind == CandidateKind::ContainerElements)
        .collect()
}

#[test]
fn container_candidates_require_distinct_accessible_elements() {
    for block in [32, 64, 128] {
        for (storage, body, expected) in [
            (
                "[AtomicU64; 0]",
                "self.bits[index].fetch_add(1, Relaxed);",
                false,
            ),
            (
                "[AtomicU64; 1]",
                "self.bits[index].fetch_add(1, Relaxed);",
                false,
            ),
            (
                "[AtomicU64; 1 + 0]",
                "self.bits[index].fetch_add(1, Relaxed);",
                false,
            ),
            (
                "Vec<AtomicU64>",
                "self.bits[0].fetch_add(1, Relaxed);",
                false,
            ),
            (
                "Vec<AtomicU64>",
                "let slot = 0; self.bits[slot].fetch_add(1, Relaxed);",
                false,
            ),
            (
                "Vec<AtomicU64>",
                "let mut slot: usize = 0; self.bits[slot].fetch_add(1, Relaxed);",
                false,
            ),
            (
                "Vec<AtomicU64>",
                "let mut slot = index; slot = 0; self.bits[slot].fetch_add(1, Relaxed);",
                false,
            ),
            (
                "Vec<AtomicU64>",
                "self.bits[index % 1].fetch_add(1, Relaxed);",
                false,
            ),
            (
                "Vec<AtomicU64>",
                "for slot in 0..1 { self.bits[slot].fetch_add(1, Relaxed); }",
                false,
            ),
            (
                "Vec<AtomicU64>",
                "for slot in 0..0 { self.bits[slot].fetch_add(1, Relaxed); }",
                false,
            ),
            (
                "Vec<AtomicU64>",
                "self.bits[index].fetch_add(1, Relaxed);",
                true,
            ),
            (
                "[AtomicU64; 2]",
                "self.bits[index].fetch_add(1, Relaxed);",
                true,
            ),
            (
                "Vec<AtomicU64>",
                "self.bits[0].fetch_add(1, Relaxed); self.bits[1].load(Relaxed);",
                true,
            ),
            (
                "Vec<AtomicU64>",
                "self.bits[0].fetch_add(1, Relaxed); self.bits[100].load(Relaxed);",
                false,
            ),
            (
                "Vec<AtomicU64>",
                "self.bits[0].load(Relaxed); self.bits[1].load(Relaxed); self.bits[100].fetch_add(1, Relaxed);",
                false,
            ),
            ("Vec<AtomicU64>", "self.bits[index].load(Relaxed);", false),
            ("Vec<AtomicU64>", "self.bits.len();", false),
        ] {
            let source = format!(
                "use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};\npub struct State {{ bits: {storage} }}\nimpl State {{ pub fn access(&self, index: usize) {{ {body} }} }}"
            );
            let findings = container_findings(&source, block);
            assert_eq!(!findings.is_empty(), expected, "B={block}: {source}");
            for finding in findings {
                assert!(finding.static_pattern.unwrap().distinct_accesses);
            }
        }
    }
}

#[test]
fn pointer_element_effects_do_not_mutate_contiguous_pointer_slots() {
    for block in [32, 64, 128] {
        for storage in [
            "Vec<Arc<AtomicU64>>",
            "Vec<Box<AtomicU64>>",
            "Vec<&'static AtomicU64>",
            "Box<[Arc<AtomicU64>]>",
        ] {
            let source = format!(
                "use std::sync::{{Arc, atomic::{{AtomicU64, Ordering::Relaxed}}}};\npub struct State {{ bits: {storage} }}\nimpl State {{ pub fn update(&self, index: usize) {{ self.bits[index].fetch_add(1, Relaxed); }} }}"
            );
            assert!(
                container_findings(&source, block).is_empty(),
                "B={block}: {source}"
            );
        }
        for (projection, expected) in [(0, false), (1, true)] {
            let source = format!(
                "use std::sync::{{Arc, atomic::{{AtomicU64, Ordering::Relaxed}}}};\npub struct State {{ bits: Vec<(Arc<AtomicU64>, AtomicU64)> }}\nimpl State {{ pub fn update(&self, index: usize) {{ self.bits[index].{projection}.fetch_add(1, Relaxed); }} }}"
            );
            assert_eq!(
                !container_findings(&source, block).is_empty(),
                expected,
                "B={block}: {source}"
            );
        }
    }
}

#[test]
fn private_container_in_a_non_sync_owner_needs_a_legal_sharing_path() {
    for block in [32, 64, 128] {
        for (owner, projection, expected) in [
            ("std::rc::Rc<()>", "", false),
            ("std::cell::Cell<usize>", "", false),
            (
                "std::rc::Rc<()>",
                "pub fn bits(&self) -> &[AtomicU64] { &self.bits }",
                true,
            ),
            ("usize", "", true),
        ] {
            let source = format!(
                "use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};\npub struct State {{ bits: Vec<AtomicU64>, owner: {owner} }}\nimpl State {{ {projection} pub fn update(&self, index: usize) {{ self.bits[index].fetch_add(1, Relaxed); }} }}"
            );
            assert_eq!(
                !container_findings(&source, block).is_empty(),
                expected,
                "B={block}: {source}"
            );
        }
    }
}

#[test]
fn constant_index_tracking_respects_shadowing_and_other_fields() {
    for body in [
        "let slot = 0; { let slot = index; self.bits[slot].fetch_add(1, Relaxed); }",
        "let slot = 0; for slot in 0..2 { self.bits[slot].fetch_add(1, Relaxed); }",
        "let mut slot = 0; if index > 0 { slot = index; } self.bits[slot].fetch_add(1, Relaxed);",
        "let mut slot = 0; for _ in 0..2 { self.bits[slot].fetch_add(1, Relaxed); slot += 1; }",
        "let mut slot = 0; change(&mut slot); self.bits[slot].fetch_add(1, Relaxed);",
    ] {
        let source = format!(
            "use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};\npub struct State {{ bits: Vec<AtomicU64> }}\nimpl State {{ pub fn access(&self, index: usize) {{ {body} }} }}"
        );
        assert!(!container_findings(&source, 64).is_empty(), "{source}");
    }
    let source = "use std::sync::atomic::{AtomicU64, Ordering::Relaxed};\npub struct State { unused: Vec<AtomicU64>, bits: Vec<AtomicU64> }\nimpl State { pub fn access(&self, index: usize) { self.bits[index].fetch_add(1, Relaxed); } }";
    assert!(
        container_findings(source, 64)
            .iter()
            .any(|finding| finding.field_list == ["bits"])
    );
}

#[test]
fn container_mutation_requires_a_write_to_the_selected_elements() {
    let source = "use std::sync::atomic::{AtomicU64, Ordering::Relaxed};\npub struct State { bits: Vec<AtomicU64> }\nimpl State { pub fn access(&mut self, index: usize) { self.bits.push(AtomicU64::new(0)); self.bits[index].load(Relaxed); } }";
    assert!(container_findings(source, 64).is_empty());
}

#[test]
fn a_finished_while_let_does_not_weaken_a_later_constant_assignment() {
    let source = "use std::sync::atomic::{AtomicU64, Ordering::Relaxed};\npub struct State { bits: Vec<AtomicU64> }\nimpl State { pub fn access(&self, index: usize) { let mut slot = index; while let Some(_) = next() { break; } slot = 0; self.bits[slot].fetch_add(1, Relaxed); } }";
    assert!(container_findings(source, 64).is_empty());
}

#[test]
fn pattern_bound_indices_shadow_constants_in_each_control_form() {
    for block in [32, 64, 128] {
        for body in [
            "if let Some(slot) = input { self.bits[slot].fetch_add(1, Relaxed); }",
            "if let Some(slot) = input && slot < self.bits.len() { self.bits[slot].fetch_add(1, Relaxed); }",
            "match input { Some(slot) => { self.bits[slot].fetch_add(1, Relaxed); }, None => {} }",
            "match input { Some(slot @ 0) | Some(slot) => { self.bits[slot].fetch_add(1, Relaxed); }, _ => {} }",
            "while let Some(slot) = input { self.bits[slot].fetch_add(1, Relaxed); break; }",
            "while let Some(slot) = input && slot < self.bits.len() { self.bits[slot].fetch_add(1, Relaxed); break; }",
        ] {
            let source = format!(
                "use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};\npub struct State {{ bits: Vec<AtomicU64> }}\nimpl State {{ pub fn access(&self, input: Option<usize>) {{ let slot = 0; {body} }} }}"
            );
            assert!(!container_findings(&source, block).is_empty(), "{source}");
        }
        for body in [
            "if let Some(slot) = input { consume(slot); } self.bits[slot].fetch_add(1, Relaxed);",
            "if let Some(slot) = input { consume(slot); } else { self.bits[slot].fetch_add(1, Relaxed); }",
            "match input { Some(slot) => consume(slot), None => {} } self.bits[slot].fetch_add(1, Relaxed);",
            "while let Some(slot) = input { consume(slot); break; } self.bits[slot].fetch_add(1, Relaxed);",
        ] {
            let source = format!(
                "use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};\nfn consume(_: usize) {{}}\npub struct State {{ bits: Vec<AtomicU64> }}\nimpl State {{ pub fn access(&self, input: Option<usize>) {{ let slot = 0; {body} }} }}"
            );
            assert!(container_findings(&source, block).is_empty(), "{source}");
        }
    }
}

#[test]
fn mutable_index_effects_in_methods_and_aliases_remove_constant_proofs() {
    for block in [32, 64, 128] {
        for body in [
            "let mut slot = 0; Selector.pick(&mut slot, index); self.bits[slot].fetch_add(1, Relaxed);",
            "let mut slot = 0; slot.clone_from(&index); self.bits[slot].fetch_add(1, Relaxed);",
            "let mut slot = 0; let reference = &mut slot; *reference = index; self.bits[slot].fetch_add(1, Relaxed);",
            "let mut slot = 0; Selector.pick(&mut (slot), index); self.bits[slot].fetch_add(1, Relaxed);",
            "let mut slot = 0; let pointer = &raw mut slot; unsafe { *pointer = index; } self.bits[slot].fetch_add(1, Relaxed);",
            "let mut slot = 0; let pointer = std::ptr::addr_of_mut!(slot); unsafe { *pointer = index; } self.bits[slot].fetch_add(1, Relaxed);",
            "let mut slot = 0; select!(slot, index); self.bits[slot].fetch_add(1, Relaxed);",
            "let mut slot = 0; for index in 0..3 { self.bits[slot].fetch_add(1, Relaxed); slot.clone_from(&index); }",
            "let mut slot = 0; for index in 0..3 { self.bits[slot].fetch_add(1, Relaxed); Selector.pick(&mut slot, index); }",
            "let mut slot = 0; for index in 0..3 { self.bits[slot].fetch_add(1, Relaxed); let reference = &mut slot; *reference = index; }",
        ] {
            let source = format!(
                "use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};\nmacro_rules! select {{ ($slot:ident, $index:expr) => {{ $slot = $index; }} }}\nstruct Selector;\nimpl Selector {{ fn pick(&self, slot: &mut usize, index: usize) {{ *slot = index; }} }}\npub struct State {{ bits: Vec<AtomicU64> }}\nimpl State {{ pub fn access(&self, index: usize) {{ {body} }} }}"
            );
            assert!(!container_findings(&source, block).is_empty(), "{source}");
        }
        for body in [
            "let slot: usize = 0; consume(slot.count_ones() as usize); self.bits[slot].fetch_add(1, Relaxed);",
            "let mut slot = 0; slot.clone_from(&index); slot = 0; self.bits[slot].fetch_add(1, Relaxed);",
            "let mut slot = 0; let reference = &mut slot; *reference = index; slot = 0; self.bits[slot].fetch_add(1, Relaxed);",
        ] {
            let source = format!(
                "use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};\nfn consume(_: usize) {{}}\npub struct State {{ bits: Vec<AtomicU64> }}\nimpl State {{ pub fn access(&self, index: usize) {{ {body} }} }}"
            );
            assert!(container_findings(&source, block).is_empty(), "{source}");
        }
    }
}

#[test]
fn a_shadowing_initializer_uses_the_previous_index_binding() {
    let source = "use std::sync::atomic::{AtomicU64, Ordering::Relaxed};\npub struct State { bits: Vec<AtomicU64> }\nimpl State { pub fn access(&self, index: usize) { let slot = index; let slot = { self.bits[slot].fetch_add(1, Relaxed); 0 }; self.bits[slot].load(Relaxed); } }";
    assert!(!container_findings(source, 64).is_empty());
}

#[test]
fn unresolved_narrow_arithmetic_is_not_an_out_of_bounds_proof() {
    let source = "#![allow(arithmetic_overflow)]\nuse std::sync::atomic::{AtomicU64, Ordering::Relaxed};\npub struct State { bits: [AtomicU64; 2] }\nimpl State { pub fn access(&self) { let left = 255u8; let right = 1u8; let slot = (left + right) as usize; self.bits[slot].fetch_add(1, Relaxed); self.bits[1].load(Relaxed); } }";
    assert!(!container_findings(source, 64).is_empty());
}

#[test]
fn native_element_accessors_preserve_index_constraints() {
    for block in [32, 64, 128] {
        for storage in ["Vec<AtomicU64>", "Box<[AtomicU64]>", "[AtomicU64; 2]"] {
            for (body, expected) in [
                ("self.bits.get(index).unwrap().fetch_add(1, Relaxed);", true),
                (
                    "self.bits.get(index).expect(\"slot\").fetch_add(1, Relaxed);",
                    true,
                ),
                (
                    "unsafe { self.bits.get_unchecked(index).fetch_add(1, Relaxed); }",
                    true,
                ),
                ("self.bits.get(0).unwrap().fetch_add(1, Relaxed);", false),
                (
                    "self.bits.get(0).unwrap().fetch_add(1, Relaxed); self.bits.get(1).unwrap().load(Relaxed);",
                    true,
                ),
                ("self.bits.get(index).unwrap().load(Relaxed);", false),
                (
                    "self.bits.get(0..2).unwrap()[0].fetch_add(1, Relaxed);",
                    false,
                ),
            ] {
                let source = format!(
                    "use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};\npub struct State {{ bits: {storage} }}\nimpl State {{ pub fn access(&self, index: usize) {{ {body} }} }}"
                );
                assert_eq!(
                    !container_findings(&source, block).is_empty(),
                    expected,
                    "B={block}: {source}"
                );
            }
        }
        let source = "use std::sync::RwLock;\npub struct State { slots: Box<[RwLock<usize>]> }\nimpl State { pub fn access(&self, index: usize) { unsafe { *self.slots.get_unchecked(index).write().unwrap() += 1; } } }";
        assert!(!container_findings(source, block).is_empty(), "B={block}");
        let exclusive = "use std::sync::atomic::{AtomicU64, Ordering::Relaxed};\npub struct State { bits: Vec<AtomicU64> }\nimpl State { pub fn access(&mut self, index: usize) { self.bits.get_mut(index).unwrap().fetch_add(1, Relaxed); } }";
        assert!(container_findings(exclusive, block).is_empty(), "B={block}");
    }
}

#[test]
fn separate_containers_keep_complete_separate_pair_witnesses() {
    let source = "use std::sync::atomic::{AtomicU64, Ordering::Relaxed};\npub struct State { first: Vec<AtomicU64>, second: Vec<AtomicU64> }\nimpl State { pub fn access(&self, index: usize) { self.first[index].fetch_add(1, Relaxed); self.second[index].fetch_add(1, Relaxed); } }";
    for block in [32, 64, 128] {
        let findings = container_findings(source, block);
        assert_eq!(findings.len(), 2, "B={block}: {findings:#?}");
        assert_ne!(findings[0].finding_group_id, findings[1].finding_group_id);
        for finding in findings {
            assert_eq!(finding.field_list.len(), 1);
            let field = &finding.field_list[0];
            assert_eq!(
                finding.static_pattern.unwrap().witness_locations,
                [format!("{field}[i]"), format!("{field}[j]")]
            );
        }
    }
}
