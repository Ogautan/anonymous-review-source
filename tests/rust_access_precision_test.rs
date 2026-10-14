use false_sharing_detector::analyzer::analyze_path_with_options;
use false_sharing_detector::types::{AnalysisOptions, ColocationPattern};
use std::fs;

fn same_object_risks(source: &str, block: usize) -> usize {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("lib.rs"), source).unwrap();
    let report = analyze_path_with_options(
        root.path(),
        &AnalysisOptions {
            cache_line_size: block,
            ..AnalysisOptions::all_rules()
        },
    );
    assert!(!report.analysis_incomplete, "{report:#?}");
    report
        .findings
        .iter()
        .filter(|finding| {
            finding.static_pattern.as_ref().is_some_and(|pattern| {
                pattern.colocation_pattern == ColocationPattern::SameObjectFields
            })
        })
        .count()
}

#[test]
fn common_mutex_requires_a_live_exclusive_guard_at_every_selected_access() {
    for block in [32, 64, 128] {
        for (guard, before_write, expected) in [
            ("let _guard = GATE.lock().unwrap();", "", false),
            ("let _guard = GATE.lock().unwrap();", "drop(_guard);", true),
            (
                "let _guard = GATE.lock().unwrap();",
                "if flag { drop(_guard); }",
                true,
            ),
            ("{ let _guard = GATE.lock().unwrap(); }", "", true),
            ("let _ = GATE.lock().unwrap();", "", true),
        ] {
            let source = format!(
                r#"
use std::sync::{{Mutex, atomic::{{AtomicU64, Ordering::Relaxed}}}};
static GATE: Mutex<()> = Mutex::new(());
pub struct State {{ a: AtomicU64, b: AtomicU64 }}
impl State {{
 pub fn left(&self, flag: bool) {{ {guard} {before_write} self.a.fetch_add(1, Relaxed); }}
 pub fn right(&self) {{ let _guard = GATE.lock().unwrap(); self.b.fetch_add(1, Relaxed); }}
}}
"#
            );
            assert_eq!(
                same_object_risks(&source, block) > 0,
                expected,
                "B={block}: {source}"
            );
        }
    }
}

#[test]
fn method_arguments_can_release_a_guard_before_the_atomic_operation() {
    let source = r#"
use std::sync::{Mutex, atomic::{AtomicU64, Ordering::Relaxed}};
static GATE: Mutex<()> = Mutex::new(());
pub struct State { a: AtomicU64, b: AtomicU64 }
impl State {
 pub fn left(&self) {
  let _guard = GATE.lock().unwrap();
  self.a.fetch_add({ drop(_guard); 1 }, Relaxed);
 }
 pub fn right(&self) { let _guard = GATE.lock().unwrap(); self.b.fetch_add(1, Relaxed); }
}
"#;
    assert!(same_object_risks(source, 64) > 0);
}

#[test]
fn shared_read_guards_do_not_serialize_atomic_writes() {
    for block in [32, 64, 128] {
        for (method, expected) in [("write", false), ("read", true)] {
            let source = format!(
                r#"
use std::sync::{{RwLock, atomic::{{AtomicU64, Ordering::Relaxed}}}};
static GATE: RwLock<()> = RwLock::new(());
pub struct State {{ a: AtomicU64, b: AtomicU64 }}
impl State {{
 pub fn left(&self) {{ let _guard = GATE.{method}().unwrap(); self.a.fetch_add(1, Relaxed); }}
 pub fn right(&self) {{ let _guard = GATE.{method}().unwrap(); self.b.fetch_add(1, Relaxed); }}
}}
"#
            );
            assert_eq!(
                same_object_risks(&source, block) > 0,
                expected,
                "B={block}: {source}"
            );
        }
    }
}

#[test]
fn a_callers_guard_does_not_protect_a_spawned_closure() {
    let source = r#"
use std::sync::{Mutex, atomic::{AtomicU64, Ordering::Relaxed}};
static GATE: Mutex<()> = Mutex::new(());
pub struct State { a: AtomicU64, b: AtomicU64 }
impl State {
 pub fn left(&self) { let _guard = GATE.lock().unwrap(); std::thread::scope(|scope| {
    scope.spawn(|| { self.a.fetch_add(1, Relaxed); });
 }); }
 pub fn right(&self) { let _guard = GATE.lock().unwrap(); self.b.fetch_add(1, Relaxed); }
}
"#;
    assert!(same_object_risks(source, 64) > 0);
}

#[test]
fn same_object_pairs_keep_the_instance_through_helper_calls_and_arc_clones() {
    for block in [32, 64, 128] {
        for (argument, expected) in [("&different", false), ("&shared", true), ("&alias", true)] {
            let source = format!(
                r#"
use std::sync::{{Arc, atomic::{{AtomicU64, Ordering::Relaxed}}}};
#[repr(C, align(128))]
#[derive(Default)]
struct Stats {{ counter: AtomicU64, other: AtomicU64 }}
fn bump(s: &Stats) {{ s.counter.fetch_add(1, Relaxed); }}
fn update(shared: &Arc<Stats>) {{ let local = Arc::clone(shared); bump(&local); }}
fn update_other(s: &Stats) {{ s.other.fetch_add(1, Relaxed); }}
fn run() {{
 let shared = Arc::new(Stats::default());
 let different = Arc::new(Stats::default());
 let alias = Arc::clone(&shared);
 std::thread::scope(|scope| {{
  scope.spawn(|| update(&shared));
  scope.spawn(|| update_other({argument}));
 }});
}}
"#
            );
            assert_eq!(
                same_object_risks(&source, block) > 0,
                expected,
                "B={block}: {source}"
            );
        }
    }
}

#[test]
fn an_exposed_callee_preserves_unresolved_external_object_use() {
    let source = r#"
use std::sync::{Arc, atomic::{AtomicU64, Ordering::Relaxed}};
#[derive(Default)]
pub struct Stats { counter: AtomicU64, other: AtomicU64 }
pub fn one(s: &Arc<Stats>) { s.counter.fetch_add(1, Relaxed); }
pub fn two(s: &Arc<Stats>) { s.other.fetch_add(1, Relaxed); }
fn run() {
 let first = Arc::new(Stats::default());
 let second = Arc::new(Stats::default());
 std::thread::scope(|scope| {
  scope.spawn(|| one(&first));
  scope.spawn(|| two(&second));
 });
}
"#;
    assert!(same_object_risks(source, 64) > 0);
}

#[test]
fn a_private_helper_inherits_the_callers_global_guard() {
    let source = r#"
use std::sync::{Mutex, atomic::{AtomicU64, Ordering::Relaxed}};
static GATE: Mutex<()> = Mutex::new(());
pub struct State { a: AtomicU64, b: AtomicU64 }
fn bump_a(s: &State) { s.a.fetch_add(1, Relaxed); }
fn bump_b(s: &State) { s.b.fetch_add(1, Relaxed); }
impl State {
 pub fn left(&self) { let _guard = GATE.lock().unwrap(); bump_a(self); }
 pub fn right(&self) { let _guard = GATE.lock().unwrap(); bump_b(self); }
}
"#;
    assert_eq!(same_object_risks(source, 64), 0);
    assert!(same_object_risks(&source.replace("fn bump_a", "pub fn bump_a"), 64) > 0);
}

#[test]
fn inline_subobjects_keep_separate_bases_through_parameter_substitution() {
    for (field, expected) in [("right", false), ("left", true)] {
        let source = format!(
            r#"
use std::sync::{{Arc, atomic::{{AtomicU64, Ordering::Relaxed}}}};
#[repr(C, align(128))]
#[derive(Default)]
struct Child {{ a: AtomicU64, b: AtomicU64 }}
#[derive(Default)]
struct Parent {{ left: Child, right: Child }}
fn one(p: &Parent) {{ p.left.a.fetch_add(1, Relaxed); }}
fn two(p: &Parent) {{ p.{field}.b.fetch_add(1, Relaxed); }}
fn run() {{
 let shared = Arc::new(Parent::default());
 std::thread::scope(|scope| {{
  scope.spawn(|| one(&shared));
  scope.spawn(|| two(&shared));
 }});
}}
"#
        );
        assert_eq!(same_object_risks(&source, 64) > 0, expected, "{source}");
    }
}

#[test]
fn separate_inline_workers_keep_their_execution_roles() {
    for (receiver, expected) in [("second", false), ("first", true)] {
        let source = format!(
            r#"
use std::sync::{{Arc, atomic::{{AtomicU64, Ordering::Relaxed}}}};
#[derive(Default)]
#[repr(C, align(128))]
struct State {{ a: AtomicU64, b: AtomicU64 }}
fn run() {{
 let first = Arc::new(State::default());
 let second = Arc::new(State::default());
 std::thread::scope(|scope| {{
  scope.spawn(|| {{ first.a.fetch_add(1, Relaxed); }});
  scope.spawn(|| {{ {receiver}.b.fetch_add(1, Relaxed); }});
 }});
}}
"#
        );
        assert_eq!(same_object_risks(&source, 64) > 0, expected, "{source}");
    }
}

#[test]
fn separate_handle_locks_do_not_serialize_shared_pointee_fields() {
    let source = r#"
use std::sync::{Arc, Mutex, atomic::{AtomicU64, Ordering::Relaxed}};
struct Child { a: AtomicU64, b: AtomicU64 }
pub struct Handle { inner: Arc<Child>, gate: Mutex<()> }
impl Handle {
 pub fn one(&self) { let _guard = self.gate.lock().unwrap(); self.inner.a.fetch_add(1, Relaxed); }
 pub fn two(&self) { let _guard = self.gate.lock().unwrap(); self.inner.b.fetch_add(1, Relaxed); }
}
"#;
    assert!(same_object_risks(source, 64) > 0);
}

#[test]
fn nested_arc_allocations_keep_the_shared_pointee() {
    let source = r#"
use std::sync::{Arc, atomic::{AtomicU64, Ordering::Relaxed}};
#[derive(Default)]
struct Stats { a: AtomicU64, b: AtomicU64 }
fn one(s: &Stats) { s.a.fetch_add(1, Relaxed); }
fn two(s: &Stats) { s.b.fetch_add(1, Relaxed); }
fn run() {
 let inner = Arc::new(Stats::default());
 let first = Arc::new(inner.clone());
 let second = Arc::new(inner.clone());
 std::thread::scope(|scope| {
  scope.spawn(|| one(&first));
  scope.spawn(|| two(&second));
 });
}


"#;
    assert!(same_object_risks(source, 64) > 0);
}

#[test]
fn an_opaque_constructor_does_not_prove_distinct_pointees() {
    for factory in [
        "#[derive(Default)] struct Stats { a: AtomicU64, b: AtomicU64 }\nimpl Stats { fn default() -> &'static Stats { &ROOT } }",
        "struct Stats { a: AtomicU64, b: AtomicU64 }\nstruct Arc;\nimpl Arc { fn new(_: Stats) -> &'static Stats { &ROOT } }",
    ] {
        let source = format!(
            r#"
use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};
{factory}
static ROOT: Stats = Stats {{ a: AtomicU64::new(0), b: AtomicU64::new(0) }};
fn one(s: &Stats) {{ s.a.fetch_add(1, Relaxed); }}
fn two(s: &Stats) {{ s.b.fetch_add(1, Relaxed); }}
fn run() {{
 let first = std::sync::Arc::new(Stats {{ a: AtomicU64::new(0), b: AtomicU64::new(0) }});
 let second = std::sync::Arc::new(Stats {{ a: AtomicU64::new(0), b: AtomicU64::new(0) }});
 std::thread::scope(|scope| {{
  scope.spawn(|| one(&first));
  scope.spawn(|| two(&second));
 }});
}}
"#
        );
        let source = if factory.contains("fn default") {
            source.replace(
                "Stats { a: AtomicU64::new(0), b: AtomicU64::new(0) });",
                "Stats::default());",
            )
        } else {
            source.replace("std::sync::Arc::new", "Arc::new")
        };
        assert!(same_object_risks(&source, 64) > 0, "{source}");
    }
}

#[test]
fn an_independent_role_on_another_object_cannot_complete_a_coupled_pair() {
    for (receiver, expected) in [("second", false), ("first", true)] {
        let source = format!(
            r#"
use std::sync::{{Arc, atomic::{{AtomicU64, Ordering::Relaxed}}}};
#[derive(Default)]
#[repr(C, align(128))]
struct State {{ a: AtomicU64, b: AtomicU64 }}
fn both(s: &State) {{ s.a.fetch_add(1, Relaxed); s.b.fetch_add(1, Relaxed); }}
fn only_b(s: &State) {{ s.b.fetch_add(1, Relaxed); }}
fn run() {{
 let first = Arc::new(State::default());
 let second = Arc::new(State::default());
 std::thread::scope(|scope| {{ scope.spawn(|| both(&first)); scope.spawn(|| only_b(&{receiver})); }});
}}
"#
        );
        assert_eq!(same_object_risks(&source, 64) > 0, expected, "{source}");
    }
}

#[test]
fn local_variables_parameters_and_imports_do_not_borrow_a_global_guard_identity() {
    for shadow in [
        "let GATE = Mutex::new(());",
        "use crate::other::GATE;",
        "use crate::other::*;",
    ] {
        let source = format!(
            r#"
use std::sync::{{Mutex, atomic::{{AtomicU64, Ordering::Relaxed}}}};
static GATE: Mutex<()> = Mutex::new(());
mod other {{ pub static GATE: std::sync::Mutex<()> = std::sync::Mutex::new(()); }}
pub struct State {{ a: AtomicU64, b: AtomicU64 }}
impl State {{
 pub fn one(&self) {{ {shadow} let _guard = GATE.lock().unwrap(); self.a.fetch_add(1, Relaxed); }}
 pub fn two(&self) {{ let _guard = GATE.lock().unwrap(); self.b.fetch_add(1, Relaxed); }}
}}
"#
        );
        assert!(same_object_risks(&source, 64) > 0, "{source}");
    }
    let source = r#"
use std::sync::{Mutex, atomic::{AtomicU64, Ordering::Relaxed}};
static GATE: Mutex<()> = Mutex::new(());
pub struct State { a: AtomicU64, b: AtomicU64 }
impl State {
 pub fn one(&self, GATE: &Mutex<()>) { let _guard = GATE.lock().unwrap(); self.a.fetch_add(1, Relaxed); }
 pub fn two(&self) { let _guard = GATE.lock().unwrap(); self.b.fetch_add(1, Relaxed); }
}
"#;
    assert!(same_object_risks(source, 64) > 0);
}

#[test]
fn a_let_initializer_uses_the_outer_object_before_the_new_binding_exists() {
    let source = r#"
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
#[repr(C, align(128))]
struct State { a: AtomicU64, b: AtomicU64 }
static STATE: State = State { a: AtomicU64::new(0), b: AtomicU64::new(0) };
fn run() {
 std::thread::scope(|scope| {
  scope.spawn(|| { let STATE = State { a: { STATE.a.fetch_add(1, Relaxed); AtomicU64::new(0) }, b: AtomicU64::new(0) }; });
  scope.spawn(|| { STATE.b.fetch_add(1, Relaxed); });
 });
}
"#;
    assert!(same_object_risks(source, 64) > 0);
}

#[test]
fn a_local_std_namespace_does_not_establish_native_mutex_serialization() {
    let source = r#"
use ::std::sync::atomic::{AtomicU64, Ordering::Relaxed};
struct Gate;
impl Gate { fn lock(&self) -> Result<(), ()> { Ok(()) } }
mod std { pub mod sync { pub type Mutex = crate::Gate; } }
static GATE: std::sync::Mutex = Gate;
pub struct State { a: AtomicU64, b: AtomicU64 }
impl State {
 pub fn one(&self) { let _guard = GATE.lock().unwrap(); self.a.fetch_add(1, Relaxed); }
 pub fn two(&self) { let _guard = GATE.lock().unwrap(); self.b.fetch_add(1, Relaxed); }
}
"#;
    assert!(same_object_risks(source, 64) > 0);
}

#[test]
fn an_empty_macro_can_release_a_definition_site_guard() {
    let source = r#"
use std::sync::{Mutex, atomic::{AtomicU64, Ordering::Relaxed}};
static GATE: Mutex<()> = Mutex::new(());
pub struct State { a: AtomicU64, b: AtomicU64 }
impl State {
 pub fn one(&self) {
  let _guard = GATE.lock().unwrap();
  macro_rules! release { () => { drop(_guard); } }
  release!();
  self.a.fetch_add(1, Relaxed);
 }
 pub fn two(&self) { let _guard = GATE.lock().unwrap(); self.b.fetch_add(1, Relaxed); }
}
"#;
    for block in [32, 64, 128] {
        assert!(same_object_risks(source, block) > 0);
    }
}

#[test]
fn opaque_methods_and_macros_can_replace_a_handle_pointee() {
    for replacement in [
        "first.redirect(&second);",
        "macro_rules! redirect { () => { first = Arc::clone(&second); } } redirect!();",
    ] {
        let source = format!(
            r#"
use std::sync::{{Arc, atomic::{{AtomicU64, Ordering::Relaxed}}}};
#[derive(Default)] struct State {{ a: AtomicU64, b: AtomicU64 }}
trait Redirect {{ fn redirect(&mut self, other: &Self); }}
impl Redirect for Arc<State> {{ fn redirect(&mut self, other: &Self) {{ *self = Arc::clone(other); }} }}
fn run() {{
 let mut first = Arc::new(State::default());
 let second = Arc::new(State::default());
 {replacement}
 std::thread::scope(|scope| {{
  scope.spawn(|| {{ first.a.fetch_add(1, Relaxed); }});
  scope.spawn(|| {{ second.b.fetch_add(1, Relaxed); }});
 }});
}}
"#
        );
        for block in [32, 64, 128] {
            assert!(same_object_risks(&source, block) > 0, "{source}");
        }
    }
}

#[test]
fn scoped_workers_can_share_atomic_fields_of_owned_stack_and_box_values() {
    for initializer in ["State::default()", "Box::new(State::default())"] {
        let source = format!(
            r#"
use std::sync::atomic::{{AtomicU64, Ordering::Relaxed}};
#[derive(Default)] struct State {{ a: AtomicU64, b: AtomicU64 }}
fn run() {{
 let state = {initializer};
 std::thread::scope(|scope| {{
  scope.spawn(|| {{ state.a.fetch_add(1, Relaxed); }});
  scope.spawn(|| {{ state.b.fetch_add(1, Relaxed); }});
 }});
}}
"#
        );
        for block in [32, 64, 128] {
            assert!(same_object_risks(&source, block) > 0, "{source}");
        }
        let separate = source
            .replace("let state =", "let other = State::default(); let state =")
            .replace("scope.spawn(||", "scope.spawn(move ||")
            .replace("state.b.fetch_add", "other.b.fetch_add");
        assert_eq!(same_object_risks(&separate, 64), 0, "{separate}");
    }
}
