use false_sharing_detector::cpp_detection::{
    analyze_cpp_path_with_options, evidence::collect_cpp_evidence, layout::collect_cpp_structs,
    parser::parse_cpp_files, types::CppFile,
};
use false_sharing_detector::types::AnalysisOptions;
use false_sharing_detector::types::RuleId;

fn source(expression: &str) -> String {
    format!(
        "struct State {{\nstd::atomic<int> counter;\nstd::atomic<int> peer;\nvoid update() {{ counter.fetch_add(1); }}\nauto inspect() {{ return {expression}; }}\n}};\nstd::shared_ptr<State> shared;\n"
    )
}

#[test]
fn noexcept_operands_do_not_supply_reads_writes_or_same_line_fallback() {
    for block in [32, 64, 128] {
        for (expression, expected) in [
            ("peer.load()", true),
            ("noexcept(peer.load())", false),
            ("noexcept(peer.fetch_add(1))", false),
            ("noexcept(noexcept(peer.fetch_add(1)))", false),
            ("requires { peer.load(); }", false),
            ("requires { peer.fetch_add(1); }", false),
            ("requires (int value) { peer.fetch_add(value); }", false),
            ("(requires { counter.load(); }) + peer.load()", true),
            ("noexcept(peer.load()) + unknown->counter", false),
            ("noexcept(counter.load()) + peer.load()", true),
        ] {
            let root = tempfile::tempdir().unwrap();
            std::fs::write(root.path().join("state.hpp"), source(expression)).unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
            options.cache_line_size = block;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "B={block}: {expression}\n{report:#?}"
            );
        }
    }
}

#[test]
fn runtime_view_keeps_original_type_source_and_live_access_locations() {
    let original = source("noexcept(peer.load()) + counter.load()");
    let files = parse_cpp_files(vec![CppFile {
        path: "state.hpp".into(),
        source: original.clone(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    assert_eq!(
        files[0].source, original,
        "type/layout input must remain original"
    );
    assert!(
        facts[0]
            .items
            .iter()
            .any(|a| a.field_name.as_deref() == Some("counter") && a.line == 5)
    );
    assert!(
        !facts[0]
            .items
            .iter()
            .any(|a| a.field_name.as_deref() == Some("peer") && a.access_kind.is_some())
    );
}

#[test]
fn keyword_macro_and_c_function_arguments_remain_runtime_accesses() {
    for prefix in [
        "#define noexcept(x) x\n",
        "#if CONFIG\n#define noexcept(x) x\n#endif\n",
        "bool noexcept(bool);\n",
    ] {
        let root = tempfile::tempdir().unwrap();
        std::fs::write(
            root.path().join("state.hpp"),
            format!("{prefix}{}", source("noexcept(peer.load())")),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(root.path(), &AnalysisOptions::all_rules());
        assert!(!report.findings.is_empty(), "{prefix}: {report:#?}");
    }
    let files = parse_cpp_files(vec![CppFile {
        path: "state.c".into(),
        source: "struct State { int counter; int peer; };\nint inspect(struct State *s) { return noexcept(s->peer); }\n".into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    let facts = collect_cpp_evidence(&files, &records);
    assert!(
        facts[0]
            .items
            .iter()
            .any(|a| a.field_name.as_deref() == Some("peer") && a.access_kind.is_some())
    );
}

#[test]
fn compile_command_keyword_overrides_preserve_runtime_operands() {
    for extra in [
        vec!["-Dnoexcept(x)=x"],
        vec!["-D", "noexcept(x)=x"],
        vec!["-include", "compat.hpp"],
    ] {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("state.cpp");
        std::fs::write(&path, source("noexcept(peer.load())")).unwrap();
        let mut args = vec!["clang++".to_owned()];
        args.extend(extra.iter().map(|s| s.to_string()));
        args.push(path.to_string_lossy().into_owned());
        let database = serde_json::json!([{"directory":root.path(),"file":path,"arguments":args}]);
        std::fs::write(
            root.path().join("compile_commands.json"),
            database.to_string(),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(root.path(), &AnalysisOptions::all_rules());
        assert!(!report.findings.is_empty(), "{extra:?}: {report:#?}");
    }
}

#[test]
fn indexed_atomic_writes_inside_noexcept_are_not_runtime_candidates() {
    for operation in [
        "values[worker].fetch_add(1)",
        "noexcept(values[worker].fetch_add(1))",
        "requires { values[worker].fetch_add(1); }",
    ] {
        let root = tempfile::tempdir().unwrap();
        std::fs::write(root.path().join("state.cpp"), format!(
            "std::atomic<int> values[8];\nvoid run() {{\n#pragma omp parallel for\nfor(int worker=0;worker<8;++worker) {{ {operation}; }}\n}}\n"
        )).unwrap();
        let report = analyze_cpp_path_with_options(root.path(), &AnalysisOptions::all_rules());
        assert_eq!(
            !report.findings.is_empty(),
            operation.starts_with("values"),
            "{operation}: {report:#?}"
        );
    }
}

#[test]
fn macro_expansion_can_change_an_apparent_noexcept_operand() {
    for (prefix, expression) in [
        (
            "#define 包装(x) evaluate_##x\n",
            "包装(noexcept(peer.load()))",
        ),
        ("#define noex\\\ncept(x) x\n", "noexcept(peer.load())"),
        (
            "#define APPLY(x) evaluate_##x\n",
            "APPLY(noexcept(peer.load()))",
        ),
        (
            "#define ESCAPE(x) x)) + x + noexcept((x\n",
            "noexcept((ESCAPE(peer.load())))",
        ),
    ] {
        let root = tempfile::tempdir().unwrap();
        std::fs::write(
            root.path().join("state.hpp"),
            format!("{prefix}{}", source(expression)),
        )
        .unwrap();
        let report = analyze_cpp_path_with_options(root.path(), &AnalysisOptions::all_rules());
        assert!(!report.findings.is_empty(), "{expression}: {report:#?}");
    }
}

#[test]
fn requires_keyword_macro_is_not_a_constraint_expression_proof() {
    for (prefix, expected) in [("", false), ("#define requires if (true)\n", true)] {
        let root = tempfile::tempdir().unwrap();
        let body = source("0").replace("return 0;", "requires { peer.load(); }; return true;");
        std::fs::write(root.path().join("state.hpp"), format!("{prefix}{body}")).unwrap();
        let report = analyze_cpp_path_with_options(root.path(), &AnalysisOptions::all_rules());
        assert_eq!(
            !report.findings.is_empty(),
            expected,
            "{prefix}: {report:#?}"
        );
    }
}
