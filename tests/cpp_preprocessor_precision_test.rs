use false_sharing_detector::cpp_detection::{
    analyze_cpp_path_with_options, evidence::collect_cpp_evidence, layout::collect_cpp_structs,
    parser::parse_cpp_files, types::CppFile,
};
use false_sharing_detector::types::AnalysisOptions;
use false_sharing_detector::types::RuleId;

const RISK: &str = "struct State {\nstd::atomic<int> counter;\nstd::atomic<int> peer;\nvoid update() { counter.fetch_add(1); }\nint inspect() { return peer.load(); }\n};\nstd::shared_ptr<State> shared;\n";

#[test]
fn only_proved_inactive_conditional_arms_lose_their_findings() {
    let cases = [
        ("$RISK", true),
        ("#if 0\n$RISK#endif\n", false),
        ("#if (0)\n$RISK#endif\n", false),
        ("#if 1\n$RISK#endif\n", true),
        ("#if UNKNOWN\n$RISK#endif\n", true),
        ("#if 1\n// continued comment \\\n#else\n$RISK#endif\n", true),
        (
            "#if 0\n// continued comment \\\n#else\n$RISK#endif\n",
            false,
        ),
        ("#if 0 \\\n || 1\n$RISK#endif\n", true),
        ("#ifdef UNKNOWN\n$RISK#endif\n", true),
        ("#if 1\nint unused;\n#else\n$RISK#endif\n", false),
        ("#if UNKNOWN\nint unused;\n#elif 0\n$RISK#endif\n", false),
        (
            "#if UNKNOWN\nint unused;\n#elif 1\nint other;\n#else\n$RISK#endif\n",
            false,
        ),
        (
            "#ifdef UNKNOWN\nint unused;\n#elif 1\nint other;\n#else\n$RISK#endif\n",
            false,
        ),
        ("#if 0\nint unused;\n#elif UNKNOWN\n$RISK#endif\n", true),
        ("#if 0\n#if UNKNOWN\n$RISK#endif\n#endif\n", false),
        ("#if UNKNOWN\n#if 0\n$RISK#endif\n#endif\n", false),
        ("#if 0\nint unused;\n#else\n$RISK#endif\n", true),
    ];
    for block in [32, 64, 128] {
        for (template, expected) in cases {
            let root = tempfile::tempdir().unwrap();
            std::fs::write(
                root.path().join("state.hpp"),
                template.replace("$RISK", RISK),
            )
            .unwrap();
            let mut options = AnalysisOptions::with_rules(&[RuleId::SameObjectFields]);
            options.cache_line_size = block;
            let report = analyze_cpp_path_with_options(root.path(), &options);
            assert_eq!(
                !report.findings.is_empty(),
                expected,
                "B={block}: {template}\n{report:#?}"
            );
            assert!(!report.analysis_incomplete, "{template}: {report:#?}");
            if !expected {
                options.cpp_include_speculative = true;
                assert!(
                    analyze_cpp_path_with_options(root.path(), &options)
                        .findings
                        .is_empty()
                );
            }
        }
    }
}

#[test]
fn inactive_members_and_accesses_are_absent_from_all_source_consumers() {
    let source = "struct State {\nint counter;\n#if 0\nOpaque unknown;\nvoid disabled() { counter++; }\n#endif\nint peer;\nvoid active() { peer++; }\n};\n";
    let files = parse_cpp_files(vec![CppFile {
        path: "state.hpp".into(),
        source: source.into(),
    }]);
    let records = collect_cpp_structs(&files, "fixture", 64);
    assert_eq!(records.len(), 1);
    assert_eq!(
        records[0]
            .fields
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        ["counter", "peer"]
    );
    assert_eq!(records[0].total_estimated_size, Some(8));
    let facts = collect_cpp_evidence(&files, &records);
    assert!(
        facts[0]
            .items
            .iter()
            .any(|a| a.function_name.as_deref() == Some("active") && a.line == 8)
    );
    assert!(
        !facts[0]
            .items
            .iter()
            .any(|a| a.function_name.as_deref() == Some("disabled"))
    );
    assert_eq!(files[0].source.len(), source.len());
    assert!(
        !files[0].source.contains("counter++"),
        "text fallback must also see the mask"
    );
}

#[test]
fn comments_and_raw_strings_cannot_open_preprocessor_regions() {
    let prefix = "/*\n#if 0\n*/\nconst char *text = R\"tag(\n#if 0\n#else\n#endif\n)tag\";\n";
    let source = format!("{prefix}{RISK}");
    let files = parse_cpp_files(vec![CppFile {
        path: "state.hpp".into(),
        source: source.clone(),
    }]);
    assert_eq!(files[0].source, source);
    let records = collect_cpp_structs(&files, "fixture", 64);
    assert!(records.iter().any(|record| record.name == "State"));
}

#[test]
fn masking_preserves_utf8_byte_offsets_crlf_and_live_source_locations() {
    let source = "#if 0\r\n// 注释\r\nint disabled;\r\n#endif\r\nstruct Live { int counter; };\r\n";
    let files = parse_cpp_files(vec![CppFile {
        path: "state.hpp".into(),
        source: source.into(),
    }]);
    let masked = &files[0].source;
    assert_eq!(masked.len(), source.len());
    for (i, byte) in source.bytes().enumerate() {
        if matches!(byte, b'\r' | b'\n') {
            assert_eq!(masked.as_bytes()[i], byte);
        }
    }
    assert_eq!(masked.find("struct Live"), source.find("struct Live"));
    let records = collect_cpp_structs(&files, "fixture", 64);
    assert_eq!(records[0].line, 5);
}

#[test]
fn missing_preprocessor_boundary_is_not_a_safe_deletion_proof() {
    let source = format!("#if 0\n{RISK}");
    let files = parse_cpp_files(vec![CppFile {
        path: "state.hpp".into(),
        source: source.clone(),
    }]);
    assert_eq!(files[0].source, source);
    assert!(files[0].tree.as_ref().unwrap().root_node().has_error());
    let source = format!("#if 0\ninvalid : garbage {{{{\n#elif 1\n{RISK}#endif\nint after;\n");
    let files = parse_cpp_files(vec![CppFile {
        path: "state.hpp".into(),
        source: source.clone(),
    }]);
    assert_eq!(
        files[0].source, source,
        "recovery must not swallow a live alternative"
    );
}
