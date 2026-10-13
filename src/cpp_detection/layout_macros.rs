//! Bounded numeric source defaults for record alignment annotations.
//! Follow direct quoted includes and join both unknown preprocessor branches.
//! This is an alignment lower bound, not an exact target/ABI layout.
use crate::cpp_detection::parser::CodeChildren;
use std::collections::HashMap;
use std::path::Path;

use super::parser::{ParsedCppFile, node_text, walk_nodes};
use super::types::{CppCompileCommand, CppStructInfo};

#[path = "record_alignment_macros.rs"]
mod record_alignment_macros;

pub(super) fn type_alignment_wrapper_names(
    files: &[ParsedCppFile],
) -> std::collections::HashSet<String> {
    record_alignment_macros::collect_wrappers(files)
        .into_keys()
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Value {
    Defined(Option<usize>),
    Unknown,
}
type State = HashMap<String, Value>;

pub(super) fn apply(
    files: &[ParsedCppFile],
    records: &mut [CppStructInfo],
    commands: &[CppCompileCommand],
) {
    let annotation = regex::Regex::new(r"(?:alignas|aligned)\s*\(\s*([A-Za-z_]\w*)\s*\)").unwrap();
    let files_by_path: HashMap<_, _> = files.iter().map(|f| (f.path.as_str(), f)).collect();
    let definitions = regex::Regex::new(r"(?m)^\s*#\s*(?:define|undef)\s+([A-Za-z_]\w*)").unwrap();
    let mut definition_files = HashMap::<String, std::collections::HashSet<&str>>::new();
    for file in files {
        for definition in definitions.captures_iter(&file.source) {
            definition_files
                .entry(definition[1].to_string())
                .or_default()
                .insert(&file.path);
        }
    }
    record_alignment_macros::apply(files, records, commands, &files_by_path, &definition_files);
    for record in records {
        if record.align_bytes.is_some() {
            continue;
        }
        let Some(file) = files_by_path.get(record.file.as_str()) else {
            continue;
        };
        let header = file
            .source
            .lines()
            .skip(record.line.saturating_sub(1))
            .take(4)
            .collect::<Vec<_>>()
            .join("\n");
        let header = header.split('{').next().unwrap_or("");
        // This bounded recognizer accepts a literal annotation, not text in
        // comments/strings. Ambiguous decorated headers stay symbolic.
        if header.contains("/*") || header.contains("//") || header.contains('"') {
            continue;
        }
        let Some(capture) = annotation.captures(header) else {
            continue;
        };
        let name = &capture[1];
        let mut visible = std::collections::HashSet::from([file.path.clone()]);
        for line in file.source.lines().take(record.line.saturating_sub(1)) {
            if let Some(relative) = line
                .trim()
                .strip_prefix("#include ")
                .map(str::trim)
                .and_then(|s| s.strip_prefix('"'))
                .and_then(|s| s.strip_suffix('"'))
            {
                visible.insert(
                    Path::new(&file.path)
                        .parent()
                        .unwrap_or(Path::new(""))
                        .join(relative)
                        .to_string_lossy()
                        .into_owned(),
                );
            }
        }
        // Definitions outside the directly interpreted sources may come from
        // an ignored transitive include. Refuse that ambiguous default.
        if definition_files
            .get(name)
            .is_some_and(|paths| paths.iter().any(|path| !visible.contains(*path)))
        {
            continue;
        }
        // A command-line override or forced include can change a header's
        // default. Until variants are preprocessed, retain the symbolic risk.
        if commands.iter().any(|command| {
            command.arguments.iter().any(|arg| {
                arg == "-D"
                    || arg == "-U"
                    || arg.starts_with(&format!("-D{name}"))
                    || arg.starts_with(&format!("-U{name}"))
                    || arg.starts_with("-include")
                    || arg.starts_with("-imacros")
                    || arg.starts_with('@')
            })
        }) {
            continue;
        }
        let mut state = State::new();
        process(
            file,
            Some(record.line.saturating_sub(1)),
            true,
            &files_by_path,
            &mut state,
        );
        let alignment = match state.get(name) {
            Some(Value::Defined(value)) => *value,
            Some(Value::Unknown) => None,
            None => scoped_literal_constant(file, record, name, &definition_files, commands),
        };
        if let Some(alignment) = alignment
            && alignment.is_power_of_two()
        {
            record.align_bytes = Some(alignment);
            record.is_cache_aligned = alignment >= record.cache_line_size;
            record.total_estimated_size = record.total_estimated_size.and_then(|size| {
                size.checked_add(alignment - 1)
                    .map(|size| size / alignment * alignment)
            });
        }
    }
}

/// A unique integral constant in the record's own lexical scope can supply an
/// alignment value. Do not turn same-spelled constants in other scopes or an
/// unresolved template argument into layout facts. Expressions/aliases and
/// cross-file C++ name lookup remain symbolic in this bounded recognizer.
fn scoped_literal_constant(
    file: &ParsedCppFile,
    record: &CppStructInfo,
    name: &str,
    macros: &HashMap<String, std::collections::HashSet<&str>>,
    commands: &[CppCompileCommand],
) -> Option<usize> {
    let keywords = [
        "constexpr",
        "const",
        "static",
        "int",
        "unsigned",
        "signed",
        "short",
        "long",
        "alignas",
        "aligned",
    ];
    if macros.contains_key(name)
        || keywords.iter().any(|k| macros.contains_key(*k))
        || commands.iter().any(|command| {
            command.arguments.iter().any(|arg| {
                arg.starts_with("/FI")
                    || arg == "/D"
                    || arg == "/U"
                    || ["-D", "-U", "/D", "/U"].iter().any(|prefix| {
                        arg.strip_prefix(prefix).is_some_and(|value| {
                            let value = value.split(['=', '(']).next().unwrap_or(value);
                            value == name || keywords.contains(&value)
                        })
                    })
            })
        })
    {
        return None;
    }
    let tree = file.tree.as_ref()?;
    let mut target = Vec::new();
    let mut declarations = Vec::new();
    let mut shadow = false;
    walk_nodes(tree.root_node(), &mut |node| {
        if matches!(
            node.kind(),
            "struct_specifier" | "class_specifier" | "union_specifier"
        ) && node.start_position().row + 1 == record.line
            && node
                .child_by_field_name("name")
                .is_some_and(|n| node_text(n, &file.source) == record.name)
        {
            target.push(node);
        }
        if matches!(
            node.kind(),
            "enumerator" | "alias_declaration" | "type_parameter_declaration"
        ) && node
            .child_by_field_name("name")
            .is_some_and(|n| node_text(n, &file.source) == name)
        {
            shadow = true;
        }
        if node.kind() == "using_declaration"
            && node_text(node, &file.source)
                .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .any(|t| t == name)
        {
            shadow = true;
        }
        if !matches!(
            node.kind(),
            "declaration"
                | "field_declaration"
                | "parameter_declaration"
                | "optional_parameter_declaration"
        ) {
            return;
        }
        for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
            let mut inner = declarator;
            while let Some(child) = inner.child_by_field_name("declarator") {
                inner = child;
            }
            if node_text(inner, &file.source) == name {
                declarations.push((node, declarator));
            }
        }
    });
    if shadow || target.len() != 1 || declarations.len() != 1 {
        return None;
    }
    let (declaration, declarator) = declarations[0];
    if declaration.has_error()
        || declaration.end_byte() >= target[0].start_byte()
        || !super::initialization::unconditionally_preprocessed(declaration, &file.source)
        || constant_scope(declaration) != constant_scope(target[0])
        || !matches!(declaration.kind(), "declaration" | "field_declaration")
        || declarator.kind() != "init_declarator"
        || declarator
            .child_by_field_name("declarator")
            .is_none_or(|n| n.kind() != "identifier")
    {
        return None;
    }
    let children = declaration
        .named_code_children(&mut declaration.walk())
        .collect::<Vec<_>>();
    if !children.iter().any(|n| {
        n.kind() == "type_qualifier" && matches!(node_text(*n, &file.source), "const" | "constexpr")
    }) || children
        .iter()
        .any(|n| n.kind() == "type_qualifier" && node_text(*n, &file.source) == "volatile")
        || (declaration.kind() == "field_declaration"
            && !children.iter().any(|n| {
                n.kind() == "storage_class_specifier" && node_text(*n, &file.source) == "static"
            }))
    {
        return None;
    }
    let ty = declaration.child_by_field_name("type")?;
    if !matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
        || !node_text(ty, &file.source)
            .split_whitespace()
            .all(|s| matches!(s, "int" | "unsigned" | "signed" | "short" | "long"))
    {
        return None;
    }
    let mut value = declarator.child_by_field_name("value")?;
    while value.kind() == "parenthesized_expression" {
        value = value.named_code_child(0)?;
    }
    if value.kind() != "number_literal" {
        return None;
    }
    let spelling = node_text(value, &file.source).replace('\'', "");
    let literal = spelling.trim_end_matches(['u', 'U', 'l', 'L']);
    let (digits, base) = if let Some(v) = literal
        .strip_prefix("0x")
        .or_else(|| literal.strip_prefix("0X"))
    {
        (v, 16)
    } else if let Some(v) = literal
        .strip_prefix("0b")
        .or_else(|| literal.strip_prefix("0B"))
    {
        (v, 2)
    } else if literal.starts_with('0') && literal.len() > 1 {
        (&literal[1..], 8)
    } else {
        (literal, 10)
    };
    let value = usize::from_str_radix(digits, base).ok()?;
    // Every admitted builtin integer type represents these positive values,
    // independently of the target ABI. Do not infer alignment after overflow.
    (value.is_power_of_two() && value <= 32767).then_some(value)
}

fn constant_scope(mut node: tree_sitter::Node<'_>) -> Option<tree_sitter::Node<'_>> {
    while let Some(parent) = node.parent() {
        if matches!(
            parent.kind(),
            "translation_unit"
                | "declaration_list"
                | "field_declaration_list"
                | "compound_statement"
        ) {
            return Some(parent);
        }
        node = parent;
    }
    None
}

fn join(left: State, right: State) -> State {
    let mut result = State::new();
    for name in left.keys().chain(right.keys()) {
        let value = match (left.get(name), right.get(name)) {
            (Some(Value::Defined(Some(a))), Some(Value::Defined(Some(b))))
                if a.is_power_of_two() && b.is_power_of_two() =>
            {
                Value::Defined(Some((*a).min(*b)))
            }
            (Some(a), Some(b)) if a == b => *a,
            _ => Value::Unknown,
        };
        result.insert(name.clone(), value);
    }
    result
}

struct Branch {
    before: State,
    first: Option<State>,
    condition: Option<bool>,
    has_else: bool,
}

fn process(
    file: &ParsedCppFile,
    limit: Option<usize>,
    follow_includes: bool,
    files: &HashMap<&str, &ParsedCppFile>,
    state: &mut State,
) {
    let mut source = file.source.as_bytes().to_vec();
    if let Some(tree) = &file.tree {
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() == "comment" {
                for byte in &mut source[node.byte_range()] {
                    if *byte != b'\n' {
                        *byte = b' ';
                    }
                }
            }
        });
    } else {
        return;
    }
    let source = String::from_utf8_lossy(&source);
    let mut branches = Vec::<Branch>::new();
    for line in source.lines().take(limit.unwrap_or(usize::MAX)) {
        let Some(directive) = line.trim().strip_prefix('#') else {
            continue;
        };
        let mut parts = directive.trim().splitn(2, char::is_whitespace);
        let op = parts.next().unwrap_or("");
        let rest = parts.next().unwrap_or("").trim();
        match op {
            "if" | "ifdef" | "ifndef" => {
                let condition = match op {
                    "ifndef" => match state.get(rest) {
                        None => Some(true),
                        Some(Value::Defined(_)) => Some(false),
                        _ => None,
                    },
                    "ifdef" => match state.get(rest) {
                        Some(Value::Defined(_)) => Some(true),
                        _ => None,
                    },
                    _ => match rest {
                        "0" => Some(false),
                        "1" => Some(true),
                        _ => None,
                    },
                };
                branches.push(Branch {
                    before: state.clone(),
                    first: None,
                    condition,
                    has_else: false,
                });
            }
            "else" | "elif" => {
                let Some(branch) = branches.last_mut() else {
                    state.clear();
                    return;
                };
                if branch.has_else {
                    state.clear();
                    return;
                }
                branch.first = Some(match branch.first.take() {
                    Some(first) => join(first, state.clone()),
                    None => state.clone(),
                });
                branch.has_else = op == "else";
                if op == "elif" {
                    branch.condition = None;
                }
                *state = branch.before.clone();
            }
            "endif" => {
                let Some(branch) = branches.pop() else {
                    state.clear();
                    return;
                };
                let (first, second) = match branch.first {
                    Some(first) => (
                        first,
                        if branch.has_else {
                            state.clone()
                        } else {
                            join(state.clone(), branch.before)
                        },
                    ),
                    None => (state.clone(), branch.before),
                };
                *state = match branch.condition {
                    Some(true) => first,
                    Some(false) => second,
                    None => join(first, second),
                };
            }
            "define" => {
                let mut parts = rest.splitn(2, char::is_whitespace);
                let name = parts.next().unwrap_or("");
                let value = parts.next().unwrap_or("").trim();
                if name.contains('(') {
                    continue;
                }
                let number = value.parse::<usize>().ok();
                state.insert(name.to_string(), Value::Defined(number));
            }
            "undef" => {
                state.remove(rest);
            }
            "include" if follow_includes => {
                if let Some(relative) = rest.strip_prefix('"').and_then(|r| r.strip_suffix('"')) {
                    let path = Path::new(&file.path)
                        .parent()
                        .unwrap_or(Path::new(""))
                        .join(relative);
                    if let Some(included) = files.get(path.to_string_lossy().as_ref()) {
                        process(included, None, false, files, state);
                    }
                }
            }
            _ => {}
        }
    }
    // The caller may end inside its own conventional header guard; that does
    // not alter the active branch at the declaration. Included files must close.
    if limit.is_none() && !branches.is_empty() {
        state.clear();
    } else {
        for branch in branches.into_iter().rev() {
            if branch.condition != Some(true) || branch.has_else {
                *state = join(state.clone(), branch.before);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpp_detection::{
        layout::collect_cpp_structs, parser::parse_cpp_files, types::CppFile,
    };

    #[test]
    fn alignment_defaults_join_all_branches_and_require_a_visible_definition() {
        for (config, include, expected) in [
            ("#define SLOT_ALIGN 64", true, Some(64)),
            (
                "#ifndef SLOT_ALIGN\n#if defined(ARCH)\n#define SLOT_ALIGN 128\n#else\n#define SLOT_ALIGN 64\n#endif\n#endif",
                true,
                Some(64),
            ),
            (
                "#if ARCH\n#define SLOT_ALIGN 128\n#elif OTHER\n#define SLOT_ALIGN 32\n#else\n#define SLOT_ALIGN 64\n#endif",
                true,
                Some(32),
            ),
            ("#if ARCH\n#define SLOT_ALIGN 64\n#endif", true, None),
            (
                "#if ARCH\n#define SLOT_ALIGN 64\n#else\n#define SLOT_ALIGN UNKNOWN\n#endif",
                true,
                None,
            ),
            ("#define SLOT_ALIGN 64\n#undef SLOT_ALIGN", true, None),
            ("#define SLOT_ALIGN 64", false, None),
            ("/*\n#define SLOT_ALIGN 64\n*/", true, None),
        ] {
            let files = parse_cpp_files(vec![
                CppFile {
                    path: "config.h".into(),
                    source: config.into(),
                },
                CppFile {
                    path: "state.h".into(),
                    source: format!(
                        "{}\nstruct __attribute__((aligned(SLOT_ALIGN))) State {{ std::atomic<int> first; std::atomic<int> second; }};",
                        if include { "#include \"config.h\"" } else { "" }
                    ),
                },
            ]);
            let mut records = collect_cpp_structs(&files, "sample", 64);
            apply(&files, &mut records, &[]);
            let record = records.iter().find(|r| r.name == "State").unwrap();
            assert_eq!(record.align_bytes, expected, "{config}: {record:#?}");
            assert!(
                crate::cpp_detection::layout::fields_may_share_cache_line(
                    record,
                    &["first".into(), "second".into()]
                ),
                "owner alignment does not isolate its internal fields"
            );
        }
    }
    #[test]
    fn literal_integer_alignment_constants_require_a_unique_same_scope_binding() {
        for (prefix, suffix, expected) in [
            ("constexpr int Boundary = 64;\n", "", Some(64)),
            ("static const unsigned Boundary = 0x40u;\n", "", Some(64)),
            (
                "namespace detail {\nstatic constexpr int Boundary = 0100;\n",
                "}",
                Some(64),
            ),
            (
                "#ifndef GUARD\n#define GUARD\nconstexpr int Boundary = 64;\n",
                "#endif",
                Some(64),
            ),
            ("int Boundary = 64;\n", "", None),
            ("int /*const*/ Boundary = 64;\n", "", None),
            ("const volatile int Boundary = 64;\n", "", None),
            ("constexpr bool Boundary = 64;\n", "", None),
            ("constexpr unsigned char Boundary = 256;\n", "", None),
            ("constexpr int Boundary = (1 << 6);\n", "", None),
            ("constexpr int Boundary = 48;\n", "", None),
            (
                "namespace unrelated { constexpr int Boundary = 64; }\n",
                "",
                None,
            ),
            (
                "namespace first { constexpr int Boundary = 64; }\nnamespace second {\n",
                "}",
                None,
            ),
            (
                "constexpr int Boundary = 64;\nnamespace nested {\n",
                "}",
                None,
            ),
            (
                "constexpr int Boundary = 64;\nnamespace nested { constexpr int Boundary = 16; }\n",
                "",
                None,
            ),
            (
                "constexpr int Boundary = 64;\ntemplate<int Boundary>\n",
                "",
                None,
            ),
            (
                "#if CONFIG\nconstexpr int Boundary = 64;\n#endif\n",
                "",
                None,
            ),
            (
                "#define constexpr\nconstexpr int Boundary = 64;\n",
                "",
                None,
            ),
            (
                "#define alignas(x)\nconstexpr int Boundary = 64;\n",
                "",
                None,
            ),
        ] {
            let source = format!(
                "{prefix}struct alignas(Boundary) Sample {{ int first; int second; }};\n{suffix}\n"
            );
            let files = parse_cpp_files(vec![CppFile {
                path: "sample.hpp".into(),
                source: source.clone(),
            }]);
            for b in [32, 64, 128] {
                let mut records = collect_cpp_structs(&files, "sample", b);
                apply(&files, &mut records, &[]);
                let record = records.iter().find(|r| r.name == "Sample").unwrap();
                assert_eq!(record.align_bytes, expected, "{source}: {record:#?}");
                assert_eq!(record.is_cache_aligned, expected.is_some_and(|a| a >= b));
                if expected.is_some() {
                    assert_eq!(record.total_estimated_size, Some(64));
                    assert!(super::super::layout::fields_may_share_cache_line(
                        record,
                        &["first".into(), "second".into()]
                    ));
                }
            }
        }
    }

    #[test]
    fn annotation_comments_and_build_overrides_do_not_prove_alignment() {
        for (decoration, arguments, expected) in [
            ("__attribute__((aligned(SLOT_ALIGN)))", vec![], Some(64)),
            ("/* aligned(SLOT_ALIGN) */", vec![], None),
            (
                "__attribute__((aligned(SLOT_ALIGN)))",
                vec!["-DSLOT_ALIGN=16"],
                None,
            ),
            (
                "__attribute__((aligned(SLOT_ALIGN)))",
                vec!["-D", "SLOT_ALIGN=16"],
                None,
            ),
            (
                "__attribute__((aligned(SLOT_ALIGN)))",
                vec!["-imacros", "override.h"],
                None,
            ),
        ] {
            let files = parse_cpp_files(vec![CppFile {
                path: "sample.h".into(),
                source: format!(
                    "#define SLOT_ALIGN 64\nstruct {decoration} Sample {{ std::atomic<int> value; }};"
                ),
            }]);
            let mut records = collect_cpp_structs(&files, "sample", 64);
            let command = CppCompileCommand {
                directory: String::new(),
                file: "sample.c".into(),
                compiler: "cc".into(),
                arguments: arguments.into_iter().map(str::to_string).collect(),
                semantic_arguments: vec![],
                command_hash: String::new(),
                variant_id: String::new(),
            };
            apply(&files, &mut records, &[command]);
            let record = records
                .iter()
                .find(|record| record.name == "Sample")
                .unwrap();
            assert_eq!(record.align_bytes, expected, "{decoration}: {record:#?}");
            if expected.is_some() {
                assert_eq!(record.total_estimated_size, Some(64));
            }
        }
    }
}
