//! Type-attached alignment wrappers in anonymous typedef record declarations.
//! Require a unique visible object-like macro and resolve its operand at use.
//! A typedef-declarator or array-variable alignment is not a record-stride fact.
use std::collections::{HashMap, HashSet};
use std::path::Path;

use super::{State, Value, process};
use crate::cpp_detection::parser::{ParsedCppFile, node_text, walk_nodes};
use crate::cpp_detection::types::{CppCompileCommand, CppRecordKind, CppStructInfo};

pub(super) struct Wrapper {
    file: String,
    operand: String,
}

pub(super) fn apply(
    files: &[ParsedCppFile],
    records: &mut [CppStructInfo],
    commands: &[CppCompileCommand],
    files_by_path: &HashMap<&str, &ParsedCppFile>,
    definition_files: &HashMap<String, HashSet<&str>>,
) {
    let wrappers = collect_wrappers(files);
    let attachments = attached_wrappers(files, &wrappers);
    apply_attachments(
        files_by_path,
        records,
        commands,
        definition_files,
        &wrappers,
        &attachments,
    );
}

pub(super) fn collect_wrappers(files: &[ParsedCppFile]) -> HashMap<String, Wrapper> {
    let body = regex::Regex::new(
        r"^__attribute__\s*\(\s*\(\s*aligned\s*\(\s*([A-Za-z_]\w*|[0-9]+)\s*\)\s*\)\s*\)$",
    )
    .unwrap();
    let mut wrappers = HashMap::new();
    let mut counts = HashMap::<String, usize>::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(node.kind(), "preproc_def" | "preproc_function_def") {
                return;
            }
            let Some(name) = node.child_by_field_name("name") else {
                return;
            };
            let name = node_text(name, &file.source).to_owned();
            *counts.entry(name.clone()).or_default() += 1;
            if node.kind() != "preproc_def" || node.has_error() {
                return;
            }
            let Some(value) = node.child_by_field_name("value") else {
                return;
            };
            if let Some(capture) = body.captures(node_text(value, &file.source).trim()) {
                wrappers.insert(
                    name,
                    Wrapper {
                        file: file.path.clone(),
                        operand: capture[1].to_owned(),
                    },
                );
            }
        });
    }
    // Retain ambiguous or redefined macros as symbolic. Macro semantics come
    // from the replacement body, never from an annotation's spelling.
    wrappers.retain(|name, _| counts.get(name) == Some(&1));
    wrappers
}

fn apply_attachments(
    files_by_path: &HashMap<&str, &ParsedCppFile>,
    records: &mut [CppStructInfo],
    commands: &[CppCompileCommand],
    definition_files: &HashMap<String, HashSet<&str>>,
    wrappers: &HashMap<String, Wrapper>,
    attachments: &Attachments,
) {
    for record in records {
        if record.align_bytes.is_some() || record.kind != CppRecordKind::Struct {
            continue;
        }
        let Some(file) = files_by_path.get(record.file.as_str()) else {
            continue;
        };
        let Some(Some((name, use_line))) =
            attachments.get(&(record.file.clone(), record.line, record.name.clone()))
        else {
            continue;
        };
        let wrapper = &wrappers[name];
        let operand = &wrapper.operand;
        let relevant = [
            name.as_str(),
            operand.as_str(),
            "__attribute__",
            "aligned",
            "typedef",
            "struct",
        ];
        if relevant[2..]
            .iter()
            .any(|name| definition_files.contains_key(*name))
            || command_override(commands, &relevant)
        {
            continue;
        }
        let mut visible = HashSet::from([file.path.clone()]);
        for line in file.source.lines().take(use_line.saturating_sub(1)) {
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
        if !visible.contains(&wrapper.file)
            || definition_files
                .get(operand)
                .is_some_and(|paths| paths.iter().any(|path| !visible.contains(*path)))
        {
            continue;
        }
        let mut state = State::new();
        process(
            file,
            Some(use_line.saturating_sub(1)),
            true,
            files_by_path,
            &mut state,
        );
        if state.get(name) != Some(&Value::Defined(None)) {
            continue;
        }
        let alignment = operand
            .parse::<usize>()
            .ok()
            .or_else(|| match state.get(operand) {
                Some(Value::Defined(value)) => *value,
                _ => None,
            });
        if let Some(alignment) = alignment.filter(|n| n.is_power_of_two()) {
            record.align_bytes = Some(alignment);
            record.is_cache_aligned = alignment >= record.cache_line_size;
            record.total_estimated_size = record.total_estimated_size.and_then(|size| {
                size.checked_add(alignment - 1)
                    .map(|size| size / alignment * alignment)
            });
        }
    }
}

fn command_override(commands: &[CppCompileCommand], names: &[&str]) -> bool {
    commands.iter().any(|command| {
        let mut arguments = command.arguments.iter();
        while let Some(arg) = arguments.next() {
            if arg.starts_with('@')
                || arg.starts_with("-include")
                || arg.starts_with("-imacros")
                || arg.starts_with("/FI")
            {
                return true;
            }
            let value = if matches!(arg.as_str(), "-D" | "-U" | "/D" | "/U") {
                let Some(value) = arguments.next() else {
                    return true;
                };
                Some(value.as_str())
            } else {
                ["-D", "-U", "/D", "/U"]
                    .iter()
                    .find_map(|prefix| arg.strip_prefix(prefix))
            };
            if value.is_some_and(|value| {
                names.contains(&value.split(['=', '(']).next().unwrap_or(value))
            }) {
                return true;
            }
        }
        false
    })
}

type Attachments = HashMap<(String, usize, String), Option<(String, usize)>>;

fn attached_wrappers(files: &[ParsedCppFile], wrappers: &HashMap<String, Wrapper>) -> Attachments {
    let mut result = Attachments::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "struct_specifier"
                || node.child_by_field_name("name").is_some()
                || !file.source[..node.start_byte()]
                    .trim_end()
                    .ends_with("typedef")
            {
                return;
            }
            let Some(body) = node.child_by_field_name("body") else {
                return;
            };
            let text = node_text(body, &file.source);
            if !text.starts_with('{') || !text.ends_with('}') || body.is_missing() {
                return;
            }
            let after = &file.source[body.end_byte()..];
            let Some(end) = after.find(';').filter(|end| *end <= 256) else {
                return;
            };
            let tail = &after[..end];
            let words = tail.split_whitespace().collect::<Vec<_>>();
            let [name, alias] = words.as_slice() else {
                return;
            };
            if !wrappers.contains_key(*name) {
                return;
            }
            let offset = body.end_byte() + tail.find(name).unwrap();
            let key = (
                file.path.clone(),
                node.start_position().row + 1,
                alias.to_string(),
            );
            let attachment = (
                name.to_string(),
                file.source[..offset]
                    .bytes()
                    .filter(|b| *b == b'\n')
                    .count()
                    + 1,
            );
            result
                .entry(key)
                .and_modify(|value| *value = None)
                .or_insert(Some(attachment));
        });
    }
    result
}
