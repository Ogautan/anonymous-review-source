//! Runtime-only source views. Layout/type recovery keeps the original source;
//! operand bytes hidden here never become a fabricated constant expression.
use crate::cpp_detection::parser::CodeChildren;

use std::borrow::Cow;
use std::collections::HashSet;
use std::ops::Range;
use tree_sitter::Node;

use super::parser::{ParsedCppFile, node_text, walk_nodes};
use super::types::CppCompileCommand;

pub(super) fn views<'a>(
    files: &'a [ParsedCppFile],
    commands: &[CppCompileCommand],
) -> Cow<'a, [ParsedCppFile]> {
    if !files.iter().any(|file| {
        !file.is_c && (file.source.contains("noexcept") || file.source.contains("requires"))
    }) {
        return Cow::Borrowed(files);
    }
    // A keyword macro changes the meaning before C++ parsing. Keep unknown
    // overrides rather than treating their argument as an unevaluated operand.
    if commands.iter().any(|command| {
        command.arguments.iter().enumerate().any(|(index, arg)| {
            let keyword = |value: &str| {
                let name = value.split(['=', '(']).next().unwrap_or("");
                matches!(name, "noexcept" | "requires") || name.contains('\\')
            };
            arg.starts_with('@')
                || arg.starts_with("-include")
                || arg.starts_with("-imacros")
                || arg.starts_with("/FI")
                || matches!(
                    arg.as_str(),
                    "-std=c++98" | "-std=gnu++98" | "-std=c++03" | "-std=gnu++03"
                )
                || ["-D", "-U", "/D", "/U"].iter().any(|prefix| {
                    arg.strip_prefix(prefix).is_some_and(|value| {
                        if value.is_empty() {
                            command
                                .arguments
                                .get(index + 1)
                                .is_some_and(|value| keyword(value))
                        } else {
                            keyword(value)
                        }
                    })
                })
        })
    }) {
        return Cow::Borrowed(files);
    }
    let mut macros = HashSet::new();
    for command in commands {
        for (index, argument) in command.arguments.iter().enumerate() {
            for prefix in ["-D", "-U", "/D", "/U"] {
                if let Some(value) = argument.strip_prefix(prefix) {
                    let value = if value.is_empty() {
                        command
                            .arguments
                            .get(index + 1)
                            .map(String::as_str)
                            .unwrap_or("")
                    } else {
                        value
                    };
                    if let Some(name) = value.split(['=', '(']).next() {
                        macros.insert(name.to_owned());
                    }
                }
            }
        }
    }
    let mut overridden = false;
    for file in files {
        if !file.source.contains("noexcept")
            && !file.source.contains("requires")
            && !file.source.contains('#')
        {
            continue;
        }
        if let Some(tree) = &file.tree {
            walk_nodes(tree.root_node(), &mut |node| {
                if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                    && let Some(name) = node.child_by_field_name("name")
                {
                    let name = node_text(name, &file.source);
                    overridden |= matches!(name, "noexcept" | "requires");
                    macros.insert(name.to_owned());
                }
                if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                    && node.child_by_field_name("name").is_some_and(|name| {
                        node_text(name, &file.source).contains('\\')
                            || file.source[name.end_byte()..].starts_with("\\\n")
                            || file.source[name.end_byte()..].starts_with("\\\r\n")
                    })
                {
                    // Universal-character names and identifier splicing are
                    // not normalized by this bounded macro lookup.
                    overridden = true;
                }
                if node.kind() == "preproc_call" {
                    let logical = node_text(node, &file.source)
                        .replace("\\\n", "")
                        .replace("\\\r\n", "");
                    if logical
                        .trim_start()
                        .strip_prefix('#')
                        .is_some_and(|directive| directive.trim_start().starts_with("define"))
                    {
                        overridden = true;
                    }
                }
                // C-compatible headers may declare an ordinary function with
                // this spelling. A C++-only keyword interpretation is unsafe.
                if node.kind() == "function_declarator"
                    && node.child_by_field_name("declarator").is_some_and(|name| {
                        matches!(node_text(name, &file.source), "noexcept" | "requires")
                    })
                {
                    overridden = true;
                }
            });
        }
    }
    if overridden {
        return Cow::Borrowed(files);
    }
    let mut changes = Vec::new();
    for (index, file) in files.iter().enumerate() {
        if file.is_c || (!file.source.contains("noexcept") && !file.source.contains("requires")) {
            continue;
        }
        let Some(tree) = &file.tree else { continue };
        let mut ranges = Vec::<Range<usize>>::new();
        walk_nodes(tree.root_node(), &mut |node| {
            // This grammar represents the expression operator as an ordinary
            // call. A declaration's exception specification is not this node.
            if !matches!(node.kind(), "call_expression" | "requires_expression") || node.has_error()
            {
                return;
            }
            let range = if node.kind() == "requires_expression" {
                // Requirement parameters and requirement bodies exist only
                // for constraint checking, not in a runtime invocation.
                let Some(keyword) = node
                    .code_child(0)
                    .filter(|token| token.kind() == "requires")
                else {
                    return;
                };
                keyword.end_byte()..node.end_byte()
            } else {
                let Some(function) = node.child_by_field_name("function") else {
                    return;
                };
                if function.kind() != "identifier"
                    || node_text(function, &file.source) != "noexcept"
                {
                    return;
                }
                let Some(arguments) = node.child_by_field_name("arguments") else {
                    return;
                };
                let operands = arguments
                    .named_code_children(&mut arguments.walk())
                    .filter(|node| node.kind() != "comment")
                    .collect::<Vec<_>>();
                if operands.len() != 1 {
                    return;
                }
                operands[0].byte_range()
            };
            // Macro expansion may paste a prefix onto the keyword, or inject
            // parentheses that escape the apparent unevaluated operand.
            if mentions_macro(node, &file.source, &macros) {
                return;
            }
            let mut parent = node.parent();
            while let Some(ancestor) = parent {
                if ancestor.kind() == "ERROR" {
                    return;
                }
                if ancestor.kind() == "call_expression"
                    && ancestor
                        .child_by_field_name("function")
                        .is_some_and(|callee| mentions_macro(callee, &file.source, &macros))
                {
                    return;
                }
                parent = ancestor.parent();
            }
            if file.source.as_bytes()[range.clone()]
                .iter()
                .any(|byte| !byte.is_ascii_whitespace())
            {
                ranges.push(range);
            }
        });
        if ranges.is_empty() {
            continue;
        }
        ranges.sort_unstable_by_key(|range| (range.start, range.end));
        let mut merged = Vec::<Range<usize>>::new();
        for range in ranges {
            if let Some(last) = merged.last_mut()
                && range.start <= last.end
            {
                last.end = last.end.max(range.end);
            } else {
                merged.push(range);
            }
        }
        changes.push((index, merged));
    }
    if changes.is_empty() {
        return Cow::Borrowed(files);
    }
    let mut result = files.to_vec();
    for (index, ranges) in changes {
        let file = &mut result[index];
        let mut bytes = file.source.as_bytes().to_vec();
        for range in ranges {
            for byte in &mut bytes[range] {
                if !matches!(*byte, b'\r' | b'\n') {
                    *byte = b' ';
                }
            }
        }
        file.source = String::from_utf8(bytes).expect("whole operands replaced with ASCII");
        // Retain the syntax shape and byte locations. No value/type is inferred
        // from a replacement expression, and text fallback sees the same mask.
    }
    Cow::Owned(result)
}

fn mentions_macro(node: Node<'_>, source: &str, macros: &HashSet<String>) -> bool {
    let mut found = false;
    walk_nodes(node, &mut |node| {
        if matches!(
            node.kind(),
            "identifier" | "field_identifier" | "type_identifier" | "namespace_identifier"
        ) {
            let name = node_text(node, source);
            found |= macros.contains(name) || name.contains('\\');
        }
    });
    found
}
