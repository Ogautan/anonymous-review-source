//! Exclude only closed, directly bound array accesses whose byte intervals
//! cannot share a block across elements. Unknown uses invalidate the proof.
use std::collections::{HashMap, HashSet};

use super::super::parser::{ParsedCppFile, node_text, walk_nodes};
use super::super::types::{CppRecordKind, CppStructInfo, IndexedWriteCandidate};

pub(super) fn isolated_arrays(
    files: &[ParsedCppFile],
    records: &[CppStructInfo],
    candidates: &[IndexedWriteCandidate],
    block: usize,
) -> HashSet<String> {
    let symbols = candidates
        .iter()
        .filter(|c| c.record_name.is_none() && c.alias_name.is_none())
        .filter_map(|c| c.field_name.as_deref())
        .collect::<HashSet<_>>();
    let mut declarations =
        HashMap::<&str, Vec<(&ParsedCppFile, tree_sitter::Node<'_>, &CppStructInfo)>>::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "declaration"
                || node.has_error()
                || node.parent().is_none_or(|p| p.kind() != "translation_unit")
            {
                return;
            }
            let Some(ty) = node.child_by_field_name("type") else {
                return;
            };
            let owners = records
                .iter()
                .filter(|r| {
                    r.name == node_text(ty, &file.source)
                        && r.file == file.path
                        && r.qualified_name == r.name
                })
                .collect::<Vec<_>>();
            let [record] = owners.as_slice() else { return };
            if record.total_estimated_size.is_none_or(|size| size < block)
                || record.kind != CppRecordKind::Struct
                || record.has_base_classes
                || record.has_no_unique_address
                || record.fields.iter().any(|f| {
                    f.estimated_size.is_none()
                        || record
                            .fields
                            .first()
                            .is_some_and(|first| first.visibility != f.visibility)
                        || f.is_indirect
                        || f.is_atomic
                        || !primitive_type(f.element_type.as_deref().unwrap_or(&f.ty_str))
                })
            {
                return;
            }
            let mut unsupported_layout = false;
            walk_nodes(tree.root_node(), &mut |definition| {
                if definition.kind() == "struct_specifier"
                    && definition.start_position().row + 1 == record.line
                {
                    walk_nodes(definition, &mut |part| {
                        unsupported_layout |= part.kind() == "bitfield_clause";
                    });
                }
            });
            if unsupported_layout {
                return;
            }
            let mut cursor = node.walk();
            for decl in node.children_by_field_name("declarator", &mut cursor) {
                if decl.kind() != "array_declarator" {
                    continue;
                }
                let Some(name) = decl.child_by_field_name("declarator") else {
                    continue;
                };
                if name.kind() == "identifier" && symbols.contains(node_text(name, &file.source)) {
                    declarations
                        .entry(node_text(name, &file.source))
                        .or_default()
                        .push((file, name, record));
                }
            }
        });
    }
    let mut isolated = HashSet::new();
    for (symbol, declarations) in declarations {
        let [(declaration_file, declaration, record)] = declarations.as_slice() else {
            continue;
        };
        let mut valid = true;
        let mut first = usize::MAX;
        let mut last = 0;
        for file in files {
            if !valid {
                break;
            }
            if !file.source.contains(symbol) {
                continue;
            }
            let lexical = super::identifier_tokens(&file.source)
                .filter(|token| *token == symbol)
                .count();
            if lexical == 0 {
                continue;
            }
            let Some(tree) = &file.tree else {
                valid = false;
                break;
            };
            if tree.root_node().has_error() {
                valid = false;
                break;
            }
            let mut recognized = 0;
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() != "identifier" || node_text(node, &file.source) != symbol {
                    return;
                }
                recognized += 1;
                if file.path == declaration_file.path && node == *declaration {
                    return;
                }
                let Some(subscript) = node.parent().filter(|p| {
                    p.kind() == "subscript_expression"
                        && p.child_by_field_name("argument") == Some(node)
                }) else {
                    valid = false;
                    return;
                };
                let Some(member) = subscript.parent().filter(|p| {
                    p.kind() == "field_expression"
                        && p.child_by_field_name("argument") == Some(subscript)
                }) else {
                    valid = false;
                    return;
                };
                let Some(field_name) = member.child_by_field_name("field") else {
                    valid = false;
                    return;
                };
                let Some((field_index, field)) = record
                    .fields
                    .iter()
                    .enumerate()
                    .find(|(_, f)| f.name == node_text(field_name, &file.source))
                else {
                    valid = false;
                    return;
                };
                if field.is_array
                    || field.is_indirect
                    || field.is_atomic
                    || !primitive_type(&field.ty_str)
                {
                    valid = false;
                    return;
                }
                let mut ancestor = member.parent();
                while let Some(parent) = ancestor {
                    if matches!(
                        parent.kind(),
                        "argument_list" | "pointer_expression" | "init_declarator"
                    ) {
                        valid = false;
                        return;
                    }
                    if parent.kind() == "function_definition" {
                        // Reference-returning wrappers need an alias contract.
                        if parent
                            .child_by_field_name("declarator")
                            .is_some_and(|d| node_text(d, &file.source).contains('&'))
                        {
                            valid = false;
                        }
                        break;
                    }
                    ancestor = parent.parent();
                }
                if field.estimated_size.is_none_or(|size| size == 0) {
                    valid = false;
                    return;
                }
                first = first.min(field_index);
                last = last.max(field_index);
            });
            // Macro replacements, comments and unsupported identifier forms
            // cannot silently disappear from a closed-use proof.
            if recognized != lexical {
                valid = false;
            }
        }
        // The trailing and leading unaccessed members separate adjacent
        // access envelopes. Alignment can only add bytes, so this bound also
        // holds under packing. Equal access control preserves member order.
        let minimum_distance = if first != usize::MAX {
            record.fields[..first]
                .iter()
                .chain(&record.fields[last + 1..])
                .try_fold(1usize, |sum, field| sum.checked_add(field.estimated_size?))
        } else {
            None
        };
        if valid && minimum_distance.is_some_and(|distance| distance >= block) {
            isolated.insert(symbol.to_owned());
        }
    }
    isolated
}

fn primitive_type(ty: &str) -> bool {
    !ty.trim().is_empty()
        && ty.split_whitespace().all(|t| {
            matches!(
                t,
                "bool"
                    | "char"
                    | "signed"
                    | "unsigned"
                    | "short"
                    | "int"
                    | "long"
                    | "float"
                    | "double"
                    | "const"
                    | "volatile"
            )
        })
}
