use crate::cpp_detection::parser::CodeChildren;
use std::collections::HashMap;
use std::path::Path;

use regex::Regex;
use tree_sitter::Node;

use crate::helpers::line_of_offset;
use crate::types::ItemVisibility;

use super::parser::{ParsedCppFile, node_text, walk_nodes};
use super::types::{CppFieldInfo, CppRecordKind, CppStructInfo};

pub fn collect_cpp_structs(
    files: &[ParsedCppFile],
    project_name: &str,
    cache_line_size: usize,
) -> Vec<CppStructInfo> {
    let mut structs = Vec::new();
    let alignment_wrappers = super::layout_macros::type_alignment_wrapper_names(files);

    for file in files {
        if let Some(tree) = &file.tree {
            let root = tree.root_node();
            walk_nodes(root, &mut |node| {
                if matches!(node.kind(), "struct_specifier" | "class_specifier")
                    && let Some(info) = analyze_record(node, file, project_name, cache_line_size)
                    && (!info.fields.is_empty() || !info.static_fields.is_empty())
                {
                    structs.push(info);
                }
            });
        }
        // Error recovery can leave a valid tree while omitting one malformed
        // record altogether (notably C11 `_Atomic(pointer-type)` parsed by the
        // C++ grammar, attribute-heavy C, and macro-decorated declarations).
        // Run the conservative record scanner as a complementary frontend and
        // retain only declarations the syntax tree did not already recover.
        for fallback in
            collect_records_fallback(file, project_name, cache_line_size, &alignment_wrappers)
        {
            if let Some(record) = structs
                .iter_mut()
                .find(|record| record.file == fallback.file && record.name == fallback.name)
            {
                // C11 recovery may retain only the ordinary array between
                // `_Atomic(T)` fields. A nonempty partial tree must not erase
                // those fields (or the array) from the source layout.
                if file.source.contains("_Atomic(")
                    && file
                        .tree
                        .as_ref()
                        .is_some_and(|tree| tree.root_node().has_error())
                    && fallback.fields.len() > record.fields.len()
                    && record
                        .fields
                        .iter()
                        .all(|field| fallback.fields.iter().any(|other| other.name == field.name))
                {
                    let mut recovered = fallback.fields;
                    for field in &mut recovered {
                        if let Some(parsed) = record
                            .fields
                            .iter()
                            .find(|parsed| parsed.name == field.name)
                        {
                            *field = parsed.clone();
                        }
                    }
                    record.fields = recovered;
                    record.ordered_own_fields = false;
                    record.public_fields = record
                        .fields
                        .iter()
                        .filter(|f| f.visibility.is_exposed())
                        .map(|f| f.name.clone())
                        .collect();
                    recompute(record, cache_line_size);
                }
            } else {
                structs.push(fallback);
            }
        }
    }

    let mut aliases = record_scoped_aliases(files);
    aliases.extend(super::type_bindings::record_aliases(files));
    enrich_with_local_types(&mut structs, cache_line_size, &aliases);
    structs
}

fn analyze_record(
    node: Node<'_>,
    file: &ParsedCppFile,
    project_name: &str,
    cache_line_size: usize,
) -> Option<CppStructInfo> {
    let declaration_node = node
        .parent()
        .filter(|parent| matches!(parent.kind(), "type_definition" | "declaration"));
    let declaration_text = declaration_node
        .map(|parent| node_text(parent, &file.source))
        .unwrap_or_else(|| node_text(node, &file.source));
    let name = node
        .child_by_field_name("name")
        .map(|child| clean_type_name(node_text(child, &file.source)))
        .filter(|candidate| !is_record_annotation_macro(candidate, &file.source))
        .or_else(|| anonymous_record_alias(declaration_text, &file.source))
        .or_else(|| record_name_after_alignment(declaration_text, &file.source))?;
    if name.is_empty() {
        return None;
    }

    let kind = if node.kind() == "class_specifier" {
        CppRecordKind::Class
    } else {
        CppRecordKind::Struct
    };
    let default_visibility = if kind == CppRecordKind::Class {
        ItemVisibility::Private
    } else {
        ItemVisibility::Public
    };
    let (qualified_name, externally_reachable) = record_identity(node, &name, file);
    let text = node_text(node, &file.source);
    // Record attributes are outside the member body. An aligned local or
    // static member in that body cannot supply the instance's alignment.
    let record_header = node_text(node, &file.source)
        .split('{')
        .next()
        .unwrap_or("");
    let align_bytes = extract_align_bytes(record_header);
    let is_cache_aligned = align_bytes
        .map(|bytes| bytes >= cache_line_size)
        .unwrap_or(false)
        || has_explicit_cache_alignment(record_header, cache_line_size);
    let is_packed = text.contains("__attribute__((packed")
        || text.contains("[[gnu::packed]]")
        || surrounding_has_pack(&file.source, node.start_byte());
    let has_no_unique_address = text.contains("[[no_unique_address]]");
    let has_base_classes = node
        .code_children(&mut node.walk())
        .any(|child| child.kind() == "base_class_clause");

    let body = node.child_by_field_name("body")?;
    let mut fields = Vec::new();
    let mut public_methods = Vec::new();
    let mut current_visibility = default_visibility;
    let mut cursor = body.walk();
    for child in body.code_children(&mut cursor) {
        match child.kind() {
            "access_specifier" => {
                current_visibility = parse_access_specifier(node_text(child, &file.source));
            }
            "field_declaration" => {
                let field_text = node_text(child, &file.source);
                if field_declaration_is_method(child, &file.source) {
                    if current_visibility.is_exposed()
                        && let Some(method) = extract_method_name(field_text)
                    {
                        public_methods.push(method);
                    }
                    continue;
                }
                fields.extend(parse_field_declaration(
                    child,
                    file,
                    current_visibility,
                    cache_line_size,
                ));
            }
            "declaration" => {
                let field_text = node_text(child, &file.source);
                if is_method_declaration(field_text)
                    && current_visibility.is_exposed()
                    && let Some(method) = extract_method_name(field_text)
                {
                    public_methods.push(method);
                }
            }
            "function_definition" => {
                if current_visibility.is_exposed()
                    && let Some(method) = extract_method_name(node_text(child, &file.source))
                {
                    public_methods.push(method);
                }
            }
            _ => {}
        }
    }
    // The C++ grammar used by tree-sitter deliberately does not model C11's
    // `_Atomic(T)` type specifier.  In mixed C/C++ projects it can therefore
    // recover the whole record body as one ERROR node.  Preserve the record
    // and feed semicolon-delimited declarations through the conservative
    // declaration parser when the syntax frontend produced no fields.
    if fields.is_empty() && body.has_error() {
        let body_text = node_text(body, &file.source);
        for statement in body_text
            .trim_start_matches('{')
            .trim_end_matches('}')
            .split(';')
            .map(str::trim)
            .filter(|statement| !statement.is_empty())
        {
            let declaration = format!("{statement};");
            fields.extend(parse_field_declaration_fallback(
                &declaration,
                file,
                body.start_byte(),
                current_visibility,
                cache_line_size,
            ));
        }
    }

    mark_bitfield_groups(body, &file.source, &mut fields);
    let static_fields = fields
        .iter()
        .filter(|field| field.is_static)
        .cloned()
        .collect::<Vec<_>>();
    fields.retain(|field| !field.is_static);
    let align_bytes = align_bytes.max(fields.iter().filter_map(|field| field.align_bytes).max());
    let is_cache_aligned =
        is_cache_aligned || align_bytes.is_some_and(|alignment| alignment >= cache_line_size);
    let ordered_own_fields = ordered_own_field_declarations(body, &file.source, &fields);
    let public_fields = fields
        .iter()
        .filter(|field| field.visibility.is_exposed())
        .map(|field| field.name.clone())
        .collect();
    let atomic_fields = fields
        .iter()
        .filter(|field| field.is_atomic && !field.is_cache_padded)
        .map(|field| field.name.clone())
        .collect();
    let hot_scalar_fields = fields
        .iter()
        .filter(|field| field.is_hot_scalar && !field.is_cache_padded)
        .map(|field| field.name.clone())
        .collect();
    let hot_sync_fields = fields
        .iter()
        .filter(|field| field.is_hot_sync && !field.is_cache_padded)
        .map(|field| field.name.clone())
        .collect();
    let has_cache_padding = fields
        .iter()
        .any(|field| field.is_cache_padded || field.is_manual_padding)
        || is_cache_aligned
        || declaration_has_manual_cache_padding(text, cache_line_size);
    let total_estimated_size = total_size(&fields, cache_line_size, align_bytes);
    let cache_line_groups = compute_cache_line_groups(&fields, cache_line_size);
    let cache_line_groups_precise = false;

    Some(CppStructInfo {
        name,
        qualified_name,
        kind,
        file: file.path.clone(),
        line: line_of_offset(&file.source, node.start_byte()),
        project_name: project_name.to_string(),
        cache_line_size,
        fields,
        static_fields,
        align_bytes,
        is_cache_aligned,
        is_packed,
        has_cache_padding,
        has_base_classes,
        has_no_unique_address,
        ordered_own_fields,
        visibility: if externally_reachable {
            ItemVisibility::Public
        } else {
            ItemVisibility::Private
        },
        public_fields,
        public_methods,
        atomic_fields,
        hot_scalar_fields,
        hot_sync_fields,
        total_estimated_size,
        cache_line_groups,
        cache_line_groups_precise,
        compiler_layout_exact: false,
    })
}

fn ordered_own_field_declarations(body: Node<'_>, source: &str, fields: &[CppFieldInfo]) -> bool {
    if fields.is_empty()
        || fields.iter().any(|field| {
            field.visibility != fields[0].visibility
                || field.bitfield_group.is_some()
                || outer_type_spelling(&field.ty_str).contains('&')
        })
    {
        return false;
    }
    let mut declared = Vec::new();
    for member in body.named_code_children(&mut body.walk()) {
        match member.kind() {
            "comment"
            | "access_specifier"
            | "function_definition"
            | "alias_declaration"
            | "type_definition"
            | "friend_declaration"
            | "static_assert_declaration" => {}
            "field_declaration" if field_declaration_is_method(member, source) => {}
            "declaration"
                if !member.has_error()
                    && member
                        .child_by_field_name("declarator")
                        .is_some_and(|decl| decl.kind() == "function_declarator") => {}
            "field_declaration" => {
                if member.has_error() {
                    return false;
                }
                let mut unsupported = false;
                walk_nodes(member, &mut |node| {
                    unsupported |= matches!(
                        node.kind(),
                        "bitfield_clause"
                            | "union_specifier"
                            | "attribute_specifier"
                            | "attribute_declaration"
                            | "attribute"
                    );
                });
                if unsupported {
                    return false;
                }
                let text = node_text(member, source);
                if text.split_whitespace().any(|word| word == "static") {
                    continue;
                }
                // Pair the original declarations with the collected fields;
                // skipped/recovered/conditional members cannot supply order.
                for declarator in member.children_by_field_name("declarator", &mut member.walk()) {
                    let mut name = declarator;
                    while let Some(inner) = name.child_by_field_name("declarator") {
                        name = inner;
                    }
                    if !matches!(name.kind(), "field_identifier" | "identifier") {
                        return false;
                    }
                    declared.push(node_text(name, source));
                }
            }
            // In particular do not combine alternative #if field sequences,
            // injected anonymous records, using declarations, or recovery.
            _ => return false,
        }
    }
    declared
        == fields
            .iter()
            .map(|field| field.name.as_str())
            .collect::<Vec<_>>()
}

fn parse_field_declaration(
    node: Node<'_>,
    file: &ParsedCppFile,
    visibility: ItemVisibility,
    cache_line_size: usize,
) -> Vec<CppFieldInfo> {
    let field_text = node_text(node, &file.source);
    if field_text.contains("typedef ") || field_text.contains("using ") {
        return Vec::new();
    }

    let type_node = node.child_by_field_name("type");
    let ty_str = type_node
        .map(|child| normalize_space(node_text(child, &file.source)))
        .unwrap_or_else(|| infer_field_type_text(field_text));

    let mut declarators = Vec::new();
    let mut cursor = node.walk();
    for child in node.children_by_field_name("declarator", &mut cursor) {
        declarators.push(child);
    }

    if declarators.is_empty() {
        // A named nested type (including a forward declaration) declares a
        // type, not an instance in the enclosing record. Do not let textual
        // recovery turn its tag or enumerators into data members. A definition
        // followed by an actual declarator still takes the normal path below.
        if type_node.is_some_and(|ty| {
            matches!(
                ty.kind(),
                "struct_specifier" | "class_specifier" | "union_specifier" | "enum_specifier"
            ) && ty.child_by_field_name("name").is_some()
        }) {
            return Vec::new();
        }
        return parse_field_declaration_fallback(
            field_text,
            file,
            node.start_byte(),
            visibility,
            cache_line_size,
        );
    }

    let mut fields = Vec::new();
    for declarator in declarators {
        let declarator_text = node_text(declarator, &file.source);
        // Unexpanded thread-safety attributes are sometimes parsed as a
        // function declarator, with the real member name in a preceding ERROR.
        // Recover only that single identifier, never annotation arguments.
        let annotation_member = if declarator.kind() == "function_declarator"
            && declarator
                .child_by_field_name("declarator")
                .is_some_and(|name| {
                    let name = node_text(name, &file.source);
                    name == "guarded_by" || name.ends_with("GUARDED_BY")
                }) {
            node.code_children(&mut node.walk())
                .filter(|child| {
                    child.kind() == "ERROR" && child.end_byte() <= declarator.start_byte()
                })
                .filter_map(|child| {
                    let text = node_text(child, &file.source).trim();
                    let mut words = identifier_words(text);
                    let name = words.next()?;
                    (name == text && words.next().is_none()).then(|| name.to_string())
                })
                .last()
        } else {
            None
        };
        let Some(name) = annotation_member
            .or_else(|| extract_declarator_name(declarator, &file.source))
            .or_else(|| extract_name_from_declarator_text(declarator_text))
        else {
            continue;
        };
        // A field may legally have the same spelling as its type (`Board
        // Board {};`). Tree-sitter supplies a real declarator for that case;
        // named nested type declarations have already been rejected above.
        if name.is_empty() {
            continue;
        }

        let is_array = declarator.kind() == "array_declarator" || declarator_text.contains('[');
        let array_len = extract_array_len(declarator_text);
        let element_type = is_array.then(|| ty_str.clone());
        let full_type =
            if is_array || declarator_text.contains('*') || declarator_text.contains('&') {
                format!("{ty_str} {declarator_text}")
            } else {
                ty_str.clone()
            };
        fields.push(make_field(
            name,
            full_type,
            field_text,
            line_of_offset(&file.source, declarator.start_byte()),
            visibility,
            is_array,
            array_len,
            element_type,
            cache_line_size,
            field_declaration_alignment(node, declarator, &file.source),
            field_declaration_qualifiers(node, &file.source),
        ));
    }

    fields
}

#[derive(Clone, Copy, Default)]
struct FieldQualifiers {
    is_static: bool,
    is_read_only: bool,
}

fn field_declaration_qualifiers(declaration: Node<'_>, source: &str) -> FieldQualifiers {
    let mut qualifiers = FieldQualifiers::default();
    for child in declaration.named_code_children(&mut declaration.walk()) {
        if matches!(child.kind(), "storage_class_specifier" | "type_qualifier") {
            match node_text(child, source).trim() {
                "static" => qualifiers.is_static = true,
                "const" | "constexpr" | "consteval" => qualifiers.is_read_only = true,
                _ => {}
            }
        }
    }
    qualifiers
}

fn field_declaration_alignment(
    declaration: Node<'_>,
    declarator: Node<'_>,
    source: &str,
) -> Option<usize> {
    let declarators: Vec<_> = declaration
        .children_by_field_name("declarator", &mut declaration.walk())
        .collect();
    let mut alignment = None;
    for child in declaration.named_code_children(&mut declaration.walk()) {
        if !matches!(
            child.kind(),
            "type_qualifier"
                | "attribute_specifier"
                | "attribute_declaration"
                | "ms_declspec_modifier"
        ) {
            continue;
        }
        // Prefix attributes apply to the declaration. A trailing GNU attribute
        // belongs to the preceding declarator, not to every sibling field.
        let preceding = declarators
            .iter()
            .filter(|decl| decl.start_byte() < child.start_byte())
            .max_by_key(|decl| decl.start_byte());
        if preceding.is_none_or(|decl| *decl == declarator) {
            alignment = alignment.max(extract_align_bytes(node_text(child, source)));
        }
    }
    // Some declarator forms retain their own attributes. Never descend into
    // an initializer, lambda body, array expression, or parameter declaration.
    let mut pending = vec![declarator];
    while let Some(node) = pending.pop() {
        if matches!(
            node.kind(),
            "attribute_specifier" | "attribute_declaration" | "ms_declspec_modifier"
        ) {
            alignment = alignment.max(extract_align_bytes(node_text(node, source)));
        } else if matches!(
            node.kind(),
            "identifier"
                | "field_identifier"
                | "pointer_declarator"
                | "reference_declarator"
                | "array_declarator"
                | "parenthesized_declarator"
                | "attributed_declarator"
        ) {
            pending.extend(node.named_code_children(&mut node.walk()).filter(|child| {
                Some(*child) == node.child_by_field_name("declarator")
                    || matches!(
                        child.kind(),
                        "attribute_specifier" | "attribute_declaration" | "ms_declspec_modifier"
                    )
            }));
        }
    }
    alignment
}

fn mark_bitfield_groups(body: Node<'_>, source: &str, fields: &mut [CppFieldInfo]) {
    let mut group = 0usize;
    for declaration in body.named_code_children(&mut body.walk()) {
        if declaration.kind() == "comment" {
            continue;
        }
        if declaration.kind().starts_with("preproc_")
            && nonzero_bitfield_branches(declaration, source)
        {
            // Endianness/configuration can reorder a sequence without
            // splitting its memory location. Join only if every syntactic
            // branch contains exclusively nonzero-width bit-fields.
            walk_nodes(declaration, &mut |node| {
                if node.kind() == "field_identifier"
                    && let Some(field) = fields
                        .iter_mut()
                        .find(|f| f.name == node_text(node, source))
                {
                    field.bitfield_group = Some(group);
                }
            });
            continue;
        }
        if declaration.kind() != "field_declaration" || declaration.has_error() {
            group += 1;
            continue;
        }
        let mut name = None;
        let mut bitfield = false;
        for child in declaration.named_code_children(&mut declaration.walk()) {
            if child.kind() == "field_identifier" {
                if name.is_some() {
                    group += 1;
                }
                name = Some(node_text(child, source));
            } else if child.kind() == "bitfield_clause" {
                bitfield = true;
                let width = node_text(child, source)
                    .trim()
                    .trim_start_matches(':')
                    .trim();
                // Unknown constant expressions may be zero. They terminate
                // our proof; never join fields across an unresolved width.
                if width.parse::<u64>().is_ok_and(|width| width > 0) {
                    if let Some(name) = name.take()
                        && let Some(field) = fields.iter_mut().find(|field| field.name == name)
                    {
                        field.bitfield_group = Some(group);
                    }
                } else {
                    name = None;
                    group += 1;
                }
            }
        }
        if !bitfield || name.is_some() {
            group += 1;
        }
    }
}

fn nonzero_bitfield_branches(node: Node<'_>, source: &str) -> bool {
    if node.has_error() {
        return false;
    }
    if node.kind() == "comment" {
        return true;
    }
    if node.kind() == "field_declaration" {
        let mut pending = false;
        let mut widths = 0;
        for child in node.named_code_children(&mut node.walk()) {
            match child.kind() {
                "field_identifier" => {
                    if pending {
                        return false;
                    }
                    pending = true;
                }
                "bitfield_clause" => {
                    let width = node_text(child, source)
                        .trim()
                        .trim_start_matches(':')
                        .trim();
                    if !width.parse::<u64>().is_ok_and(|n| n > 0) {
                        return false;
                    }
                    pending = false;
                    widths += 1;
                }
                "primitive_type" | "sized_type_specifier" | "type_identifier" | "comment" => {}
                _ => return false,
            }
        }
        return widths > 0 && !pending;
    }
    if !matches!(
        node.kind(),
        "preproc_if" | "preproc_ifdef" | "preproc_elif" | "preproc_else"
    ) {
        return false;
    }
    node.named_code_children(&mut node.walk()).all(|child| {
        Some(child) == node.child_by_field_name("condition")
            || Some(child) == node.child_by_field_name("name")
            || nonzero_bitfield_branches(child, source)
    })
}

fn parse_field_declaration_fallback(
    field_text: &str,
    file: &ParsedCppFile,
    start_byte: usize,
    visibility: ItemVisibility,
    cache_line_size: usize,
) -> Vec<CppFieldInfo> {
    let mut text = field_text.trim().trim_end_matches(';').trim().to_string();
    text = text
        .replace("mutable ", "")
        .replace("static ", "")
        .replace("const ", "");
    if identifier_words(&text).next().is_some_and(|word| {
        matches!(
            word,
            "using" | "typedef" | "friend" | "static_assert" | "template"
        )
    }) {
        return Vec::new();
    }
    if text.split('[').next().unwrap_or(&text).contains('(')
        && !text.trim_start().starts_with("_Atomic(")
    {
        return Vec::new();
    }

    let mut fields = Vec::new();
    let parts: Vec<&str> = text.split(',').collect();
    if parts.is_empty() {
        return fields;
    }

    let first = parts[0]
        .split('=')
        .next()
        .unwrap_or(parts[0])
        .split('{')
        .next()
        .unwrap_or(parts[0])
        .trim();
    let Some((ty, first_decl)) = split_type_and_declarator(first) else {
        return fields;
    };
    for (idx, part) in parts.iter().enumerate() {
        let decl = if idx == 0 { first_decl } else { part.trim() };
        let decl = decl
            .split('=')
            .next()
            .unwrap_or(decl)
            .split('{')
            .next()
            .unwrap_or(decl)
            .trim();
        let Some(name) = extract_name_from_declarator_text(decl) else {
            continue;
        };
        let is_array = decl.contains('[');
        let array_len = extract_array_len(decl);
        fields.push(make_field(
            name,
            if is_array {
                format!("{ty} {decl}")
            } else {
                ty.to_string()
            },
            field_text,
            line_of_offset(&file.source, start_byte),
            visibility,
            is_array,
            array_len,
            is_array.then(|| ty.to_string()),
            cache_line_size,
            extract_align_bytes(field_text.split(['=', '{']).next().unwrap_or("")),
            {
                // Initializer text cannot change a member's storage duration.
                let prefix = field_text.split(['=', '{', '[']).next().unwrap_or("");
                let tokens = super::parser::source_text::code_tokens(prefix);
                FieldQualifiers {
                    is_static: tokens.contains(&"static"),
                    is_read_only: tokens
                        .iter()
                        .any(|token| matches!(*token, "const" | "constexpr" | "consteval")),
                }
            },
        ));
    }

    fields
}

#[allow(clippy::too_many_arguments)]
fn make_field(
    name: String,
    ty_str: String,
    declaration_text: &str,
    line: usize,
    visibility: ItemVisibility,
    is_array: bool,
    array_len: Option<usize>,
    element_type: Option<String>,
    cache_line_size: usize,
    align_bytes: Option<usize>,
    qualifiers: FieldQualifiers,
) -> CppFieldInfo {
    let FieldQualifiers {
        is_static,
        is_read_only,
    } = qualifiers;
    let is_atomic = !is_read_only && is_cpp_atomic_type(&ty_str);
    let is_hot_scalar = !is_read_only && is_hot_scalar_field(&name, &ty_str);
    let is_hot_sync = !is_read_only && is_cpp_hot_sync_type(&ty_str);
    let is_indirect = is_indirection_type(&ty_str);
    // Member names and initializers cannot supply size, alignment, or storage
    // qualifiers. Keep nominal type size separate from recovered attributes.
    let estimated_size = estimate_cpp_type_size(&ty_str, is_array, array_len, cache_line_size);
    // Aligning a member's start does not isolate it from following members.
    // Only a padded inline type may supply this guarantee during enrichment.
    let is_cache_padded = false;
    let is_manual_padding = is_manual_padding_field(&name, &ty_str)
        && (estimated_size.is_some_and(|size| size >= cache_line_size)
            || bracketed_expression_mentions_cache_line(declaration_text, cache_line_size));

    CppFieldInfo {
        name,
        bitfield_group: None,
        ty_str,
        line,
        estimated_size,
        align_bytes,
        offset: None,
        is_atomic,
        is_hot_scalar,
        is_hot_sync,
        is_cache_padded,
        is_manual_padding,
        is_indirect,
        is_array,
        is_static,
        array_len,
        element_type,
        guarded_by: extract_guarded_by(declaration_text),
        visibility,
    }
}

fn extract_guarded_by(declaration_text: &str) -> Option<String> {
    for marker in ["GUARDED_BY(", "PT_GUARDED_BY(", "guarded_by("] {
        let Some(start) = declaration_text
            .find(marker)
            .map(|offset| offset + marker.len())
        else {
            continue;
        };
        let Some(end) = declaration_text[start..]
            .find(')')
            .map(|offset| offset + start)
        else {
            continue;
        };
        let guard = declaration_text[start..end].trim();
        if !guard.is_empty() {
            return Some(guard.to_string());
        }
    }
    None
}

fn collect_records_fallback(
    file: &ParsedCppFile,
    project_name: &str,
    cache_line_size: usize,
    alignment_wrappers: &std::collections::HashSet<String>,
) -> Vec<CppStructInfo> {
    let Ok(record_re) = Regex::new(
        r"(?ms)^[ \t]*(?:typedef[ \t]+)?(struct|class)(?:[ \t]+([A-Za-z_][A-Za-z0-9_:]*))?[^;{]*\{",
    ) else {
        return Vec::new();
    };
    let alias_re = Regex::new(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*;").ok();
    let mut records = Vec::new();
    for caps in record_re.captures_iter(&file.source) {
        let Some(header) = caps.get(0) else {
            continue;
        };
        if header.as_str().contains('(') {
            continue;
        }
        let open_brace = header.end().saturating_sub(1);
        let Some(close_brace) = matching_record_brace(&file.source, open_brace) else {
            continue;
        };
        let kind = if caps.get(1).is_some_and(|m| m.as_str() == "class") {
            CppRecordKind::Class
        } else {
            CppRecordKind::Struct
        };
        let default_visibility = if kind == CppRecordKind::Class {
            ItemVisibility::Private
        } else {
            ItemVisibility::Public
        };
        let derived_name = record_name_after_alignment(header.as_str(), &file.source);
        let source_name = derived_name.as_ref().and_then(|name| {
            header
                .as_str()
                .rfind(name)
                .map(|offset| (name.clone(), header.start() + offset))
        });
        let suffix = &file.source[close_brace + 1..];
        let alias_name = alias_re
            .as_ref()
            .and_then(|regex| regex.captures(suffix))
            .and_then(|captures| {
                captures.get(1).map(|name| {
                    (
                        clean_type_name(name.as_str()),
                        close_brace + 1 + name.start(),
                    )
                })
            })
            .or_else(|| {
                // The C++ grammar can recover `} ATTRIBUTE Alias;` differently
                // depending on spelling. Recover the typedef identity only for
                // source-defined type-attribute wrappers; alignment itself is
                // still resolved separately with visibility/build checks.
                if !header.as_str().trim_start().starts_with("typedef ") {
                    return None;
                }
                let end = suffix.find(';').filter(|end| *end <= 256)?;
                let words = suffix[..end].split_whitespace().collect::<Vec<_>>();
                let [annotation, alias] = words.as_slice() else {
                    return None;
                };
                if !alignment_wrappers.contains(*annotation) {
                    return None;
                }
                Some((alias.to_string(), header.start()))
            });
        let Some((name, name_offset)) = source_name.or(alias_name) else {
            continue;
        };
        let body_start = open_brace + 1;
        let body_text = &file.source[body_start..close_brace];
        let mut fields = Vec::new();
        let mut current_visibility = default_visibility;
        for (relative_offset, statement) in fallback_body_statements(body_text) {
            let mut cleaned = statement
                .lines()
                .filter(|line| {
                    let line = line.trim_start();
                    !line.starts_with('#')
                        && !line.starts_with("//")
                        && !line.starts_with("/*")
                        && !line.starts_with('*')
                        && !line.starts_with("*/")
                })
                .collect::<Vec<_>>()
                .join(" ");
            cleaned = cleaned.trim().trim_end_matches(';').trim().to_string();
            for (label, visibility) in [
                ("public:", ItemVisibility::Public),
                ("private:", ItemVisibility::Private),
                ("protected:", ItemVisibility::Restricted),
            ] {
                if let Some(rest) = cleaned.strip_prefix(label) {
                    current_visibility = visibility;
                    cleaned = rest.trim().to_string();
                    break;
                }
            }
            if cleaned == "public:" {
                current_visibility = ItemVisibility::Public;
                continue;
            }
            if cleaned == "private:" {
                current_visibility = ItemVisibility::Private;
                continue;
            }
            if cleaned == "protected:" {
                current_visibility = ItemVisibility::Restricted;
                continue;
            }
            let nested_type = cleaned.split('{').next().is_some_and(|header| {
                identifier_words(header)
                    .any(|word| matches!(word, "class" | "struct" | "union" | "enum"))
            });
            if !cleaned.is_empty() && !nested_type {
                let declaration = format!("{cleaned};");
                fields.extend(parse_field_declaration_fallback(
                    &declaration,
                    file,
                    body_start + relative_offset,
                    current_visibility,
                    cache_line_size,
                ));
            }
        }
        if fields.is_empty() {
            continue;
        }
        let static_fields = fields
            .iter()
            .filter(|field| field.is_static)
            .cloned()
            .collect::<Vec<_>>();
        fields.retain(|field| !field.is_static);
        if fields.is_empty() && static_fields.is_empty() {
            continue;
        }
        let text = &file.source[header.start()..=close_brace];
        let public_fields = fields
            .iter()
            .filter(|field| field.visibility.is_exposed())
            .map(|field| field.name.clone())
            .collect();
        let atomic_fields = fields
            .iter()
            .filter(|field| field.is_atomic && !field.is_cache_padded)
            .map(|field| field.name.clone())
            .collect();
        let hot_scalar_fields = fields
            .iter()
            .filter(|field| field.is_hot_scalar && !field.is_cache_padded)
            .map(|field| field.name.clone())
            .collect();
        let hot_sync_fields = fields
            .iter()
            .filter(|field| field.is_hot_sync && !field.is_cache_padded)
            .map(|field| field.name.clone())
            .collect();
        let align_bytes = extract_align_bytes(header.as_str())
            .max(fields.iter().filter_map(|field| field.align_bytes).max());
        let total_estimated_size = total_size(&fields, cache_line_size, align_bytes);
        let cache_line_groups = compute_cache_line_groups(&fields, cache_line_size);

        records.push(CppStructInfo {
            name: name.clone(),
            qualified_name: name,
            kind,
            file: file.path.clone(),
            line: line_of_offset(&file.source, name_offset),
            project_name: project_name.to_string(),
            cache_line_size,
            fields: fields.clone(),
            static_fields,
            align_bytes,
            is_cache_aligned: align_bytes.is_some_and(|alignment| alignment >= cache_line_size),
            is_packed: text.contains("packed") || surrounding_has_pack(&file.source, name_offset),
            has_cache_padding: fields
                .iter()
                .any(|field| field.is_cache_padded || field.is_manual_padding),
            // Access labels, bit-fields and qualified names in the body are
            // not base clauses. Only a standalone colon in the record head
            // can introduce inheritance (a scope separator is not one).
            has_base_classes: header.as_str().as_bytes().iter().enumerate().any(|(i, b)| {
                *b == b':'
                    && i.checked_sub(1)
                        .is_none_or(|j| header.as_str().as_bytes()[j] != b':')
                    && header.as_str().as_bytes().get(i + 1) != Some(&b':')
            }),
            has_no_unique_address: text.contains("[[no_unique_address]]"),
            ordered_own_fields: false,
            visibility: ItemVisibility::Public,
            public_fields,
            public_methods: Vec::new(),
            atomic_fields,
            hot_scalar_fields,
            hot_sync_fields,
            total_estimated_size,
            cache_line_groups,
            cache_line_groups_precise: false,
            compiler_layout_exact: false,
        });
    }
    records
}

fn matching_record_brace(source: &str, open_brace: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    if bytes.get(open_brace) != Some(&b'{') {
        return None;
    }
    let mut depth = 0usize;
    let mut index = open_brace;
    let mut quote = None;
    while index < bytes.len() {
        let byte = bytes[index];
        if let Some(delimiter) = quote {
            if byte == b'\\' {
                index = index.saturating_add(2);
                continue;
            }
            if byte == delimiter {
                quote = None;
            }
            index += 1;
            continue;
        }
        if matches!(byte, b'\'' | b'"') {
            quote = Some(byte);
            index += 1;
            continue;
        }
        if byte == b'/' && bytes.get(index + 1) == Some(&b'/') {
            index += 2;
            while index < bytes.len() && bytes[index] != b'\n' {
                index += 1;
            }
            continue;
        }
        if byte == b'/' && bytes.get(index + 1) == Some(&b'*') {
            index += 2;
            while index + 1 < bytes.len() && !(bytes[index] == b'*' && bytes[index + 1] == b'/') {
                index += 1;
            }
            index = (index + 2).min(bytes.len());
            continue;
        }
        match byte {
            b'{' => depth += 1,
            b'}' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(index);
                }
            }
            _ => {}
        }
        index += 1;
    }
    None
}

fn fallback_body_statements(body: &str) -> Vec<(usize, &str)> {
    let bytes = body.as_bytes();
    let mut statements = Vec::new();
    let mut start = 0usize;
    let mut depth = 0usize;
    let mut index = 0usize;
    while index < bytes.len() {
        match bytes[index] {
            b'{' => depth += 1,
            b'}' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    let prefix = body[start..index].split('{').next().unwrap_or("");
                    let mut next = index + 1;
                    while next < bytes.len() && bytes[next].is_ascii_whitespace() {
                        next += 1;
                    }
                    if bytes.get(next) != Some(&b';')
                        && prefix.contains('(')
                        && !prefix.contains('=')
                    {
                        start = index + 1;
                    }
                }
            }
            b';' if depth == 0 => {
                statements.push((start, &body[start..=index]));
                start = index + 1;
            }
            _ => {}
        }
        index += 1;
    }
    statements
}

/// Recover a stable C++ record identity and conservatively determine whether
/// the declaration is reachable outside its translation unit. Anonymous
/// namespaces and function-local records are intentionally treated as private.
fn record_identity(node: Node<'_>, name: &str, file: &ParsedCppFile) -> (String, bool) {
    let mut scopes = Vec::new();
    // A record defined only in a .c/.cc/.cpp translation unit is not an open
    // API merely because it is at namespace scope.  Header declarations remain
    // externally reachable unless an anonymous/function-local scope says
    // otherwise.
    let mut externally_reachable = Path::new(&file.path)
        .extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| matches!(extension, "h" | "hh" | "hpp" | "hxx" | "ipp" | "inl"));
    let mut ancestor = node.parent();

    while let Some(current) = ancestor {
        match current.kind() {
            "namespace_definition" => {
                let namespace = current
                    .child_by_field_name("name")
                    // C++17 nested namespace syntax denotes every component;
                    // clean_type_name would erase a:: from namespace a::b.
                    .map(|child| {
                        node_text(child, &file.source)
                            .split_whitespace()
                            .collect::<String>()
                    })
                    .filter(|value| !value.is_empty());
                if let Some(namespace) = namespace {
                    scopes.push(namespace);
                } else {
                    externally_reachable = false;
                }
            }
            "struct_specifier" | "class_specifier" => {
                if let Some(parent_name) = current
                    .child_by_field_name("name")
                    .map(|child| clean_type_name(node_text(child, &file.source)))
                    .filter(|value| !value.is_empty())
                {
                    scopes.push(parent_name);
                }
            }
            "function_definition" | "lambda_expression" => {
                externally_reachable = false;
            }
            _ => {}
        }
        ancestor = current.parent();
    }

    scopes.reverse();
    scopes.push(name.to_string());
    (scopes.join("::"), externally_reachable)
}

pub fn is_cpp_atomic_type(ty: &str) -> bool {
    let outer = outer_type_spelling(ty);
    if outer.contains(['*', '&']) {
        return false;
    }
    let compact = outer
        .split_whitespace()
        .find(|token| {
            !matches!(
                *token,
                "const" | "volatile" | "static" | "mutable" | "struct" | "class"
            )
        })
        .unwrap_or("");
    compact.rsplit("::").next() == Some("atomic")
        || compact.ends_with("_atomic")
        || compact.contains("_Atomic(")
        || compact.contains("atomic_")
        || compact.contains("std::atomic_")
        || compact.contains("std::atomic_flag")
        || compact.contains("Atomic")
}

pub fn is_cpp_hot_sync_type(ty: &str) -> bool {
    let outer = outer_type_spelling(ty);
    let ty = outer.as_str();
    if ty.contains(['*', '&']) {
        return false;
    }
    let nominal = identifier_words(ty).last().unwrap_or("");
    is_cpp_atomic_type(ty)
        || ty.contains("std::mutex")
        || ty.contains("std::shared_mutex")
        || ty.contains("pthread_mutex")
        || ty.contains("spinlock")
        || ty.contains("SpinLock")
        || ty.contains("Futex")
        || ty.contains("futex")
        || ty.contains("absl::Mutex")
        || matches!(nominal, "Mutex" | "SpinLock" | "SharedMutex" | "Futex")
}

fn outer_type_spelling(ty: &str) -> String {
    let mut depth = 0usize;
    ty.chars()
        .filter(|ch| match ch {
            '<' => {
                depth += 1;
                false
            }
            '>' => {
                depth = depth.saturating_sub(1);
                false
            }
            _ => depth == 0,
        })
        .collect()
}

pub fn is_hot_scalar_field(name: &str, ty: &str) -> bool {
    let lower = name.to_lowercase();
    let hot_name = [
        "count", "counter", "stat", "hits", "miss", "idx", "index", "tail", "head", "write",
        "read", "epoch", "tick", "size", "state", "flag", "seq", "version",
    ]
    .iter()
    .any(|keyword| lower.contains(keyword));
    hot_name && is_scalar_type(ty)
}

pub fn is_hot_container_name(name: &str) -> bool {
    [
        "bucket", "buckets", "shard", "shards", "slot", "slots", "queue", "queues", "worker",
        "workers", "counter", "counters", "stat", "stats", "hist", "locks", "cache", "caches",
    ]
    .iter()
    .any(|keyword| name.to_lowercase().contains(keyword))
}

pub fn element_type_name(ty: &str) -> Option<String> {
    let compact = normalize_space(ty);
    if let Some(start) = compact.find('<') {
        let end = compact.rfind('>')?;
        if end <= start {
            return None;
        }
        let inside = &compact[start + 1..end];
        let first = inside.split(',').next()?.trim();
        return Some(clean_type_name(first));
    }
    clean_type_name(compact.split_whitespace().next()?).into()
}

pub fn clean_type_name(raw: &str) -> String {
    raw.trim()
        .trim_start_matches("class ")
        .trim_start_matches("struct ")
        .trim_start_matches("const ")
        .trim_matches('&')
        .trim_matches('*')
        .split('<')
        .next()
        .unwrap_or(raw)
        .rsplit("::")
        .next()
        .unwrap_or(raw)
        .trim()
        .to_string()
}

fn anonymous_record_alias(declaration_text: &str, source: &str) -> Option<String> {
    let suffix = declaration_text.rsplit_once('}')?.1;
    identifier_words(suffix)
        .rfind(|word| !is_record_annotation_macro(word, source))
        .map(ToOwned::to_owned)
}

fn record_name_after_alignment(declaration_text: &str, source: &str) -> Option<String> {
    let header = declaration_text.split('{').next()?.split(':').next()?;
    identifier_words(header)
        .rfind(|word| {
            !matches!(*word, "class" | "struct" | "union" | "typedef")
                && !is_record_annotation_macro(word, source)
        })
        .map(ToOwned::to_owned)
}

fn identifier_words(text: &str) -> impl DoubleEndedIterator<Item = &str> {
    text.split(|ch: char| !(ch == '_' || ch.is_ascii_alphanumeric()))
        .filter(|word| {
            !word.is_empty()
                && word
                    .as_bytes()
                    .first()
                    .is_some_and(|byte| *byte == b'_' || byte.is_ascii_alphabetic())
        })
}

fn is_record_annotation_macro(word: &str, source: &str) -> bool {
    matches!(
        word,
        "alignas" | "__attribute__" | "__declspec" | "final" | "override"
    ) || source.lines().any(|line| {
        line.trim()
            .strip_prefix("#define ")
            .and_then(|definition| identifier_words(definition).next())
            == Some(word)
    })
}

type RecordAliases = HashMap<(String, usize), HashMap<String, String>>;

fn record_scoped_aliases(files: &[ParsedCppFile]) -> RecordAliases {
    let mut aliases = RecordAliases::new();
    for file in files {
        let Some(tree) = &file.tree else {
            continue;
        };
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(node.kind(), "class_specifier" | "struct_specifier") {
                return;
            }
            // Only containing lexical scopes supply aliases. A sibling
            // namespace, function or later namespace declaration cannot
            // shadow this record's type names.
            let mut scopes = Vec::new();
            let mut ancestor = node.parent();
            while let Some(parent) = ancestor {
                if matches!(
                    parent.kind(),
                    "translation_unit" | "declaration_list" | "field_declaration_list"
                ) {
                    scopes.push(parent);
                }
                ancestor = parent.parent();
            }
            scopes.reverse();
            if let Some(body) = node.child_by_field_name("body") {
                scopes.push(body);
            }
            let mut visible = HashMap::new();
            for scope in scopes {
                let mut cursor = scope.walk();
                for alias in scope.named_code_children(&mut cursor) {
                    if !matches!(alias.kind(), "alias_declaration" | "type_definition")
                        || alias.has_error()
                        || (scope.kind() != "field_declaration_list"
                            && alias.start_byte() >= node.start_byte())
                    {
                        continue;
                    }
                    if let (Some(name), Some(ty)) = (
                        alias.child_by_field_name(if alias.kind() == "type_definition" {
                            "declarator"
                        } else {
                            "name"
                        }),
                        alias.child_by_field_name("type"),
                    ) {
                        // Pointer/function declarator typedefs need their full
                        // declarator reconstructed; don't bind just the base.
                        if alias.kind() == "type_definition"
                            && !matches!(name.kind(), "type_identifier" | "identifier")
                        {
                            continue;
                        }
                        // Bind the target with the aliases visible at this
                        // declaration, before an inner scope can shadow them.
                        let target = scoped_field_type(node_text(ty, &file.source), Some(&visible));
                        visible.insert(node_text(name, &file.source).to_string(), target);
                    }
                }
            }
            aliases.insert((file.path.clone(), node.start_position().row + 1), visible);
        });
    }
    aliases
}

fn scoped_field_type(ty: &str, aliases: Option<&HashMap<String, String>>) -> String {
    // Targets have already been bound at their declarations. Rebinding an
    // alias chain here could capture an unrelated inner declaration.
    super::type_bindings::substitute(ty, |name| {
        aliases.and_then(|aliases| aliases.get(name)).cloned()
    })
}

fn enrich_with_local_types(
    structs: &mut [CppStructInfo],
    cache_line_size: usize,
    aliases: &RecordAliases,
) {
    // A class-local alias shadows a same-spelled record elsewhere in the
    // project. Resolve it before propagating synchronization, size or padding.
    for record in structs.iter_mut() {
        let local_aliases = aliases.get(&(record.file.clone(), record.line));
        for field in &mut record.fields {
            let resolved = scoped_field_type(&field.ty_str, local_aliases);
            if resolved != field.ty_str {
                let outer = outer_type_spelling(&resolved);
                let read_only = identifier_words(&outer)
                    .any(|token| matches!(token, "const" | "constexpr" | "consteval"));
                field.is_atomic = !read_only && is_cpp_atomic_type(&resolved);
                field.is_hot_sync = !read_only && is_cpp_hot_sync_type(&resolved);
                field.is_hot_scalar = !read_only && is_hot_scalar_field(&field.name, &resolved);
                field.is_indirect = is_indirection_type(&resolved);
                // Preserve any existing explicit alignment estimate, and fill
                // only an unknown size using the lexically bound target.
                if field.estimated_size.is_none() {
                    field.estimated_size = estimate_cpp_type_size(
                        &resolved,
                        field.is_array,
                        field.array_len,
                        cache_line_size,
                    );
                }
                // Downstream holder/pointee effects must see the same bound
                // type as layout, rather than reinterpreting an alias name.
                field.ty_str = resolved;
            }
        }
    }
    let mut name_counts: HashMap<&str, usize> = HashMap::new();
    for record in structs.iter() {
        *name_counts.entry(record.name.as_str()).or_default() += 1;
    }
    let qualified_owners = structs
        .iter()
        .filter(|record| name_counts.get(record.name.as_str()) == Some(&1))
        .map(|record| (record.name.clone(), record.qualified_name.clone()))
        .collect::<HashMap<_, _>>();
    let summary_name = |resolved: &str| {
        let local = clean_type_name(resolved);
        let nominal = outer_type_spelling(resolved)
            .split_whitespace()
            .filter(|word| {
                !matches!(
                    *word,
                    "const" | "volatile" | "struct" | "class" | "typename"
                )
            })
            .collect::<String>();
        if nominal.contains("::")
            && qualified_owners.get(&local).is_none_or(|owner| {
                owner.trim_start_matches("::") != nominal.trim_start_matches("::")
            })
        {
            None
        } else {
            Some(local)
        }
    };
    let mut summaries: HashMap<String, (bool, Option<usize>, bool, Option<usize>)> = structs
        .iter()
        .filter(|record| name_counts.get(record.name.as_str()) == Some(&1))
        .map(|record| {
            (
                record.name.clone(),
                (
                    record.fields.iter().any(|field| {
                        (field.is_atomic || field.is_hot_sync) && !field.is_cache_padded
                    }),
                    record.total_estimated_size,
                    record.is_cache_aligned,
                    record.align_bytes,
                ),
            )
        })
        .collect();

    for _ in 0..8 {
        let mut changed = false;
        for record in structs.iter() {
            if name_counts.get(record.name.as_str()) != Some(&1) {
                continue;
            }
            let mut contains_hot = record
                .fields
                .iter()
                .any(|field| (field.is_atomic || field.is_hot_sync) && !field.is_cache_padded);
            let mut layout_fields = record.fields.clone();
            let local_aliases = aliases.get(&(record.file.clone(), record.line));
            for field in &mut layout_fields {
                let resolved = scoped_field_type(&field.ty_str, local_aliases);
                if outer_type_spelling(&resolved).contains(['*', '&']) {
                    continue;
                }
                let Some(local_type) = summary_name(&resolved) else {
                    continue;
                };
                if let Some((inner_hot, inner_size, inner_aligned, inner_alignment)) =
                    summaries.get(&local_type)
                {
                    contains_hot |= *inner_hot && !inner_aligned;
                    field.estimated_size = field.estimated_size.or(*inner_size);
                    field.is_cache_padded |= *inner_aligned;
                    field.align_bytes = field.align_bytes.max(*inner_alignment);
                }
            }
            let next = (
                contains_hot,
                // Member byte counts are not sizeof(record): both inter-field
                // alignment and trailing padding participate in the stride.
                // Use the same layout calculation as the record itself when
                // propagating an embedded type, rather than shrinking it to
                // the sum of its payload sizes.
                total_size(&layout_fields, cache_line_size, record.align_bytes)
                    .or(record.total_estimated_size),
                record.is_cache_aligned,
                record.align_bytes,
            );
            if summaries.get(&record.name) != Some(&next) {
                summaries.insert(record.name.clone(), next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    for record in structs.iter_mut() {
        let local_aliases = aliases.get(&(record.file.clone(), record.line));
        for field in &mut record.fields {
            // Pointee layout/synchronization belongs to a different object;
            // it cannot enlarge, pad, or synchronize the stored pointer slot.
            let resolved = scoped_field_type(&field.ty_str, local_aliases);
            if outer_type_spelling(&resolved).contains(['*', '&']) {
                continue;
            }
            let Some(local_type) = summary_name(&resolved) else {
                continue;
            };
            if let Some((contains_hot, size, aligned, alignment)) =
                summaries.get(&local_type).copied()
            {
                field.align_bytes = field.align_bytes.max(alignment);
                if aligned {
                    field.is_cache_padded = true;
                } else {
                    if contains_hot && !field.is_cache_padded {
                        field.is_hot_sync = true;
                    }
                }
                if let Some(local_size) = size.or(alignment) {
                    field.estimated_size = Some(
                        field
                            .estimated_size
                            .unwrap_or_default()
                            .max(local_size.max(alignment.unwrap_or(1))),
                    );
                }
            }
        }
        recompute(record, cache_line_size);
    }
}

pub(crate) fn ablate_protection_evidence(record: &mut CppStructInfo, cache_line_size: usize) {
    record.align_bytes = None;
    record.is_cache_aligned = false;
    record.has_cache_padding = false;
    for field in &mut record.fields {
        field.align_bytes = None;
        if field.is_cache_padded || field.is_manual_padding {
            // Removing a field alignment does not erase the underlying
            // scalar type's size. Wrapper/padding-only sizes remain unknown.
            field.estimated_size = if field.is_manual_padding {
                None
            } else {
                estimate_cpp_type_size(
                    &field.ty_str,
                    field.is_array,
                    field.array_len,
                    cache_line_size,
                )
            };
        }
        field.is_cache_padded = false;
        field.is_manual_padding = false;
    }
    recompute(record, cache_line_size);
}

fn recompute(record: &mut CppStructInfo, cache_line_size: usize) {
    record.align_bytes = record.align_bytes.max(
        record
            .fields
            .iter()
            .filter_map(|field| field.align_bytes)
            .max(),
    );
    record.is_cache_aligned = record
        .align_bytes
        .is_some_and(|alignment| alignment >= cache_line_size);
    record.has_cache_padding = record.has_cache_padding
        || record
            .fields
            .iter()
            .any(|field| field.is_cache_padded || field.is_manual_padding)
        || record.is_cache_aligned;
    record.atomic_fields = record
        .fields
        .iter()
        .filter(|field| field.is_atomic && !field.is_cache_padded)
        .map(|field| field.name.clone())
        .collect();
    record.hot_scalar_fields = record
        .fields
        .iter()
        .filter(|field| field.is_hot_scalar && !field.is_cache_padded)
        .map(|field| field.name.clone())
        .collect();
    record.hot_sync_fields = record
        .fields
        .iter()
        .filter(|field| field.is_hot_sync && !field.is_cache_padded)
        .map(|field| field.name.clone())
        .collect();
    record.total_estimated_size = total_size(&record.fields, cache_line_size, record.align_bytes);
    assign_estimated_offsets(&mut record.fields, cache_line_size);
    record.cache_line_groups = compute_cache_line_groups(&record.fields, cache_line_size);
    record.cache_line_groups_precise = false;
    record.compiler_layout_exact = false;
}

fn assign_estimated_offsets(fields: &mut [CppFieldInfo], cache_line_size: usize) {
    let offsets = compute_estimated_offsets(fields, cache_line_size);
    for (field, offset) in fields.iter_mut().zip(offsets) {
        field.offset = offset;
    }
}

fn compute_estimated_offsets(
    fields: &[CppFieldInfo],
    cache_line_size: usize,
) -> Vec<Option<usize>> {
    let mut offsets = Vec::with_capacity(fields.len());
    let mut current_offset = 0usize;

    for field in fields {
        let size = field.estimated_size.unwrap_or(8).max(1);
        let align = field_alignment(field, cache_line_size);
        let offset = align_up(current_offset, align);
        offsets.push(Some(offset));
        current_offset = offset + size;
    }

    offsets
}

fn compute_cache_line_groups(fields: &[CppFieldInfo], cache_line_size: usize) -> Vec<Vec<String>> {
    let offsets = compute_estimated_offsets(fields, cache_line_size);
    let mut by_line: HashMap<usize, Vec<String>> = HashMap::new();
    for (field, offset) in fields.iter().zip(offsets) {
        let Some(offset) = offset else {
            continue;
        };
        let size = field.estimated_size.unwrap_or(8).max(1);
        let first = offset / cache_line_size;
        let last = offset.saturating_add(size - 1) / cache_line_size;
        for line in first..=last {
            by_line.entry(line).or_default().push(field.name.clone());
        }
    }
    let mut groups = by_line.into_iter().collect::<Vec<_>>();
    groups.sort_by_key(|(line, _)| *line);
    groups.into_iter().map(|(_, fields)| fields).collect()
}

/// Whether two selected record fields may occupy one cache line.
///
/// Exact compiler layouts can use their recovered line groups. Source-only
/// C++ offsets are ABI estimates and the object's base address modulo a cache
/// line is unknown, so use an existential placement test instead of silently
/// assuming that every object starts at cache-line offset zero.
pub fn fields_may_share_cache_line(record: &CppStructInfo, fields: &[String]) -> bool {
    if record.cache_line_groups_precise {
        return record
            .cache_line_groups
            .iter()
            .any(|group| fields.iter().filter(|field| group.contains(field)).count() >= 2);
    }

    let candidates = record
        .fields
        .iter()
        .filter(|field| fields.contains(&field.name))
        .collect::<Vec<_>>();
    candidates.iter().enumerate().any(|(left_index, left)| {
        candidates.iter().skip(left_index + 1).any(|right| {
            let (Some(left_offset), Some(right_offset)) = (left.offset, right.offset) else {
                // An unknown ABI offset must remain a may-alias witness.
                return true;
            };
            // Restrict source-estimated placements to the record's natural
            // alignment. A pair of 8-byte slots 64 bytes apart cannot share
            // a 64-byte block merely because an impossible byte-skewed base
            // would put their endpoints in one block. Unknown prefix sizes,
            // packed records and inheritance do not support this exclusion.
            let known_prefix = record
                .fields
                .iter()
                .take_while(|field| {
                    field
                        .offset
                        .is_some_and(|offset| offset <= left_offset.max(right_offset))
                })
                .all(|field| field.estimated_size.is_some());
            if known_prefix
                && !record.is_packed
                && !record.has_base_classes
                && !record.has_no_unique_address
                && let (Some(left_size), Some(right_size)) =
                    (left.estimated_size, right.estimated_size)
                && left_size > 0
                && right_size > 0
            {
                let alignment = record
                    .fields
                    .iter()
                    .filter_map(|field| {
                        field
                            .estimated_size
                            .map(|_| field_alignment(field, record.cache_line_size))
                    })
                    .max()
                    .unwrap_or(1)
                    .max(record.align_bytes.unwrap_or(1));
                if alignment.is_power_of_two() {
                    return (0..record.cache_line_size).step_by(alignment).any(|base| {
                        let left_start = base.saturating_add(left_offset);
                        let right_start = base.saturating_add(right_offset);
                        left_start / record.cache_line_size
                            <= right_start.saturating_add(right_size - 1) / record.cache_line_size
                            && right_start / record.cache_line_size
                                <= left_start.saturating_add(left_size - 1) / record.cache_line_size
                    });
                }
            }
            let left_end = left_offset.saturating_add(left.estimated_size.unwrap_or(1));
            let right_end = right_offset.saturating_add(right.estimated_size.unwrap_or(1));
            let nearest_byte_distance = if left_end <= right_offset {
                (right_offset - left_end).saturating_add(1)
            } else if right_end <= left_offset {
                (left_offset - right_end).saturating_add(1)
            } else {
                0
            };
            // `end` is exclusive: the nearest byte is end - 1, so the
            // distance between occupied bytes is gap + 1, not gap.
            nearest_byte_distance < record.cache_line_size
        })
    })
}

/// Source/ABI model for selected bytes in distinct consecutive objects. Keep
/// an unknown layout as may-risk; a byte-distance test alone admits impossible
/// skewed placements when the record has natural alignment.
pub(crate) fn fields_may_share_across_objects(
    record: &CppStructInfo,
    a: &CppFieldInfo,
    b: &CppFieldInfo,
) -> bool {
    if !record.compiler_layout_exact && ordered_members_separate_objects(record, a, b) {
        return false;
    }
    if !record.compiler_layout_exact
        && (record.has_base_classes
            || record.has_no_unique_address
            || record.is_packed
            || record
                .fields
                .iter()
                .any(|f| f.estimated_size.is_none() || f.bitfield_group.is_some()))
    {
        return true;
    }
    let (Some(stride), Some(a_offset), Some(a_size), Some(b_offset), Some(b_size)) = (
        record.total_estimated_size,
        a.offset,
        a.estimated_size,
        b.offset,
        b.estimated_size,
    ) else {
        return true;
    };
    if a_size == 0 || b_size == 0 {
        return false;
    }
    if stride == 0 {
        return true;
    }
    // Only known scalar/pointer members establish a minimum natural alignment.
    // The byte size of an embedded opaque record is not its alignment.
    let alignment = record
        .align_bytes
        .unwrap_or(1)
        .max(if record.compiler_layout_exact {
            1
        } else {
            record
                .fields
                .iter()
                .filter_map(|f| {
                    let outer = outer_type_spelling(&f.ty_str);
                    (scalar_type_size(&f.ty_str).is_some() || outer.contains(['*', '&']))
                        .then(|| field_alignment(f, record.cache_line_size))
                })
                .max()
                .unwrap_or(1)
        });
    let alignment = if alignment.is_power_of_two() {
        alignment
    } else {
        1
    };
    let overlaps = |left: usize, left_size: usize, right: usize, right_size: usize| {
        (0..record.cache_line_size).step_by(alignment).any(|base| {
            let Some((left, right)) = base.checked_add(left).zip(base.checked_add(right)) else {
                return true;
            };
            let Some((left_end, right_end)) = left
                .checked_add(left_size - 1)
                .zip(right.checked_add(right_size - 1))
            else {
                return true;
            };
            left / record.cache_line_size <= right_end / record.cache_line_size
                && right / record.cache_line_size <= left_end / record.cache_line_size
        })
    };
    let Some((next_a, next_b)) = stride
        .checked_add(a_offset)
        .zip(stride.checked_add(b_offset))
    else {
        return true;
    };
    overlaps(a_offset, a_size, next_b, b_size) || overlaps(b_offset, b_size, next_a, a_size)
}

/// Distance from the last byte of A in one object to the first byte of B
/// in the next is at least suffix_after(A) + prefix_before(B) + 1. Unknown
/// members/bases contribute no proved bytes; they are never assigned offsets
/// or sizes. Both directions must be separated. This uses the same target
/// scalar/standard-container size model as the existing complete-layout path.
fn ordered_members_separate_objects(
    record: &CppStructInfo,
    a: &CppFieldInfo,
    b: &CppFieldInfo,
) -> bool {
    if !record.ordered_own_fields
        || record.is_packed
        || record.has_no_unique_address
        || record.fields.iter().any(|field| {
            // Alias resolution runs after the original declaration proof.
            outer_type_spelling(&field.ty_str).contains('&') || field.bitfield_group.is_some()
        })
    {
        return false;
    }
    let Some(a_index) = record.fields.iter().position(|f| std::ptr::eq(f, a)) else {
        return false;
    };
    let Some(b_index) = record.fields.iter().position(|f| std::ptr::eq(f, b)) else {
        return false;
    };
    let distance = |left: usize, right: usize| {
        record.fields[left + 1..]
            .iter()
            .chain(record.fields[..right].iter())
            .try_fold(1usize, |bytes, field| {
                // Do not recursively borrow a recovered record's estimated
                // offsets or a name-based padding heuristic as a lower bound.
                let known = extract_align_bytes(&field.ty_str).is_none();
                let size = known
                    .then(|| {
                        estimate_cpp_type_size(
                            &field.ty_str,
                            field.is_array,
                            field.array_len,
                            record.cache_line_size,
                        )
                    })
                    .flatten()
                    .unwrap_or(0);
                bytes.checked_add(size)
            })
            .is_some_and(|minimum| minimum >= record.cache_line_size)
    };
    distance(a_index, b_index) && distance(b_index, a_index)
}

fn total_size(
    fields: &[CppFieldInfo],
    cache_line_size: usize,
    explicit_alignment: Option<usize>,
) -> Option<usize> {
    if fields.is_empty() {
        return None;
    }
    let offsets = compute_estimated_offsets(fields, cache_line_size);
    let end = fields
        .iter()
        .zip(offsets)
        .try_fold(0usize, |end, (field, offset)| {
            Some(end.max(offset?.saturating_add(field.estimated_size?)))
        })?;
    let natural_alignment = fields
        .iter()
        .map(|field| field_alignment(field, cache_line_size))
        .max()
        .unwrap_or(1)
        .max(explicit_alignment.unwrap_or(1));
    Some(align_up(end, natural_alignment))
}

fn estimate_cpp_type_alignment(ty: &str, size: usize) -> usize {
    extract_align_bytes(ty).unwrap_or_else(|| {
        if let Some((prefix, _)) = ty.split_once('[') {
            // An array has its element alignment, not its total byte size.
            return scalar_type_size(prefix.trim())
                .or_else(|| {
                    prefix
                        .trim()
                        .rsplit_once(char::is_whitespace)
                        .and_then(|(element, _)| scalar_type_size(element))
                })
                .map(|bytes| bytes.next_power_of_two().min(8))
                .unwrap_or(1);
        }
        if is_indirection_type(ty)
            || ty.contains("std::vector")
            || ty.contains("std::shared_ptr")
            || ty.contains("std::unique_ptr")
            || ty.contains("std::mutex")
            || ty.contains("pthread_mutex")
        {
            8
        } else {
            scalar_type_size(ty)
                .unwrap_or(size)
                .next_power_of_two()
                .min(8)
        }
    })
}

fn field_alignment(field: &CppFieldInfo, cache_line_size: usize) -> usize {
    estimate_cpp_type_alignment(&field.ty_str, field.estimated_size.unwrap_or(1))
        .max(field.align_bytes.unwrap_or(1))
        .max(if field.is_cache_padded {
            cache_line_size
        } else {
            1
        })
}

fn estimate_cpp_type_size(
    ty: &str,
    is_array: bool,
    array_len: Option<usize>,
    _cache_line_size: usize,
) -> Option<usize> {
    if let Some(alignment) = extract_align_bytes(ty) {
        return Some(alignment);
    }
    let outer = outer_type_spelling(ty);
    let base = if outer.contains(['*', '&']) {
        Some(8)
    } else if outer.split_whitespace().any(|token| token == "std::vector") {
        // Indirect element storage does not make the inline vector object
        // a single pointer. Keep the existing LP64 three-pointer ABI model,
        // but do not apply it to the bit-packed bool specialization or to
        // an explicit allocator whose inline state is not known here.
        let arguments = ty
            .split_once('<')
            .and_then(|(_, rest)| rest.rsplit_once('>'));
        match arguments {
            Some((arguments, _)) if arguments.trim() != "bool" && !arguments.contains(',') => {
                Some(24)
            }
            _ => return None,
        }
    } else if outer
        .split_whitespace()
        .any(|token| matches!(token, "std::shared_ptr" | "std::weak_ptr"))
    {
        // LP64 holder: stored pointer plus separately allocated control block.
        Some(16)
    } else if outer
        .split_whitespace()
        .any(|token| token == "std::unique_ptr")
    {
        // Stateful custom deleters can occupy inline storage of unknown size.
        if ty
            .split_once('<')
            .is_some_and(|(_, args)| args.contains(','))
        {
            return None;
        }
        Some(8)
    } else if is_cpp_atomic_type(ty) {
        if ty.contains("bool") || ty.contains("flag") {
            Some(1)
        } else if ty.contains("64")
            || ty.contains("long")
            || ty.contains("size_t")
            || ty.contains("uint64")
        {
            Some(8)
        } else {
            Some(4)
        }
    } else if matches!(outer.trim(), "std::mutex" | "pthread_mutex_t") {
        Some(40)
    } else {
        if is_array {
            let prefix = ty.split('[').next().unwrap_or(ty).trim();
            // The parser retains a named array declarator after its type.
            scalar_type_size(prefix).or_else(|| {
                prefix
                    .rsplit_once(char::is_whitespace)
                    .and_then(|(head, _)| scalar_type_size(head))
            })
        } else {
            scalar_type_size(ty)
        }
    };

    if is_array {
        base.and_then(|base| array_len.and_then(|len| base.checked_mul(len)))
    } else {
        base
    }
}

fn is_scalar_type(ty: &str) -> bool {
    scalar_type_size(ty).is_some() || is_cpp_atomic_type(ty)
}

pub(crate) fn scalar_type_size(ty: &str) -> Option<usize> {
    let normalized = ty
        .split_whitespace()
        .filter(|word| !matches!(*word, "const" | "volatile" | "mutable" | "constexpr"))
        .collect::<Vec<_>>()
        .join(" ");
    let normalized = normalized.strip_prefix("std::").unwrap_or(&normalized);
    Some(match normalized {
        "bool" | "char" | "signed char" | "unsigned char" | "int8_t" | "uint8_t" => 1,
        "short" | "short int" | "signed short" | "signed short int" | "unsigned short"
        | "unsigned short int" | "int16_t" | "uint16_t" => 2,
        "int" | "signed" | "signed int" | "unsigned" | "unsigned int" | "float" | "int32_t"
        | "uint32_t" => 4,
        "long"
        | "long int"
        | "signed long"
        | "signed long int"
        | "unsigned long"
        | "unsigned long int"
        | "long long"
        | "long long int"
        | "signed long long"
        | "signed long long int"
        | "unsigned long long"
        | "unsigned long long int"
        | "double"
        | "size_t"
        | "ssize_t"
        | "ptrdiff_t"
        | "intptr_t"
        | "uintptr_t"
        | "int64_t"
        | "uint64_t" => 8,
        _ => return None,
    })
}

fn is_indirection_type(ty: &str) -> bool {
    let outer = outer_type_spelling(ty);
    outer.contains(['*', '&'])
        || outer.split_whitespace().any(|token| {
            matches!(
                token,
                "std::shared_ptr" | "std::weak_ptr" | "std::unique_ptr" | "std::vector"
            )
        })
}

fn is_manual_padding_field(name: &str, ty: &str) -> bool {
    let lower = name.to_lowercase();
    let padding_name =
        lower.contains("pad") || lower.contains("padding") || lower.starts_with("_pad");
    padding_name
        && (ty.contains("char")
            || ty.contains("std::byte")
            || ty.contains("uint8_t")
            || ty.contains("uint64_t")
            || ty.contains('['))
}

fn declaration_has_manual_cache_padding(text: &str, cache_line_size: usize) -> bool {
    text.lines().any(|line| {
        let lower = line.to_ascii_lowercase();
        let padding_name =
            lower.contains("padding") || lower.contains("_pad") || lower.contains("pad_");
        padding_name
            && (bracketed_usize(line).is_some_and(|size| size >= cache_line_size)
                || bracketed_expression_mentions_cache_line(line, cache_line_size))
    })
}

fn bracketed_expression_mentions_cache_line(text: &str, cache_line_size: usize) -> bool {
    let Some(open) = text.find('[') else {
        return false;
    };
    let Some(relative_close) = text[open + 1..].find(']') else {
        return false;
    };
    let expression = &text[open + 1..open + 1 + relative_close];
    expression
        .split(|character: char| !character.is_ascii_alphanumeric() && character != '_')
        .any(|token| token.parse::<usize>().ok() == Some(cache_line_size))
}

fn bracketed_usize(text: &str) -> Option<usize> {
    let open = text.find('[')?;
    let close = text[open + 1..].find(']')? + open + 1;
    text[open + 1..close].trim().parse().ok()
}

pub(crate) fn extract_align_bytes(text: &str) -> Option<usize> {
    let tokens = super::parser::source_text::code_tokens(text);
    let mut alignment = None;
    for (index, token) in tokens.iter().enumerate() {
        if *token == "alignas" {
            alignment = alignment.max(numeric_attribute_argument(&tokens, index));
        } else if matches!(*token, "__attribute__" | "__attribute")
            && tokens.get(index + 1) == Some(&"(")
            && tokens.get(index + 2) == Some(&"(")
            && let Some(end) = closing_parenthesis(&tokens, index + 2)
            && tokens.get(end + 1) == Some(&")")
        {
            let mut depth = 0usize;
            for attribute in index + 3..end {
                if depth == 0
                    && (attribute == index + 3 || tokens[attribute - 1] == ",")
                    && matches!(tokens[attribute], "aligned" | "__aligned__")
                {
                    alignment = alignment.max(numeric_attribute_argument(&tokens, attribute));
                }
                match tokens[attribute] {
                    "(" => depth += 1,
                    ")" => depth = depth.saturating_sub(1),
                    _ => {}
                }
            }
        } else if *token == "[" && tokens.get(index + 1) == Some(&"[") {
            let Some(end) = (index + 2..tokens.len().saturating_sub(1))
                .find(|&end| tokens[end..end + 2] == ["]", "]"])
            else {
                continue;
            };
            let using_gnu = tokens.get(index + 2..index + 5) == Some(&["using", "gnu", ":"]);
            let begin = index + if using_gnu { 5 } else { 2 };
            let mut depth = 0usize;
            for attribute in begin..end {
                if depth == 0 && (attribute == begin || tokens[attribute - 1] == ",") {
                    if using_gnu && tokens[attribute] == "aligned" {
                        alignment = alignment.max(numeric_attribute_argument(&tokens, attribute));
                    } else if tokens.get(attribute..attribute + 4)
                        == Some(&["gnu", ":", ":", "aligned"])
                    {
                        alignment =
                            alignment.max(numeric_attribute_argument(&tokens, attribute + 3));
                    }
                }
                match tokens[attribute] {
                    "(" => depth += 1,
                    ")" => depth = depth.saturating_sub(1),
                    _ => {}
                }
            }
        } else if *token == "__declspec"
            && tokens.get(index + 1..index + 3) == Some(&["(", "align"])
            && tokens.get(index + 6) == Some(&")")
        {
            alignment = alignment.max(numeric_attribute_argument(&tokens, index + 2));
        }
    }
    alignment
}

fn closing_parenthesis(tokens: &[&str], start: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(start) {
        match *token {
            "(" => depth += 1,
            ")" => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(index);
                }
            }
            _ => {}
        }
    }
    None
}

fn numeric_attribute_argument(tokens: &[&str], name: usize) -> Option<usize> {
    if tokens.get(name + 1) != Some(&"(") || tokens.get(name + 3) != Some(&")") {
        return None;
    }
    let literal = tokens.get(name + 2)?.replace('\'', "");
    let literal = literal.trim_end_matches(['u', 'U', 'l', 'L']);
    let value = if let Some(hex) = literal
        .strip_prefix("0x")
        .or_else(|| literal.strip_prefix("0X"))
    {
        usize::from_str_radix(hex, 16).ok()
    } else if let Some(binary) = literal
        .strip_prefix("0b")
        .or_else(|| literal.strip_prefix("0B"))
    {
        usize::from_str_radix(binary, 2).ok()
    } else if literal.starts_with('0') && literal.len() > 1 {
        usize::from_str_radix(literal, 8).ok()
    } else {
        literal.parse().ok()
    }?;
    value.is_power_of_two().then_some(value)
}

fn has_explicit_cache_alignment(text: &str, cache_line_size: usize) -> bool {
    extract_align_bytes(text).is_some_and(|bytes| bytes >= cache_line_size)
}

fn surrounding_has_pack(source: &str, start: usize) -> bool {
    let safe_start = floor_char_boundary(source, start.min(source.len()));
    let prefix_start = floor_char_boundary(source, safe_start.saturating_sub(4096));
    let prefix = &source[prefix_start..safe_start];
    let suffix_end = ceil_char_boundary(source, (safe_start + 4096).min(source.len()));
    let suffix = &source[safe_start..suffix_end];
    prefix.contains("#pragma pack(push")
        && !prefix
            .rsplit("#pragma pack")
            .next()
            .unwrap_or("")
            .contains("pop")
        || suffix
            .lines()
            .take(3)
            .any(|line| line.contains("__attribute__((packed"))
}

fn floor_char_boundary(text: &str, mut index: usize) -> usize {
    index = index.min(text.len());
    while index > 0 && !text.is_char_boundary(index) {
        index -= 1;
    }
    index
}

fn ceil_char_boundary(text: &str, mut index: usize) -> usize {
    index = index.min(text.len());
    while index < text.len() && !text.is_char_boundary(index) {
        index += 1;
    }
    index
}

fn parse_access_specifier(text: &str) -> ItemVisibility {
    if text.contains("public") {
        ItemVisibility::Public
    } else if text.contains("protected") {
        ItemVisibility::Restricted
    } else {
        ItemVisibility::Private
    }
}

fn extract_declarator_name(node: Node<'_>, source: &str) -> Option<String> {
    match node.kind() {
        "field_identifier" | "identifier" => Some(node_text(node, source).to_string()),
        "function_declarator" => node
            .child_by_field_name("declarator")
            .and_then(|inner| extract_declarator_name(inner, source)),
        "array_declarator"
        | "pointer_declarator"
        | "reference_declarator"
        | "parenthesized_declarator"
        | "attributed_declarator"
        | "init_declarator" => {
            let mut cursor = node.walk();
            for child in node.code_children(&mut cursor) {
                if let Some(name) = extract_declarator_name(child, source) {
                    return Some(name);
                }
            }
            None
        }
        _ => None,
    }
}

fn extract_name_from_declarator_text(text: &str) -> Option<String> {
    let before_init = text.split('=').next().unwrap_or(text);
    let before_array = before_init.split('[').next().unwrap_or(before_init);
    let cleaned = before_array
        .trim()
        .trim_start_matches('*')
        .trim_start_matches('&')
        .trim();
    cleaned
        .split_whitespace()
        .last()
        .map(|name| name.trim_matches('*').trim_matches('&').to_string())
}

fn split_type_and_declarator(text: &str) -> Option<(&str, &str)> {
    let mut angle_depth = 0i32;
    let mut bracket_depth = 0i32;
    let mut paren_depth = 0i32;
    let bytes = text.as_bytes();
    for idx in (0..bytes.len()).rev() {
        match bytes[idx] as char {
            '>' => angle_depth += 1,
            '<' => angle_depth -= 1,
            ']' => bracket_depth += 1,
            '[' => bracket_depth -= 1,
            ')' => paren_depth += 1,
            '(' => paren_depth -= 1,
            ' ' | '\t' if angle_depth == 0 && bracket_depth == 0 && paren_depth == 0 => {
                let ty = text[..idx].trim();
                let decl = text[idx..].trim();
                if !ty.is_empty() && !decl.is_empty() {
                    return Some((ty, decl));
                }
            }
            _ => {}
        }
    }
    None
}

fn extract_array_len(text: &str) -> Option<usize> {
    let open = text.find('[')?;
    let close = text[open + 1..].find(']')? + open + 1;
    constant_array_bound(text[open + 1..close].trim(), 0)
}

// A bounded source-ABI estimate, never evaluate calls or unknown sizeof types.
fn constant_array_bound(text: &str, depth: usize) -> Option<usize> {
    if depth > 16 || text.len() > 256 {
        return None;
    }
    let text = text.trim();
    let mut nesting = 0i32;
    for (index, byte) in text.bytes().enumerate().rev() {
        match byte {
            b')' => nesting += 1,
            b'(' => nesting -= 1,
            b'+' | b'-' if nesting == 0 => {
                let left = constant_array_bound(&text[..index], depth + 1)?;
                let right = constant_array_bound(&text[index + 1..], depth + 1)?;
                return if byte == b'+' {
                    left.checked_add(right)
                } else {
                    left.checked_sub(right)
                };
            }
            _ => {}
        }
    }
    if let Some(ty) = text
        .strip_prefix("sizeof(")
        .and_then(|s| s.strip_suffix(')'))
    {
        return scalar_type_size(ty.trim());
    }
    if let Some(inner) = text.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        return constant_array_bound(inner, depth + 1);
    }
    text.parse().ok()
}

fn infer_field_type_text(field_text: &str) -> String {
    split_type_and_declarator(field_text.trim().trim_end_matches(';'))
        .map(|(ty, _)| ty.to_string())
        .unwrap_or_else(|| field_text.trim().to_string())
}

fn is_method_declaration(text: &str) -> bool {
    text.contains('(')
        && text.contains(')')
        && !text.trim_start().starts_with("_Atomic(")
        && !text.contains("GUARDED_BY(")
        && !text.contains("PT_GUARDED_BY(")
        && !text.contains("guarded_by(")
}

fn field_declaration_is_method(node: Node<'_>, source: &str) -> bool {
    // Parentheses in a default value, array bound or type expression are not
    // evidence of a member function. Only inspect the declarator spine.
    // Retain annotation recovery for unexpanded thread-safety attributes.
    if !is_method_declaration(node_text(node, source)) {
        return false;
    }
    let mut cursor = node.walk();
    node.children_by_field_name("declarator", &mut cursor)
        .any(|mut declarator| {
            loop {
                if declarator.kind() == "function_declarator" {
                    // Parenthesized indirection binds the identifier before
                    // the parameter suffix: R (&slot)(Args) is a data member.
                    return !declarator
                        .child_by_field_name("declarator")
                        .is_some_and(|inner| {
                            if inner.kind() != "parenthesized_declarator" {
                                return false;
                            }
                            let Some(indirection) = inner.named_code_child(0) else {
                                return false;
                            };
                            if !matches!(
                                indirection.kind(),
                                "reference_declarator" | "pointer_declarator"
                            ) {
                                return false;
                            }
                            indirection
                                .child_by_field_name("declarator")
                                .or_else(|| indirection.named_code_child(0))
                                .is_some_and(|name| {
                                    matches!(name.kind(), "identifier" | "field_identifier")
                                })
                        });
                }
                // tree-sitter-cpp reference_declarator uses an unnamed
                // declarator child (unlike pointer_declarator). Follow only
                // that spine, never parameters or default-value expressions.
                let inner = declarator.child_by_field_name("declarator").or_else(|| {
                    (declarator.kind() == "reference_declarator")
                        .then(|| declarator.named_code_child(0))
                        .flatten()
                });
                let Some(inner) = inner else {
                    return false;
                };
                declarator = inner;
            }
        })
}

fn extract_method_name(text: &str) -> Option<String> {
    let before_paren = text.split('(').next()?.trim();
    before_paren
        .split_whitespace()
        .last()
        .map(|name| name.trim_matches('*').trim_matches('&').to_string())
}

fn normalize_space(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn align_up(value: usize, align: usize) -> usize {
    if align == 0 {
        value
    } else {
        (value + align - 1) & !(align - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alignment_requires_real_attribute_syntax_and_uses_the_strongest_constraint() {
        for (source, expected) in [
            ("alignas(32) alignas(128) int value", Some(128)),
            ("int value __attribute__((aligned(64)))", Some(64)),
            (
                "int value __attribute__((unused, __aligned__(0x40UL)))",
                Some(64),
            ),
            ("[[gnu::aligned(128)]] int value", Some(128)),
            ("[[using gnu: aligned(64)]] int value", Some(64)),
            ("__declspec(align(64)) int value", Some(64)),
            ("int value = aligned(128)", None),
            ("int aligned_counter{64}", None),
            ("/* alignas(64) */ int value", None),
            ("const char* value = \"alignas(128)\"", None),
            (
                "const char* value = R\"tag(__attribute__((aligned(128))))tag\"",
                None,
            ),
            ("[[custom::aligned(128)]] int value", None),
            ("[[custom::gnu::aligned(128)]] int value", None),
            ("__attribute__((deprecated(aligned(128)))) int value", None),
            ("alignas(0) int value", None),
            ("alignas(48) int value", None),
        ] {
            assert_eq!(extract_align_bytes(source), expected, "{source}");
        }
    }

    #[test]
    fn recovered_record_inheritance_is_read_only_from_the_header() {
        for (source, inherits) in [
            (
                "class Plain { public: int first; private: int second; };",
                false,
            ),
            ("struct Scoped { std::atomic<int> value; };", false),
            ("struct Bits { unsigned flag:1; };", false),
            ("struct space::Qualified { int value; };", false),
            ("struct Derived : public space::Base { int value; };", true),
        ] {
            let files = super::super::parser::parse_cpp_files(vec![super::super::types::CppFile {
                path: "fallback.hpp".into(),
                source: source.into(),
            }]);
            let records = collect_records_fallback(&files[0], "fixture", 64, &Default::default());
            assert_eq!(records.len(), 1, "{source}: {records:#?}");
            assert_eq!(records[0].has_base_classes, inherits, "{source}");
        }
    }
    use crate::cpp_detection::parser::parse_cpp_files;
    use crate::cpp_detection::types::CppFile;

    #[test]
    fn bitfield_locations_respect_zero_unknown_and_ordinary_member_boundaries() {
        let files = parse_cpp_files(vec![CppFile {
            path: "bits.hpp".into(),
            source: "struct Bits { unsigned a:1, b:2; unsigned :0; unsigned c:1; unsigned d:1; unsigned :WIDTH; unsigned e:1; int ordinary; unsigned f:1, other, g:1; };".into(),
        }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let record = &records[0];
        let group = |name: &str| {
            record
                .fields
                .iter()
                .find(|f| f.name == name)
                .unwrap()
                .bitfield_group
        };
        assert!(group("a").is_some(), "{record:#?}");
        assert_eq!(group("a"), group("b"));
        assert_ne!(group("b"), group("c"));
        assert_eq!(group("c"), group("d"));
        assert_ne!(group("d"), group("e"));
        assert_ne!(group("e"), group("f"));
        assert_ne!(group("f"), group("g"));
        assert_eq!(group("ordinary"), None);
        assert_eq!(group("other"), None);
    }

    #[test]
    fn bitfield_location_can_span_only_uniform_preprocessor_branches() {
        for (branch, joined) in [
            ("unsigned b:1;", true),
            ("unsigned :0; unsigned b:1;", false),
            ("unsigned :WIDTH; unsigned b:1;", false),
            ("int value;", false),
        ] {
            let source = format!(
                "struct Bits {{\nunsigned first:16;\n#if ORDER == BIG\nunsigned a:1;\n#elif ORDER == LITTLE\n{branch}\n#endif\nunsigned last:16;\n}};"
            );
            let files = parse_cpp_files(vec![CppFile {
                path: "bits.hpp".into(),
                source,
            }]);
            let records = collect_cpp_structs(&files, "fixture", 64);
            let fields = &records[0].fields;
            let group = |name: &str| {
                fields
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .bitfield_group
            };
            assert_eq!(
                group("first") == group("last"),
                joined,
                "{branch}\n{fields:#?}"
            );
        }
    }

    #[test]
    fn inline_vector_descriptor_is_not_its_element_storage_pointer() {
        for element in ["int", "char", "double", "int*", "std::atomic<int>"] {
            let ty = format!("std::vector<{element}>");
            assert_eq!(estimate_cpp_type_size(&ty, false, None, 64), Some(24));
            assert_eq!(
                estimate_cpp_type_size(&format!("{ty}*"), false, None, 64),
                Some(8)
            );
            assert_eq!(estimate_cpp_type_size(&ty, true, Some(3), 64), Some(72));
        }
        assert_eq!(
            estimate_cpp_type_size("std::vector<bool>", false, None, 64),
            None
        );
        assert_eq!(
            estimate_cpp_type_size("std::vector<bool>", true, Some(3), 64),
            None
        );
        assert_eq!(
            estimate_cpp_type_size("std::vector<int, StatefulAllocator<int>>", false, None, 64),
            None
        );
    }

    #[test]
    fn aggregate_template_arguments_do_not_supply_scalar_or_pointer_layout() {
        for ty in [
            "std::map<int64_t, char>",
            "std::unordered_map<int, Thing*>",
            "std::optional<bool>",
            "Wrapper<std::mutex>",
            "CharacterBuffer",
            "uint64_table",
        ] {
            assert_eq!(estimate_cpp_type_size(ty, false, None, 64), None, "{ty}");
            assert!(!is_scalar_type(ty), "{ty}");
            assert!(!is_indirection_type(ty), "{ty}");
        }
        assert_eq!(
            estimate_cpp_type_size("Unknown values[4]", true, Some(4), 64),
            None
        );
        assert_eq!(
            estimate_cpp_type_size("int values[4]", true, Some(4), 64),
            Some(16)
        );
        assert_eq!(
            estimate_cpp_type_size("int values[N]", true, None, 64),
            None
        );
        for (ty, size) in [
            ("unsigned int", 4),
            ("const std::uint64_t", 8),
            ("unsigned long long int", 8),
            ("volatile signed char", 1),
            ("std::shared_ptr<char>", 16),
            ("std::weak_ptr<int>", 16),
            ("std::unique_ptr<int>", 8),
            ("std::shared_ptr<int>*", 8),
        ] {
            assert_eq!(
                estimate_cpp_type_size(ty, false, None, 64),
                Some(size),
                "{ty}"
            );
        }
        assert_eq!(
            estimate_cpp_type_size("std::unique_ptr<int, StatefulDeleter>", false, None, 64),
            None
        );
        assert!(
            is_scalar_type("std::atomic<int>"),
            "atomic scalar accesses remain eligible for field_group"
        );
    }

    #[test]
    fn estimated_field_colocation_matches_exhaustive_byte_placement() {
        let files = parse_cpp_files(vec![CppFile {
            path: "intervals.hpp".into(),
            source: "struct Intervals { char left; char right; };".into(),
        }]);
        let mut record = collect_cpp_structs(&files, "fixture", 64).remove(0);
        record.cache_line_groups_precise = false;
        let selected = vec!["left".to_string(), "right".to_string()];
        for line_size in [16, 32, 64, 128] {
            record.cache_line_size = line_size;
            for width in [1, 4, 8] {
                for right_offset in width..=2 * line_size {
                    record.fields[0].offset = Some(0);
                    record.fields[0].estimated_size = Some(width);
                    record.fields[1].offset = Some(right_offset);
                    record.fields[1].estimated_size = Some(1);
                    let expected = (0..line_size).any(|base| {
                        (0..width).any(|byte| {
                            (base + byte) / line_size == (base + right_offset) / line_size
                        })
                    });
                    assert_eq!(
                        fields_may_share_cache_line(&record, &selected),
                        expected,
                        "line={line_size}, width={width}, right={right_offset}"
                    );
                    record.fields.swap(0, 1);
                    assert_eq!(fields_may_share_cache_line(&record, &selected), expected);
                    record.fields.swap(0, 1);
                }
            }
        }
    }

    #[test]
    fn record_local_alias_shadows_an_unrelated_sync_record() {
        let files = parse_cpp_files(vec![CppFile { path: "aliases.hpp".into(), source: "namespace remote { struct Flags { std::mutex mutex; }; }\nstruct Plain {\nusing Flags = std::bitset<64>;\nFlags flags;\n};\nstruct Wrapper {\nusing Flags = remote::Flags;\nFlags flags;\n};\nstruct Direct {\nusing Counter = std::atomic<int>;\nCounter counter;\n};\n".into() }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let field = |name: &str| {
            &records
                .iter()
                .find(|record| record.name == name)
                .unwrap()
                .fields[0]
        };
        assert!(!field("Plain").is_atomic);
        assert!(!field("Plain").is_hot_sync);
        assert!(field("Wrapper").is_hot_sync);
        assert!(field("Direct").is_atomic);
    }

    #[test]
    fn only_the_outer_inline_type_supplies_atomic_and_sync_traits() {
        for ty in [
            "std::vector<std::atomic<int>>",
            "std::unique_ptr<ns::AtomicCounter>",
            "std::atomic<int>*",
            "std::atomic<int>&",
        ] {
            assert!(!is_cpp_atomic_type(ty), "{ty}");
            assert!(!is_cpp_hot_sync_type(ty), "{ty}");
        }
        for ty in [
            "std::atomic<int>",
            "std::atomic<int> count",
            "std::atomic<Thing*>",
            "weak_atomic<size_t>",
            "boost::atomic<int>",
            "atomic_int",
            "_Atomic(int)",
        ] {
            assert!(is_cpp_atomic_type(ty), "{ty}");
        }
        assert!(!is_cpp_hot_sync_type("std::vector<std::mutex>"));
        assert!(!is_cpp_hot_sync_type("std::mutex*"));
        assert!(is_cpp_hot_sync_type("std::mutex"));
        assert_eq!(clean_type_name("std::vector<ns::Counter>"), "vector");
    }

    #[test]
    fn pointee_properties_do_not_pad_or_enlarge_pointer_slots() {
        let files = parse_cpp_files(vec![CppFile { path: "types.hpp".into(), source: "struct alignas(64) Padded { std::atomic<int> counter; };\nstruct Owner {\n Padded* pointer;\n Padded value;\n};".into() }]);
        let records = collect_cpp_structs(&files, "fixture", 64);
        let owner = records
            .iter()
            .find(|record| record.name == "Owner")
            .unwrap();
        let pointer = owner
            .fields
            .iter()
            .find(|field| field.name == "pointer")
            .unwrap();
        assert_eq!(pointer.estimated_size, Some(8));
        assert!(!pointer.is_cache_padded);
        assert!(!pointer.is_hot_sync);
        assert!(
            owner
                .fields
                .iter()
                .find(|field| field.name == "value")
                .unwrap()
                .is_cache_padded
        );
    }

    #[test]
    fn numeric_alignment_is_compared_with_configured_granularity() {
        let declaration = "struct alignas(64) SharedCounters";
        assert!(has_explicit_cache_alignment(declaration, 32));
        assert!(has_explicit_cache_alignment(declaration, 64));
        assert!(!has_explicit_cache_alignment(declaration, 128));

        let widened = "struct __attribute__((aligned(128))) SharedCounters";
        assert!(has_explicit_cache_alignment(widened, 128));
    }

    #[test]
    fn malformed_template_text_does_not_panic() {
        assert_eq!(
            element_type_name("enum Type { // if type >= DATA_BACKUP_DEST and type <"),
            None
        );
    }

    #[test]
    fn static_members_do_not_participate_in_instance_layout() {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.cpp".to_string(),
            source: r#"
                struct Counters {
                    static constexpr int READY = 1;
                    static int global_count;
                    int local_count;
                };
            "#
            .to_string(),
        }]);
        let records = collect_cpp_structs(&files, "test", 64);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].fields.len(), 1);
        assert_eq!(records[0].fields[0].name, "local_count");
        assert_eq!(records[0].static_fields.len(), 2);
    }

    #[test]
    fn c11_atomic_parenthesized_fields_are_record_fields() {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.c".to_string(),
            source: "typedef struct { _Atomic(long) top; _Atomic(long) bottom; } Queue;"
                .to_string(),
        }]);
        let records = collect_cpp_structs(&files, "test", 64);
        assert_eq!(
            records.len(),
            1,
            "tree: {}",
            files[0].tree.as_ref().unwrap().root_node().to_sexp()
        );
        assert_eq!(
            records[0]
                .fields
                .iter()
                .map(|field| (field.name.as_str(), field.ty_str.as_str(), field.is_atomic))
                .collect::<Vec<_>>(),
            vec![
                ("top", "_Atomic(long)", true),
                ("bottom", "_Atomic(long)", true)
            ]
        );
    }

    #[test]
    fn template_record_keeps_fields_after_a_template_parameter_list() {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.cpp".to_string(),
            source: r#"
                template <int Role>
                class SearchTask {
                    unsigned long nodes = 0;
                    unsigned long state = 0;
                public:
                    void run() { nodes += 1; }
                };
            "#
            .to_string(),
        }]);
        let records = collect_cpp_structs(&files, "test", 64);
        let record = records
            .iter()
            .find(|record| record.name == "SearchTask")
            .expect("template record");
        assert_eq!(
            record
                .fields
                .iter()
                .map(|field| field.name.as_str())
                .collect::<Vec<_>>(),
            vec!["nodes", "state"]
        );
    }
}
