use quote::ToTokens;
use std::collections::HashMap;
use syn::spanned::Spanned;
use syn::{Attribute, Fields, ItemStruct, Visibility};

use crate::helpers::{
    cfg_is_test_only, is_atomic_type, is_cache_padded_type, is_hot_scalar_field, is_hot_sync_type,
    is_indirection_type, is_manual_padding_field, normalize_type_name,
};
use crate::rustc_layout::{RustcLayoutMap, RustcTypeLayout};
use crate::types::ItemVisibility;
use crate::types::StructKey;
use crate::types::{FieldInfo, LayoutSource, ParsedFile, StructInfo};

pub const CACHE_LINE_SIZE: usize = 64;
// Crossbeam uses target-dependent alignment, including 16-byte targets.
// Without a resolved target, a qualified library name proves only this minimum.
pub(crate) const CACHE_PADDING_MIN_ALIGN: usize = 16;

pub fn analyze_struct_layout(
    item_struct: &ItemStruct,
    src: &str,
    file: &str,
    crate_name: Option<&str>,
    module_path: &str,
    cache_line_size: usize,
) -> StructInfo {
    let repr_align_bytes = repr_align_bytes(&item_struct.attrs);
    let repr_align = repr_align_bytes
        .map(|bytes| bytes >= cache_line_size)
        .unwrap_or(false);
    let repr_packed = has_repr_packed(&item_struct.attrs);
    let repr_c = has_repr_c(&item_struct.attrs);

    let padding_imports = padding_imports_at(src, item_struct.span().start().line);
    let mut fields = Vec::new();
    let mut atomic_fields = Vec::new();
    let mut hot_scalar_fields = Vec::new();
    let mut hot_sync_fields = Vec::new();
    let mut has_cache_padded = false;
    let mut public_fields = Vec::new();

    if !matches!(item_struct.fields, Fields::Unit) {
        for (field_index, field) in item_struct.fields.iter().enumerate() {
            let ty_str = field
                .ty
                .to_token_stream()
                .to_string()
                .split_whitespace()
                .map(|token| padding_imports.get(token).map_or(token, String::as_str))
                .collect::<Vec<_>>()
                .join(" ");
            let name = field
                .ident
                .as_ref()
                .map(|x| x.to_string())
                .unwrap_or_else(|| field_index.to_string());

            let is_atomic = is_atomic_type(&ty_str);
            let is_hot = is_hot_scalar_field(&name, &ty_str);
            let is_hot_sync = is_hot_sync_type(&ty_str);
            let is_manual_padding = is_manual_padding_field(&name, &ty_str);
            let is_indirect = is_indirection_type(&ty_str);
            let estimated_size = estimate_type_size(&ty_str);
            // A wrapper that isolates a 64-byte line is not sufficient when
            // the analysis is intentionally configured for 128-byte
            // interference granularity.
            let is_padded = cache_padding_guarantee(&ty_str)
                .is_some_and(|guarantee| guarantee >= cache_line_size);
            let visibility = item_visibility(&field.vis);

            if is_padded {
                has_cache_padded = true;
            }
            if visibility.is_exposed() {
                public_fields.push(name.clone());
            }
            if is_atomic {
                atomic_fields.push(name.clone());
            }
            if is_hot {
                hot_scalar_fields.push(name.clone());
            }
            if is_hot_sync {
                hot_sync_fields.push(name.clone());
            }

            fields.push(FieldInfo {
                name,
                ty_str,
                estimated_size,
                offset: None,
                is_atomic,
                is_hot_scalar: is_hot,
                is_hot_sync,
                is_cache_padded: is_padded,
                is_manual_padding,
                is_indirect,
                visibility,
            });
        }
    }

    let total_estimated_size =
        estimated_struct_size(&fields, repr_align_bytes, repr_c, repr_packed);

    assign_estimated_offsets(&mut fields, repr_c, repr_packed);
    let cache_line_groups =
        compute_cache_line_groups(&fields, repr_c, repr_packed, cache_line_size);
    // Source estimates are useful may-alias witnesses, but are never exact:
    // repr(Rust) may reorder fields and repr(C) still depends on target ABI.
    let cache_line_groups_precise = false;
    let layout_source = if repr_c {
        LayoutSource::ReprCEstimate
    } else {
        LayoutSource::RustDefaultEstimate
    };

    let line = item_struct.span().start().line;

    StructInfo {
        name: item_struct.ident.to_string(),
        module_path: module_path.to_string(),
        file: file.to_string(),
        line,
        crate_name: crate_name.map(|s| s.to_string()),
        cache_line_size,
        fields,
        repr_align_bytes,
        repr_align,
        repr_packed,
        repr_c,
        has_cache_padded,
        atomic_fields,
        hot_scalar_fields,
        hot_sync_fields,
        total_estimated_size,
        cache_line_groups,
        cache_line_groups_precise,
        layout_source,
        visibility: item_visibility(&item_struct.vis),
        public_fields,
    }
}

fn item_visibility(vis: &Visibility) -> ItemVisibility {
    match vis {
        Visibility::Public(_) => ItemVisibility::Public,
        Visibility::Restricted(_) => ItemVisibility::Restricted,
        Visibility::Inherited => ItemVisibility::Private,
    }
}

/// Resolve documented external wrapper contracts through explicit imports.
/// Unresolved/local names carry no layout guarantee.
fn padding_imports_at(source: &str, line: usize) -> HashMap<String, String> {
    fn use_names(tree: &syn::UseTree, prefix: &str, imports: &mut HashMap<String, String>) {
        match tree {
            syn::UseTree::Path(path) => {
                use_names(&path.tree, &format!("{prefix}{}::", path.ident), imports)
            }
            syn::UseTree::Name(name) => {
                let path = format!("{prefix}{}", name.ident);
                if is_cache_padded_type(&path) {
                    imports.insert(name.ident.to_string(), path);
                }
            }
            syn::UseTree::Rename(name) => {
                let path = format!("{prefix}{}", name.ident);
                if is_cache_padded_type(&path) {
                    imports.insert(name.rename.to_string(), path);
                }
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    use_names(item, prefix, imports);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }
    fn in_scope(items: &[syn::Item], line: usize) -> HashMap<String, String> {
        let mut imports = HashMap::new();
        for item in items {
            if let syn::Item::Use(item) = item {
                use_names(&item.tree, "", &mut imports);
            }
        }
        for item in items {
            let local = match item {
                syn::Item::Struct(item) => Some(&item.ident),
                syn::Item::Enum(item) => Some(&item.ident),
                syn::Item::Type(item) => Some(&item.ident),
                _ => None,
            };
            if let Some(local) = local {
                imports.remove(&local.to_string());
            }
            if let syn::Item::Mod(module) = item
                && module.span().start().line <= line
                && line <= module.span().end().line
                && let Some((_, items)) = &module.content
            {
                // Parent imports are not implicitly in a child module's scope.
                return in_scope(items, line);
            }
        }
        imports
    }
    syn::parse_file(source)
        .map(|file| in_scope(&file.items, line))
        .unwrap_or_default()
}

#[derive(Clone, Debug, Default)]
struct LocalTypeSummary {
    contains_hot_payload: bool,
    total_size: Option<usize>,
    cache_line_aligned: bool,
    alignment: Option<usize>,
}

pub fn enrich_structs_with_type_registry(structs: &mut [StructInfo], cache_line_size: usize) {
    let mut summaries: HashMap<StructKey, LocalTypeSummary> = structs
        .iter()
        .map(|si| {
            (
                StructKey::from_struct(si),
                summarize_local_type(si, &HashMap::new(), cache_line_size),
            )
        })
        .collect();

    for _ in 0..8 {
        let mut changed = false;
        for si in structs.iter() {
            let next = summarize_local_type(si, &summaries, cache_line_size);
            let entry = summaries.entry(StructKey::from_struct(si)).or_default();
            if entry.contains_hot_payload != next.contains_hot_payload
                || entry.total_size != next.total_size
                || entry.cache_line_aligned != next.cache_line_aligned
                || entry.alignment != next.alignment
            {
                *entry = next;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    for si in structs.iter_mut() {
        let crate_name = si
            .crate_name
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        let module_path = si.module_path.clone();
        for field in &mut si.fields {
            let Some(type_name) = normalize_type_name(&field.ty_str) else {
                continue;
            };
            let Some(summary) =
                local_type_summary_for_type(&crate_name, &module_path, &type_name, &summaries)
            else {
                continue;
            };

            if field.is_indirect {
                continue;
            }
            field.is_cache_padded = summary.cache_line_aligned;

            if !field.is_cache_padded && summary.contains_hot_payload {
                field.is_hot_sync = true;
            }
            let local_type_size = summary
                .total_size
                .or(summary.alignment)
                .map(|size| size.max(summary.alignment.unwrap_or(1)));
            if let Some(local_type_size) = local_type_size {
                field.estimated_size = Some(local_type_size);
            }
        }

        recompute_struct_derived_fields(si, cache_line_size);
    }
}

pub fn apply_rustc_layouts(
    structs: &mut [StructInfo],
    layouts: &RustcLayoutMap,
    cache_line_size: usize,
) {
    let short_name_counts = structs.iter().fold(HashMap::new(), |mut counts, si| {
        *counts
            .entry((si.crate_name.clone(), si.name.clone()))
            .or_insert(0usize) += 1;
        counts
    });
    for si in structs {
        let crate_name = si
            .crate_name
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        let key = StructKey::from_struct(si);
        let Some(layout) = layouts.get(&key).or_else(|| {
            (short_name_counts.get(&(si.crate_name.clone(), si.name.clone())) == Some(&1))
                .then(|| layouts.get(&StructKey::new(crate_name, "", si.name.clone())))
                .flatten()
        }) else {
            continue;
        };
        if !rustc_layout_matches_fields(si, layout) {
            continue;
        }

        let mut fields_by_name: HashMap<String, FieldInfo> = si
            .fields
            .iter()
            .cloned()
            .map(|field| (field.name.clone(), field))
            .collect();
        let mut ordered_fields = Vec::new();
        for layout_field in &layout.fields {
            let Some(mut field) = fields_by_name.remove(&layout_field.name) else {
                continue;
            };
            field.estimated_size = Some(layout_field.size);
            field.offset = Some(layout_field.offset);
            ordered_fields.push(field);
        }
        if !fields_by_name.is_empty() || ordered_fields.len() != si.fields.len() {
            continue;
        }

        si.fields = ordered_fields;
        recompute_struct_derived_fields(si, cache_line_size);
        for (field, layout_field) in si.fields.iter_mut().zip(&layout.fields) {
            field.estimated_size = Some(layout_field.size);
            field.offset = Some(layout_field.offset);
        }
        si.total_estimated_size = Some(layout.total_size);
        si.cache_line_groups = compute_offset_groups(layout, cache_line_size);
        si.cache_line_groups_precise = true;
        si.layout_source = LayoutSource::RustcExact;
    }
}

fn summarize_local_type(
    si: &StructInfo,
    summaries: &HashMap<StructKey, LocalTypeSummary>,
    cache_line_size: usize,
) -> LocalTypeSummary {
    let mut contains_hot_payload = si.fields.iter().any(|field| {
        (field.is_atomic || field.is_hot_sync || field.is_hot_scalar) && !field.is_cache_padded
    });
    let mut total_size = 0usize;
    let mut has_unknown_size = false;

    for field in &si.fields {
        if let Some(type_name) = normalize_type_name(&field.ty_str)
            && let Some(summary) = local_type_summary_for_field(si, &type_name, summaries)
        {
            contains_hot_payload |= summary.contains_hot_payload && !summary.cache_line_aligned;
            if let Some(size) = summary.total_size.or(field.estimated_size) {
                total_size += size;
            } else {
                has_unknown_size = true;
            }
            continue;
        }

        if let Some(size) = field.estimated_size {
            total_size += size;
        } else {
            has_unknown_size = true;
        }
    }

    LocalTypeSummary {
        contains_hot_payload,
        total_size: align_struct_size(
            if has_unknown_size {
                si.total_estimated_size
            } else {
                Some(total_size)
            },
            si.repr_align_bytes,
        ),
        cache_line_aligned: si
            .repr_align_bytes
            .is_some_and(|alignment| alignment >= cache_line_size),
        alignment: si.repr_align_bytes,
    }
}

fn local_type_summary_for_field<'a>(
    si: &StructInfo,
    type_name: &str,
    summaries: &'a HashMap<StructKey, LocalTypeSummary>,
) -> Option<&'a LocalTypeSummary> {
    let crate_name = si
        .crate_name
        .clone()
        .unwrap_or_else(|| "unknown".to_string());
    local_type_summary_for_type(&crate_name, &si.module_path, type_name, summaries)
}

fn local_type_summary_for_type<'a>(
    crate_name: &str,
    module_path: &str,
    type_name: &str,
    summaries: &'a HashMap<StructKey, LocalTypeSummary>,
) -> Option<&'a LocalTypeSummary> {
    summaries
        .get(&StructKey::new(
            crate_name.to_string(),
            module_path.to_string(),
            type_name.to_string(),
        ))
        .or_else(|| {
            summaries.get(&StructKey::new(
                crate_name.to_string(),
                String::new(),
                type_name.to_string(),
            ))
        })
}

pub(crate) fn ablate_protection_evidence(si: &mut StructInfo, cache_line_size: usize) {
    si.repr_align_bytes = None;
    si.repr_align = false;
    si.has_cache_padded = false;
    for field in &mut si.fields {
        if field.is_cache_padded || field.is_manual_padding {
            // Once the protection recognizer is removed, the wrapper/padding
            // payload size is no longer known to the layout model.  Retain the
            // field but fall back to the ordinary unknown-size estimate.
            field.estimated_size = None;
        }
        field.is_cache_padded = false;
        field.is_manual_padding = false;
    }
    recompute_struct_derived_fields(si, cache_line_size);
}

fn recompute_struct_derived_fields(si: &mut StructInfo, cache_line_size: usize) {
    si.has_cache_padded = si.fields.iter().any(|field| field.is_cache_padded);
    si.atomic_fields = si
        .fields
        .iter()
        .filter(|field| field.is_atomic && !field.is_cache_padded)
        .map(|field| field.name.clone())
        .collect();
    si.hot_scalar_fields = si
        .fields
        .iter()
        .filter(|field| field.is_hot_scalar && !field.is_cache_padded)
        .map(|field| field.name.clone())
        .collect();
    si.hot_sync_fields = si
        .fields
        .iter()
        .filter(|field| field.is_hot_sync && !field.is_cache_padded)
        .map(|field| field.name.clone())
        .collect();
    si.total_estimated_size =
        estimated_struct_size(&si.fields, si.repr_align_bytes, si.repr_c, si.repr_packed);
    assign_estimated_offsets(&mut si.fields, si.repr_c, si.repr_packed);
    si.cache_line_groups =
        compute_cache_line_groups(&si.fields, si.repr_c, si.repr_packed, cache_line_size);
    si.cache_line_groups_precise = false;
    if si.layout_source != LayoutSource::RustcExact {
        si.layout_source = if si.repr_c {
            LayoutSource::ReprCEstimate
        } else {
            LayoutSource::RustDefaultEstimate
        };
    }
}

fn rustc_layout_matches_fields(si: &StructInfo, layout: &RustcTypeLayout) -> bool {
    if si.fields.len() != layout.fields.len() {
        return false;
    }
    let declared: std::collections::HashSet<&str> =
        si.fields.iter().map(|field| field.name.as_str()).collect();
    let compiled: std::collections::HashSet<&str> = layout
        .fields
        .iter()
        .map(|field| field.name.as_str())
        .collect();
    declared == compiled
}

fn compute_offset_groups(layout: &RustcTypeLayout, cache_line_size: usize) -> Vec<Vec<String>> {
    let mut by_line: HashMap<usize, Vec<String>> = HashMap::new();
    for field in &layout.fields {
        let start_line = field.offset / cache_line_size;
        let end_line = if field.size == 0 {
            start_line
        } else {
            (field.offset + field.size - 1) / cache_line_size
        };
        for line in start_line..=end_line {
            by_line.entry(line).or_default().push(field.name.clone());
        }
    }

    let mut lines: Vec<_> = by_line.into_iter().collect();
    lines.sort_by_key(|(line, _)| *line);
    lines.into_iter().map(|(_, fields)| fields).collect()
}

fn compute_cache_line_groups(
    fields: &[FieldInfo],
    repr_c: bool,
    repr_packed: bool,
    cache_line_size: usize,
) -> Vec<Vec<String>> {
    if repr_c {
        compute_repr_c_groups(fields, repr_packed, cache_line_size)
    } else {
        compute_default_groups(fields, cache_line_size)
    }
}

fn assign_estimated_offsets(fields: &mut [FieldInfo], repr_c: bool, repr_packed: bool) {
    if repr_c {
        let offsets = compute_repr_c_offsets(fields, repr_packed);
        for (field, offset) in fields.iter_mut().zip(offsets) {
            field.offset = Some(offset);
        }
    } else {
        for field in fields {
            field.offset = None;
        }
    }
}

fn compute_repr_c_offsets(fields: &[FieldInfo], repr_packed: bool) -> Vec<usize> {
    let mut offsets = Vec::with_capacity(fields.len());
    let mut current_offset: usize = 0;

    for field in fields {
        let size = field.estimated_size.unwrap_or(8);
        let align = if repr_packed {
            1
        } else {
            estimate_type_alignment(&field.ty_str).unwrap_or(1)
        };
        let aligned_offset = align_up(current_offset, align);
        offsets.push(aligned_offset);
        current_offset = aligned_offset.saturating_add(size);
    }

    offsets
}

fn compute_repr_c_groups(
    fields: &[FieldInfo],
    repr_packed: bool,
    cache_line_size: usize,
) -> Vec<Vec<String>> {
    let offsets = compute_repr_c_offsets(fields, repr_packed);
    cache_line_groups_from_offsets(fields, &offsets, cache_line_size)
}

fn compute_default_groups(fields: &[FieldInfo], cache_line_size: usize) -> Vec<Vec<String>> {
    let _ = cache_line_size;
    // repr(Rust) does not guarantee declaration order. The only sound
    // source-level may-alias group is therefore the whole record.
    vec![fields.iter().map(|field| field.name.clone()).collect()]
}

fn estimated_struct_size(
    fields: &[FieldInfo],
    repr_align_bytes: Option<usize>,
    repr_c: bool,
    repr_packed: bool,
) -> Option<usize> {
    if !repr_c {
        let natural_size = fields
            .iter()
            .try_fold(0usize, |total, field| Some(total + field.estimated_size?))?;
        return align_struct_size(Some(natural_size), repr_align_bytes);
    }

    let offsets = compute_repr_c_offsets(fields, repr_packed);
    let end = fields
        .iter()
        .zip(offsets)
        .try_fold(0usize, |end, (field, offset)| {
            Some(end.max(offset.saturating_add(field.estimated_size?)))
        })?;
    let natural_alignment = if repr_packed {
        1
    } else {
        fields
            .iter()
            .filter_map(|field| estimate_type_alignment(&field.ty_str))
            .max()
            .unwrap_or(1)
    };
    align_struct_size(
        Some(end),
        Some(natural_alignment.max(repr_align_bytes.unwrap_or(1))),
    )
}

fn cache_line_groups_from_offsets(
    fields: &[FieldInfo],
    offsets: &[usize],
    cache_line_size: usize,
) -> Vec<Vec<String>> {
    let mut by_line: HashMap<usize, Vec<String>> = HashMap::new();
    for (field, offset) in fields.iter().zip(offsets) {
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

fn align_up(value: usize, alignment: usize) -> usize {
    value.div_ceil(alignment.max(1)) * alignment.max(1)
}

fn estimate_type_alignment(ty: &str) -> Option<usize> {
    let ty = ty.trim();
    match ty {
        "bool" | "u8" | "i8" => Some(1),
        "u16" | "i16" => Some(2),
        "u32" | "i32" | "f32" => Some(4),
        "u64" | "i64" | "f64" | "usize" | "isize" => Some(8),
        "u128" | "i128" => Some(16),
        _ if is_cache_padded_type(ty) => Some(CACHE_PADDING_MIN_ALIGN),
        _ => estimate_complex_type_size(ty).map(|size| size.next_power_of_two().min(8)),
    }
}

fn align_struct_size(size: Option<usize>, alignment: Option<usize>) -> Option<usize> {
    let size = size?;
    let Some(alignment) = alignment.filter(|alignment| *alignment > 1) else {
        return Some(size);
    };
    if size == 0 {
        return Some(alignment);
    }
    Some(size.div_ceil(alignment) * alignment)
}

pub fn estimate_type_size(ty: &str) -> Option<usize> {
    let ty = ty.trim();
    match ty {
        "bool" => Some(1),
        "u8" | "i8" => Some(1),
        "u16" | "i16" => Some(2),
        "u32" | "i32" | "f32" => Some(4),
        "u64" | "i64" | "f64" | "usize" | "isize" => Some(8),
        "u128" | "i128" => Some(16),
        _ => estimate_complex_type_size(ty),
    }
}

fn estimate_complex_type_size(ty: &str) -> Option<usize> {
    if let Some(size) = estimate_byte_array_size(ty) {
        return Some(size);
    }
    if ty.starts_with('&')
        || ty.starts_with("* const")
        || ty.starts_with("* mut")
        || ty.contains("Box <")
        || ty.contains("Box<")
        || ty.contains("Arc <")
        || ty.contains("Arc<")
        || ty.contains("Rc <")
        || ty.contains("Rc<")
    {
        return Some(8);
    }
    // Resolve the outer representation before its generic payload. Pointer
    // slots and opaque wrappers must not inherit the payload's byte size.
    if let Some(guarantee) = cache_padding_guarantee(ty) {
        return Some(guarantee);
    }
    match normalize_type_name(ty).as_deref() {
        Some("AtomicBool" | "AtomicU8" | "AtomicI8") => return Some(1),
        Some("AtomicU16" | "AtomicI16") => return Some(2),
        Some("AtomicU32" | "AtomicI32") => return Some(4),
        Some("AtomicU64" | "AtomicI64" | "AtomicUsize" | "AtomicIsize" | "AtomicPtr") => {
            return Some(8);
        }
        _ => {}
    }
    if ty.contains("NonNull") || ty.contains("NonZero") {
        return Some(8);
    }
    None
}

/// Return the target-independent minimum for explicitly resolved library paths.
fn cache_padding_guarantee(ty: &str) -> Option<usize> {
    is_cache_padded_type(ty).then_some(CACHE_PADDING_MIN_ALIGN)
}

fn estimate_byte_array_size(ty: &str) -> Option<usize> {
    let compact: String = ty.chars().filter(|c| !c.is_whitespace()).collect();
    if !compact.starts_with("[u8;") {
        return None;
    }

    compact
        .trim_start_matches("[u8;")
        .trim_end_matches(']')
        .parse::<usize>()
        .ok()
}

pub fn has_repr_align(attrs: &[Attribute]) -> bool {
    repr_align_bytes(attrs).is_some()
}

pub fn repr_align_bytes(attrs: &[Attribute]) -> Option<usize> {
    let unconditional = attrs
        .iter()
        .filter_map(attr_repr_align_bytes)
        .max()
        .unwrap_or(0);
    let mut conditional = Vec::new();
    for attr in attrs.iter().filter(|attr| attr.path().is_ident("cfg_attr")) {
        let Ok(options) = attr.parse_args_with(
            syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated,
        ) else {
            continue;
        };
        let Some(condition) = options.first() else {
            continue;
        };
        let alignment = options
            .iter()
            .skip(1)
            .filter_map(meta_repr_align_bytes)
            .max();
        if let Some(alignment) = alignment {
            conditional.push((condition.clone(), alignment));
        }
    }
    if conditional.is_empty() {
        return (unconditional > 0).then_some(unconditional);
    }
    // Without a target selection, only an alignment guaranteed by every cfg
    // branch may suppress a candidate. Architecture values are mutually
    // exclusive; other cfg atoms are conservatively treated as independent.
    let mut architectures = Vec::new();
    let mut atoms = Vec::new();
    for (condition, _) in &conditional {
        collect_alignment_cfg_atoms(condition, &mut architectures, &mut atoms);
    }
    architectures.sort();
    architectures.dedup();
    atoms.sort();
    atoms.dedup();
    if atoms.len() > 6 || architectures.len() > 32 {
        return (unconditional > 0).then_some(unconditional);
    }
    let mut guaranteed = usize::MAX;
    for architecture in architectures.iter().map(Some).chain(std::iter::once(None)) {
        for assignment in 0..(1usize << atoms.len()) {
            let alignment = conditional
                .iter()
                .filter(|(condition, _)| {
                    alignment_cfg_holds(
                        condition,
                        architecture.map(String::as_str),
                        &atoms,
                        assignment,
                    )
                })
                .map(|(_, alignment)| *alignment)
                .max()
                .unwrap_or(0)
                .max(unconditional);
            guaranteed = guaranteed.min(alignment);
        }
    }
    (guaranteed > 0).then_some(guaranteed)
}

fn cfg_architecture(meta: &syn::Meta) -> Option<String> {
    let syn::Meta::NameValue(value) = meta else {
        return None;
    };
    if !value.path.is_ident("target_arch") {
        return None;
    }
    let syn::Expr::Lit(value) = &value.value else {
        return None;
    };
    let syn::Lit::Str(value) = &value.lit else {
        return None;
    };
    Some(value.value())
}

fn cfg_operands(
    meta: &syn::Meta,
) -> Option<syn::punctuated::Punctuated<syn::Meta, syn::Token![,]>> {
    let syn::Meta::List(list) = meta else {
        return None;
    };
    if !["all", "any", "not"]
        .iter()
        .any(|name| list.path.is_ident(name))
    {
        return None;
    }
    list.parse_args_with(syn::punctuated::Punctuated::parse_terminated)
        .ok()
}

fn collect_alignment_cfg_atoms(
    meta: &syn::Meta,
    architectures: &mut Vec<String>,
    atoms: &mut Vec<String>,
) {
    if let Some(architecture) = cfg_architecture(meta) {
        architectures.push(architecture);
    } else if let Some(operands) = cfg_operands(meta) {
        for operand in &operands {
            collect_alignment_cfg_atoms(operand, architectures, atoms);
        }
    } else {
        atoms.push(meta.to_token_stream().to_string());
    }
}

fn alignment_cfg_holds(
    meta: &syn::Meta,
    architecture: Option<&str>,
    atoms: &[String],
    assignment: usize,
) -> bool {
    if let Some(value) = cfg_architecture(meta) {
        return architecture == Some(value.as_str());
    }
    if let Some(operands) = cfg_operands(meta) {
        if meta.path().is_ident("all") {
            return operands
                .iter()
                .all(|operand| alignment_cfg_holds(operand, architecture, atoms, assignment));
        }
        if meta.path().is_ident("any") {
            return operands
                .iter()
                .any(|operand| alignment_cfg_holds(operand, architecture, atoms, assignment));
        }
        return operands.len() == 1
            && !alignment_cfg_holds(&operands[0], architecture, atoms, assignment);
    }
    atoms
        .iter()
        .position(|atom| *atom == meta.to_token_stream().to_string())
        .is_some_and(|index| assignment & (1 << index) != 0)
}

fn repr_options(
    attr: &Attribute,
) -> Option<syn::punctuated::Punctuated<syn::Meta, syn::Token![,]>> {
    if !attr.path().is_ident("repr") {
        return None;
    }
    attr.parse_args_with(syn::punctuated::Punctuated::parse_terminated)
        .ok()
}

fn attr_repr_align_bytes(attr: &Attribute) -> Option<usize> {
    meta_repr_align_bytes(&attr.meta)
}

fn meta_repr_align_bytes(meta: &syn::Meta) -> Option<usize> {
    let syn::Meta::List(repr) = meta else {
        return None;
    };
    if !repr.path.is_ident("repr") {
        return None;
    }
    let options = repr
        .parse_args_with(syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated)
        .ok()?;
    options
        .iter()
        .filter_map(|option| {
            let syn::Meta::List(list) = option else {
                return None;
            };
            if !list.path.is_ident("align") {
                return None;
            }
            list.parse_args::<syn::LitInt>().ok()?.base10_parse().ok()
        })
        .max()
}

pub fn has_repr_packed(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .filter_map(repr_options)
        .flatten()
        .any(|option| option.path().is_ident("packed"))
}

fn has_repr_c(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .filter_map(repr_options)
        .flatten()
        .any(|option| matches!(option, syn::Meta::Path(path) if path.is_ident("C")))
}

struct StructCollector<'a> {
    source: &'a str,
    file: &'a str,
    crate_name: Option<&'a str>,
    base_module_path: &'a str,
    cache_line_size: usize,
    module_stack: Vec<String>,
    structs: Vec<StructInfo>,
}

impl StructCollector<'_> {
    fn current_module_path(&self) -> String {
        if self.module_stack.is_empty() {
            self.base_module_path.to_string()
        } else if self.base_module_path.is_empty() {
            self.module_stack.join("::")
        } else {
            format!(
                "{}::{}",
                self.base_module_path,
                self.module_stack.join("::")
            )
        }
    }
}

impl<'ast> syn::visit::Visit<'ast> for StructCollector<'_> {
    fn visit_item_struct(&mut self, node: &'ast syn::ItemStruct) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        let module_path = self.current_module_path();
        self.structs.push(analyze_struct_layout(
            node,
            self.source,
            self.file,
            self.crate_name,
            &module_path,
            self.cache_line_size,
        ));
    }

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        let Some((_, items)) = &node.content else {
            return;
        };
        self.module_stack.push(node.ident.to_string());
        for item in items {
            self.visit_item(item);
        }
        self.module_stack.pop();
    }
}

pub(crate) fn collect_structs_from_file(
    pf: &ParsedFile,
    cache_line_size: usize,
) -> Vec<StructInfo> {
    let mut collector = StructCollector {
        source: &pf.source,
        file: &pf.path,
        crate_name: pf.crate_name.as_deref(),
        base_module_path: &pf.module_path,
        cache_line_size,
        module_stack: Vec::new(),
        structs: Vec::new(),
    };
    syn::visit::Visit::visit_file(&mut collector, &pf.ast);
    collector.structs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conditional_alignment_requires_coverage_of_every_cfg_branch() {
        for (attrs, expected) in [
            (
                r#"#[cfg_attr(target_arch = "x86_64", repr(align(128)))]"#,
                None,
            ),
            (
                r#"#[cfg_attr(target_arch = "x86_64", repr(align(128)))] #[cfg_attr(not(target_arch = "x86_64"), repr(align(64)))]"#,
                Some(64),
            ),
            (
                r#"#[cfg_attr(feature = "padded", repr(align(128)))] #[cfg_attr(not(feature = "padded"), repr(align(32)))]"#,
                Some(32),
            ),
            (
                r#"#[repr(align(64))] #[cfg_attr(feature = "padded", repr(align(128)))]"#,
                Some(64),
            ),
            (
                r#"#[cfg_attr(any(target_arch = "aarch64", target_arch = "x86_64"), repr(align(128)))] #[cfg_attr(not(any(target_arch = "aarch64", target_arch = "x86_64")), repr(align(64)))]"#,
                Some(64),
            ),
        ] {
            let item: syn::ItemStruct =
                syn::parse_str(&format!("{attrs} struct State {{ value: u8 }}")).unwrap();
            assert_eq!(repr_align_bytes(&item.attrs), expected, "{attrs}");
        }
    }

    #[test]
    fn repr_attributes_are_parsed_as_syntax_including_combined_options() {
        for (attribute, c, packed, align) in [
            ("#[repr(C)]", true, false, None),
            ("#[repr(C, align(128))]", true, false, Some(128)),
            ("#[repr(align(32), C)]", true, false, Some(32)),
            ("#[repr(C, packed(2))]", true, true, None),
            ("#[repr(packed)]", false, true, None),
            (r##"#[doc = "#[repr(C, align(128))]"]"##, false, false, None),
        ] {
            let item: syn::ItemStruct =
                syn::parse_str(&format!("{attribute} struct State {{ value: u8 }}")).unwrap();
            assert_eq!(has_repr_c(&item.attrs), c, "{attribute}");
            assert_eq!(has_repr_packed(&item.attrs), packed, "{attribute}");
            assert_eq!(repr_align_bytes(&item.attrs), align, "{attribute}");
        }
    }

    #[test]
    fn test_estimate_type_size_primitives() {
        assert_eq!(estimate_type_size("u8"), Some(1));
        assert_eq!(estimate_type_size("u64"), Some(8));
        assert_eq!(estimate_type_size("bool"), Some(1));
        assert_eq!(estimate_type_size("usize"), Some(8));
    }

    #[test]
    fn test_estimate_type_size_atomics() {
        assert_eq!(estimate_type_size("AtomicU64"), Some(8));
        assert_eq!(estimate_type_size("AtomicBool"), Some(1));
        assert_eq!(estimate_type_size("AtomicUsize"), Some(8));
        assert_eq!(estimate_type_size("CachePadded<AtomicBool>"), None);
        assert_eq!(
            estimate_type_size("crossbeam_utils::CachePadded<AtomicBool>"),
            Some(CACHE_PADDING_MIN_ALIGN)
        );
        assert_eq!(estimate_type_size("Box<[CachePadded<AtomicU64>]>"), Some(8));
    }

    #[test]
    fn test_estimate_type_size_unknown() {
        assert_eq!(estimate_type_size("MyCustomType"), None);
        assert_eq!(estimate_type_size("String"), None);
    }

    #[test]
    fn test_zero_sized_field_layout_does_not_underflow() {
        let fields = vec![
            FieldInfo {
                name: "marker".to_string(),
                ty_str: "[u8; 0]".to_string(),
                estimated_size: Some(0),
                offset: None,
                is_atomic: false,
                is_hot_scalar: false,
                is_hot_sync: false,
                is_cache_padded: false,
                is_manual_padding: false,
                is_indirect: false,
                visibility: crate::types::ItemVisibility::Private,
            },
            FieldInfo {
                name: "value".to_string(),
                ty_str: "u64".to_string(),
                estimated_size: Some(8),
                offset: None,
                is_atomic: false,
                is_hot_scalar: false,
                is_hot_sync: false,
                is_cache_padded: false,
                is_manual_padding: false,
                is_indirect: false,
                visibility: crate::types::ItemVisibility::Private,
            },
        ];

        assert_eq!(
            compute_repr_c_groups(&fields, false, CACHE_LINE_SIZE),
            vec![vec!["marker".to_string(), "value".to_string()]]
        );
    }

    #[test]
    fn local_aligned_wrapper_uses_configured_interference_granularity() {
        let source = r#"
#[repr(align(64))]
struct Padded<T>(T);
struct Ring {
    head: Padded<AtomicUsize>,
    flush: Padded<AtomicUsize>,
}
"#;
        let ast = syn::parse_file(source).expect("parse aligned-wrapper fixture");

        let analyze = |cache_line_size| {
            let mut structs: Vec<_> = ast
                .items
                .iter()
                .filter_map(|item| match item {
                    syn::Item::Struct(item_struct) => Some(analyze_struct_layout(
                        item_struct,
                        source,
                        "src/lib.rs",
                        Some("fixture"),
                        "",
                        cache_line_size,
                    )),
                    _ => None,
                })
                .collect();
            enrich_structs_with_type_registry(&mut structs, cache_line_size);
            structs
                .into_iter()
                .find(|info| info.name == "Ring")
                .expect("Ring layout")
        };

        let at_64 = analyze(64);
        assert!(
            at_64
                .fields
                .iter()
                .filter(|field| matches!(field.name.as_str(), "head" | "flush"))
                .all(|field| field.is_cache_padded && field.estimated_size == Some(64))
        );

        let at_128 = analyze(128);
        assert!(
            at_128
                .fields
                .iter()
                .filter(|field| matches!(field.name.as_str(), "head" | "flush"))
                .all(|field| !field.is_cache_padded && field.estimated_size == Some(64))
        );
        assert!(at_128.cache_line_groups.iter().any(|group| {
            group.contains(&"head".to_string()) && group.contains(&"flush".to_string())
        }));
    }
}
