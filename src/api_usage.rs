use std::collections::{HashMap, HashSet};

use quote::ToTokens;
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{FnArg, ImplItemFn, ItemFn, ItemImpl, ReturnType, Type, Visibility};

use crate::helpers::normalize_type_name;
use crate::module_visibility::{ModuleKey, externally_reachable_modules};
use crate::types::{
    ApiUsageEvidence, ApiUsageEvidenceSet, ApiUsageKind, ItemVisibility, ParsedFile, StructInfo,
    StructKey,
};

pub fn collect_api_usage_evidence(
    files: &[ParsedFile],
    structs: &[StructInfo],
) -> HashMap<StructKey, ApiUsageEvidenceSet> {
    let index = ApiUsageIndex::new(structs);
    let reachable_modules = externally_reachable_modules(files);
    let externally_reachable_types = structs
        .iter()
        .filter(|record| record.visibility.is_externally_exposed())
        .map(StructKey::from_struct)
        .collect::<HashSet<_>>();
    let mut evidence_map: HashMap<StructKey, ApiUsageEvidenceSet> = HashMap::new();

    for si in structs {
        let key = StructKey::from_struct(si);

        if si.visibility.is_externally_exposed() {
            evidence_map
                .entry(key.clone())
                .or_default()
                .evidence
                .push(ApiUsageEvidence {
                    kind: ApiUsageKind::PublicStruct,
                    description: format!(
                        "API exposure: struct '{}' has {:?} visibility",
                        si.name, si.visibility
                    ),
                    file: si.file.clone(),
                    line: si.line,
                    score: 0.20,
                });
        }

        if !si.public_fields.is_empty() {
            evidence_map
                .entry(key.clone())
                .or_default()
                .evidence
                .push(ApiUsageEvidence {
                    kind: ApiUsageKind::PublicField,
                    description: format!(
                        "API exposure: public fields on '{}': {}",
                        si.name,
                        si.public_fields.join(", ")
                    ),
                    file: si.file.clone(),
                    line: si.line,
                    score: 0.25,
                });
        }

        if semantic_name_suggests_hot_use(&si.name)
            || si
                .fields
                .iter()
                .any(|field| semantic_name_suggests_hot_use(&field.name))
        {
            evidence_map
                .entry(key)
                .or_default()
                .evidence
                .push(ApiUsageEvidence {
                    kind: ApiUsageKind::SemanticTypeOrFieldName,
                    description: format!(
                        "API semantic hint: '{}' or its fields look like hot runtime state",
                        si.name
                    ),
                    file: si.file.clone(),
                    line: si.line,
                    score: 0.35,
                });
        }
    }

    for pf in files {
        let crate_name = pf
            .crate_name
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        let mut collector = ApiUsageCollector {
            file: &pf.path,
            crate_name,
            module_path: pf.module_path.clone(),
            reachable_modules: &reachable_modules,
            externally_reachable_types: &externally_reachable_types,
            index: &index,
            current_impl_type: None,
            evidence_map: &mut evidence_map,
        };
        collector.visit_file(&pf.ast);
    }

    evidence_map
}

struct ApiUsageCollector<'a> {
    file: &'a str,
    crate_name: String,
    module_path: String,
    reachable_modules: &'a HashSet<ModuleKey>,
    externally_reachable_types: &'a HashSet<StructKey>,
    index: &'a ApiUsageIndex,
    current_impl_type: Option<String>,
    evidence_map: &'a mut HashMap<StructKey, ApiUsageEvidenceSet>,
}

impl ApiUsageCollector<'_> {
    fn current_module_is_externally_reachable(&self) -> bool {
        self.reachable_modules
            .contains(&(self.crate_name.clone(), self.module_path.clone()))
    }

    fn current_impl_is_externally_reachable(&self) -> bool {
        self.current_impl_type
            .as_deref()
            .and_then(|name| self.resolve_struct_key(name))
            .is_some_and(|key| self.externally_reachable_types.contains(&key))
    }

    fn resolve_struct_key(&self, struct_name: &str) -> Option<StructKey> {
        self.index
            .resolve(&self.crate_name, &self.module_path, struct_name)
    }

    fn add_evidence(&mut self, type_ref: &TypeRef, item: ApiUsageEvidence) {
        self.evidence_map
            .entry(type_ref.key.clone())
            .or_default()
            .evidence
            .push(item);
    }

    fn inspect_public_signature(
        &mut self,
        fn_name: &str,
        inputs: &syn::punctuated::Punctuated<FnArg, syn::token::Comma>,
        output: &ReturnType,
        line: usize,
        impl_type: Option<&str>,
    ) {
        let mut type_refs = Vec::new();
        for input in inputs {
            match input {
                FnArg::Receiver(receiver) => {
                    if let Some(impl_ty) = impl_type {
                        let Some(key) = self.resolve_struct_key(impl_ty) else {
                            continue;
                        };
                        type_refs.push(TypeRef {
                            key,
                            struct_name: impl_ty.to_string(),
                            via_arc: receiver_type_contains_wrapper(receiver, "Arc"),
                            via_raw_pointer: false,
                            by_reference: receiver.reference.is_some(),
                            is_receiver: true,
                            receiver_is_exclusive: receiver_is_exclusive(receiver),
                        });
                    }
                }
                FnArg::Typed(pat_ty) => {
                    type_refs.extend(extract_type_refs(
                        &pat_ty.ty,
                        self.index,
                        &self.crate_name,
                        &self.module_path,
                    ));
                }
            }
        }
        if let ReturnType::Type(_, ty) = output {
            type_refs.extend(extract_type_refs(
                ty,
                self.index,
                &self.crate_name,
                &self.module_path,
            ));
        }

        let hot_name = function_name_suggests_hot_use(fn_name);
        let callback_or_batch = signature_suggests_callback_or_batch(inputs, output);

        for type_ref in type_refs {
            if !self.externally_reachable_types.contains(&type_ref.key) {
                continue;
            }
            let receiver_is_exclusive = type_ref.receiver_is_exclusive;
            let shared_receiver =
                type_ref.is_receiver && type_ref.by_reference && !receiver_is_exclusive;
            if type_ref.is_receiver && !shared_receiver && !hot_name && !callback_or_batch {
                continue;
            }
            let hot_name_for_type = hot_name && !receiver_is_exclusive;

            let mut emitted = false;
            if shared_receiver {
                self.add_evidence(
                    &type_ref,
                    ApiUsageEvidence {
                        kind: ApiUsageKind::SharedReceiverMethod,
                        description: format!(
                            "API parallelism capability: public method '{fn_name}' exposes '{}' through a non-exclusive receiver at {}:{line}",
                            type_ref.struct_name, self.file
                        ),
                        file: self.file.to_string(),
                        line,
                        score: 0.50,
                    },
                );
                emitted = true;
            }
            if hot_name_for_type {
                self.add_evidence(
                    &type_ref,
                    ApiUsageEvidence {
                        kind: if impl_type.is_some() {
                            ApiUsageKind::MethodNameSuggestsHotUse
                        } else {
                            ApiUsageKind::FunctionNameSuggestsHotUse
                        },
                        description: format!(
                            "API usage hint: public function '{fn_name}' suggests hot/concurrent use of '{}' at {}:{line}",
                            type_ref.struct_name, self.file
                        ),
                        file: self.file.to_string(),
                        line,
                        score: 0.55,
                    },
                );
                emitted = true;
            }

            if type_ref.via_arc {
                self.add_evidence(
                    &type_ref,
                    ApiUsageEvidence {
                        kind: ApiUsageKind::SharedWrapperInSignature,
                        description: format!(
                            "API usage hint: public signature of '{fn_name}' shares '{}' through Arc at {}:{line}",
                            type_ref.struct_name, self.file
                        ),
                        file: self.file.to_string(),
                        line,
                        score: 0.65,
                    },
                );
                emitted = true;
            }

            if type_ref.via_raw_pointer {
                self.add_evidence(
                    &type_ref,
                    ApiUsageEvidence {
                        kind: ApiUsageKind::RawPointerInSignature,
                        description: format!(
                            "API parallelism capability: public function '{fn_name}' exposes '{}' through a raw pointer at {}:{line}",
                            type_ref.struct_name, self.file
                        ),
                        file: self.file.to_string(),
                        line,
                        score: 0.45,
                    },
                );
                emitted = true;
            }

            if type_ref.by_reference
                && !receiver_is_exclusive
                && (hot_name_for_type || callback_or_batch)
            {
                self.add_evidence(
                    &type_ref,
                    ApiUsageEvidence {
                        kind: ApiUsageKind::ReferenceInSignature,
                        description: format!(
                            "API usage hint: public signature of '{fn_name}' exposes '{}' by reference at {}:{line}",
                            type_ref.struct_name, self.file
                        ),
                        file: self.file.to_string(),
                        line,
                        score: 0.45,
                    },
                );
                emitted = true;
            }

            if return_or_name_suggests_handle(fn_name, output) {
                self.add_evidence(
                    &type_ref,
                    ApiUsageEvidence {
                        kind: ApiUsageKind::HandleLikeReturn,
                        description: format!(
                            "API usage hint: public API '{fn_name}' looks like a handle/channel/task access path for '{}' at {}:{line}",
                            type_ref.struct_name, self.file
                        ),
                        file: self.file.to_string(),
                        line,
                        score: 0.50,
                    },
                );
                emitted = true;
            }

            if callback_or_batch {
                self.add_evidence(
                    &type_ref,
                    ApiUsageEvidence {
                        kind: ApiUsageKind::CallbackOrBatchApi,
                        description: format!(
                            "API usage hint: public API '{fn_name}' accepts callback/batch/iterator-style inputs around '{}' at {}:{line}",
                            type_ref.struct_name, self.file
                        ),
                        file: self.file.to_string(),
                        line,
                        score: 0.50,
                    },
                );
                emitted = true;
            }

            if !emitted
                && semantic_name_suggests_hot_use(&type_ref.struct_name)
                && hot_name_for_type
            {
                self.add_evidence(
                    &type_ref,
                    ApiUsageEvidence {
                        kind: ApiUsageKind::SemanticTypeOrFieldName,
                        description: format!(
                            "API usage hint: public API '{fn_name}' and type '{}' both suggest hot runtime state at {}:{line}",
                            type_ref.struct_name, self.file
                        ),
                        file: self.file.to_string(),
                        line,
                        score: 0.40,
                    },
                );
            }
        }
    }
}

impl<'ast> Visit<'ast> for ApiUsageCollector<'_> {
    fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
        let prev = self.current_impl_type.take();
        self.current_impl_type = normalize_type_name(&node.self_ty.to_token_stream().to_string());
        syn::visit::visit_item_impl(self, node);
        self.current_impl_type = prev;
    }

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        let Some((_, items)) = &node.content else {
            return;
        };
        let prev_module_path = self.module_path.clone();
        self.module_path = join_module_path(&self.module_path, &node.ident.to_string());
        for item in items {
            self.visit_item(item);
        }
        self.module_path = prev_module_path;
    }

    fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
        if (self.current_module_is_externally_reachable()
            || self.current_impl_is_externally_reachable())
            && item_visibility(&node.vis).is_externally_exposed()
        {
            let impl_type = self.current_impl_type.clone();
            self.inspect_public_signature(
                &node.sig.ident.to_string(),
                &node.sig.inputs,
                &node.sig.output,
                node.span().start().line,
                impl_type.as_deref(),
            );
        }
        syn::visit::visit_impl_item_fn(self, node);
    }

    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        if self.current_module_is_externally_reachable()
            && item_visibility(&node.vis).is_externally_exposed()
        {
            self.inspect_public_signature(
                &node.sig.ident.to_string(),
                &node.sig.inputs,
                &node.sig.output,
                node.span().start().line,
                None,
            );
        }
        syn::visit::visit_item_fn(self, node);
    }
}

#[derive(Debug)]
struct TypeRef {
    key: StructKey,
    struct_name: String,
    via_arc: bool,
    via_raw_pointer: bool,
    by_reference: bool,
    is_receiver: bool,
    receiver_is_exclusive: bool,
}

fn extract_type_refs(
    ty: &Type,
    index: &ApiUsageIndex,
    crate_name: &str,
    module_path: &str,
) -> Vec<TypeRef> {
    let mut refs = Vec::new();
    let mut seen = HashSet::new();
    collect_type_refs(
        ty,
        index,
        crate_name,
        module_path,
        TypeRefContext::default(),
        &mut seen,
        &mut refs,
    );
    refs
}

#[derive(Debug, Clone, Copy, Default)]
struct TypeRefContext {
    via_arc: bool,
    via_raw_pointer: bool,
    by_reference: bool,
}

fn collect_type_refs(
    ty: &Type,
    index: &ApiUsageIndex,
    crate_name: &str,
    module_path: &str,
    context: TypeRefContext,
    seen: &mut HashSet<StructKey>,
    refs: &mut Vec<TypeRef>,
) {
    match ty {
        Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                let name = segment.ident.to_string();
                if let Some(key) = index.resolve(crate_name, module_path, &name)
                    && seen.insert(key.clone())
                {
                    refs.push(TypeRef {
                        key,
                        struct_name: name,
                        via_arc: context.via_arc,
                        via_raw_pointer: context.via_raw_pointer,
                        by_reference: context.by_reference,
                        is_receiver: false,
                        receiver_is_exclusive: false,
                    });
                }
            }

            for segment in &type_path.path.segments {
                let next_context = TypeRefContext {
                    via_arc: context.via_arc || segment.ident == "Arc",
                    via_raw_pointer: context.via_raw_pointer,
                    by_reference: context.by_reference,
                };
                if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                    for arg in &args.args {
                        if let syn::GenericArgument::Type(inner_ty) = arg {
                            collect_type_refs(
                                inner_ty,
                                index,
                                crate_name,
                                module_path,
                                next_context,
                                seen,
                                refs,
                            );
                        }
                    }
                }
            }
        }
        Type::Reference(reference) => {
            collect_type_refs(
                &reference.elem,
                index,
                crate_name,
                module_path,
                TypeRefContext {
                    by_reference: true,
                    ..context
                },
                seen,
                refs,
            );
        }
        Type::Ptr(pointer) => collect_type_refs(
            &pointer.elem,
            index,
            crate_name,
            module_path,
            TypeRefContext {
                via_raw_pointer: true,
                ..context
            },
            seen,
            refs,
        ),
        Type::Paren(paren) => collect_type_refs(
            &paren.elem,
            index,
            crate_name,
            module_path,
            context,
            seen,
            refs,
        ),
        Type::Group(group) => collect_type_refs(
            &group.elem,
            index,
            crate_name,
            module_path,
            context,
            seen,
            refs,
        ),
        _ => {}
    }
}

fn receiver_is_exclusive(receiver: &syn::Receiver) -> bool {
    if receiver.reference.is_some() {
        return receiver.mutability.is_some();
    }
    if receiver.colon_token.is_none() {
        return true;
    }

    let compact: String = receiver
        .ty
        .to_token_stream()
        .to_string()
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect();

    compact == "Self"
        || compact == "Box<Self>"
        || compact.ends_with("::Box<Self>")
        || compact.contains("Pin<Box<Self>>")
        || compact.contains("Pin<::std::boxed::Box<Self>>")
        || compact.contains("Pin<std::boxed::Box<Self>>")
}

fn item_visibility(vis: &Visibility) -> ItemVisibility {
    match vis {
        Visibility::Public(_) => ItemVisibility::Public,
        Visibility::Restricted(_) => ItemVisibility::Restricted,
        Visibility::Inherited => ItemVisibility::Private,
    }
}

struct ApiUsageIndex {
    keys_by_crate: HashMap<String, Vec<StructKey>>,
}

impl ApiUsageIndex {
    fn new(structs: &[StructInfo]) -> Self {
        let mut keys_by_crate: HashMap<String, Vec<StructKey>> = HashMap::new();
        for si in structs {
            let key = StructKey::from_struct(si);
            keys_by_crate
                .entry(key.crate_name.clone())
                .or_default()
                .push(key);
        }
        Self { keys_by_crate }
    }

    fn resolve(&self, crate_name: &str, module_path: &str, struct_name: &str) -> Option<StructKey> {
        let keys = self.keys_by_crate.get(crate_name)?;
        let local = keys
            .iter()
            .find(|key| key.module_path == module_path && key.name == struct_name);
        if let Some(key) = local {
            return Some(key.clone());
        }
        let root = keys
            .iter()
            .find(|key| key.module_path.is_empty() && key.name == struct_name);
        if let Some(key) = root {
            return Some(key.clone());
        }
        let mut matches = keys.iter().filter(|key| key.name == struct_name);
        let first = matches.next()?.clone();
        if matches.next().is_none() {
            Some(first.clone())
        } else {
            None
        }
    }
}

fn receiver_type_contains_wrapper(receiver: &syn::Receiver, wrapper: &str) -> bool {
    let Type::Path(type_path) = receiver.ty.as_ref() else {
        return false;
    };
    type_path
        .path
        .segments
        .iter()
        .any(|segment| segment.ident == wrapper)
}

fn join_module_path(base: &str, child: &str) -> String {
    if base.is_empty() {
        child.to_string()
    } else {
        format!("{base}::{child}")
    }
}

fn function_name_suggests_hot_use(name: &str) -> bool {
    let lower = name.to_lowercase();
    [
        "send", "push", "pop", "poll", "wake", "notify", "spawn", "schedule", "register", "get",
        "insert", "update", "record", "inc", "fetch", "lock", "try_lock", "read", "write",
        "reserve", "release", "alloc", "free", "enqueue", "dequeue", "submit", "complete",
    ]
    .iter()
    .any(|token| lower.contains(token))
}

fn semantic_name_suggests_hot_use(name: &str) -> bool {
    let lower = name.to_lowercase();
    [
        "handle",
        "guard",
        "sender",
        "receiver",
        "worker",
        "task",
        "slot",
        "shard",
        "cache",
        "stats",
        "stat",
        "counter",
        "runtime",
        "channel",
        "queue",
        "waker",
        "latch",
        "lock",
        "epoch",
        "quota",
        "scheduler",
    ]
    .iter()
    .any(|token| lower.contains(token))
}

fn signature_suggests_callback_or_batch(
    inputs: &syn::punctuated::Punctuated<FnArg, syn::token::Comma>,
    output: &ReturnType,
) -> bool {
    let mut sig = String::new();
    for input in inputs {
        sig.push_str(&input.to_token_stream().to_string());
        sig.push(' ');
    }
    sig.push_str(&output.to_token_stream().to_string());
    let lower = sig.to_lowercase();
    lower.contains("fn (")
        || lower.contains("f :")
        || lower.contains("impl fn")
        || lower.contains("impl fnonce")
        || lower.contains("impl fnmut")
        || lower.contains("impl iterator")
        || lower.contains("iterator")
        || lower.contains("iter")
        || lower.contains("batch")
        || lower.contains("range")
        || lower.contains("parallel")
        || lower.contains("thread")
        || lower.contains("task")
}

fn return_or_name_suggests_handle(name: &str, output: &ReturnType) -> bool {
    let lower_name = name.to_lowercase();
    let output_tokens = output.to_token_stream().to_string().to_lowercase();
    [
        "handle", "guard", "sender", "receiver", "task", "worker", "slot", "shard",
    ]
    .iter()
    .any(|token| lower_name.contains(token) || output_tokens.contains(token))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{FieldInfo, ItemVisibility, LayoutSource};

    #[test]
    fn type_ref_index_finds_struct_mentioned_in_arc_signature() {
        let structs = vec![StructInfo {
            name: "SharedCounters".to_string(),
            module_path: String::new(),
            file: "src/lib.rs".to_string(),
            line: 1,
            crate_name: Some("demo".to_string()),
            cache_line_size: crate::struct_layout::CACHE_LINE_SIZE,
            fields: Vec::new(),
            repr_align_bytes: None,
            repr_align: false,
            repr_packed: false,
            repr_c: false,
            has_cache_padded: false,
            atomic_fields: Vec::new(),
            hot_scalar_fields: Vec::new(),
            hot_sync_fields: Vec::new(),
            total_estimated_size: None,
            cache_line_groups: Vec::new(),
            cache_line_groups_precise: false,
            layout_source: LayoutSource::RustDefaultEstimate,
            visibility: ItemVisibility::Public,
            public_fields: Vec::new(),
            known_not_sync: false,
            shared_field_projections: Vec::new(),
        }];
        let index = ApiUsageIndex::new(&structs);
        let ty: Type = syn::parse_str("std::sync::Arc<SharedCounters>").unwrap();

        let refs = extract_type_refs(&ty, &index, "demo", "");

        assert_eq!(refs.len(), 1);
        assert_eq!(refs[0].struct_name, "SharedCounters");
        assert!(refs[0].via_arc);
    }

    #[test]
    fn type_ref_index_ignores_structs_not_mentioned_in_signature() {
        let structs = vec![
            test_struct("demo", "SharedCounters"),
            test_struct("demo", "OtherCounters"),
        ];
        let index = ApiUsageIndex::new(&structs);
        let ty: Type = syn::parse_str("&SharedCounters").unwrap();

        let refs = extract_type_refs(&ty, &index, "demo", "");

        assert_eq!(refs.len(), 1);
        assert_eq!(refs[0].struct_name, "SharedCounters");
        assert!(refs[0].by_reference);
    }

    fn test_struct(crate_name: &str, name: &str) -> StructInfo {
        StructInfo {
            name: name.to_string(),
            module_path: String::new(),
            file: "src/lib.rs".to_string(),
            line: 1,
            crate_name: Some(crate_name.to_string()),
            cache_line_size: crate::struct_layout::CACHE_LINE_SIZE,
            fields: Vec::<FieldInfo>::new(),
            repr_align_bytes: None,
            repr_align: false,
            repr_packed: false,
            repr_c: false,
            has_cache_padded: false,
            atomic_fields: Vec::new(),
            hot_scalar_fields: Vec::new(),
            hot_sync_fields: Vec::new(),
            total_estimated_size: None,
            cache_line_groups: Vec::new(),
            cache_line_groups_precise: false,
            layout_source: LayoutSource::RustDefaultEstimate,
            visibility: ItemVisibility::Public,
            public_fields: Vec::new(),
            known_not_sync: false,
            shared_field_projections: Vec::new(),
        }
    }
}
