use quote::ToTokens;
use std::collections::{HashMap, HashSet};
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{
    BinOp, Expr, ExprCall, ExprField, ExprMethodCall, ImplItemFn, ItemFn, ItemImpl, Pat, PatType,
    Token,
};

use crate::dataflow::LoopAnalyzer;
use crate::helpers::normalize_type_name;
use crate::rust_indices::{self, IndexValue};
use crate::types::{
    AccessMode, AtomicAccessKind, ConcurrencyEvidenceSet, EvidenceItem, EvidenceKind, ParsedFile,
    StructInfo, StructKey,
};

const MAX_INTERPROCEDURAL_DEPTH: usize = 3;
const MAX_ACCESSES_PER_FUNCTION: usize = 128;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct FunctionKey {
    crate_name: String,
    module_path: String,
    owner: Option<String>,
    trait_name: Option<String>,
    name: String,
}

impl FunctionKey {
    fn display_name(&self) -> String {
        match (&self.owner, &self.trait_name) {
            (Some(owner), Some(trait_name)) => {
                format!("<{owner} as {trait_name}>::{}", self.name)
            }
            (Some(owner), None) => format!("{owner}::{}", self.name),
            (None, _) if self.module_path.is_empty() => self.name.clone(),
            (None, _) => format!("{}::{}", self.module_path, self.name),
        }
    }
}

#[derive(Clone, Debug)]
struct FunctionAccess {
    struct_key: StructKey,
    item: EvidenceItem,
}

#[derive(Clone, Debug, Default)]
struct FunctionSummary {
    accesses: Vec<FunctionAccess>,
    truncated_accesses: usize,
}

pub struct ConcurrencyEvidenceCollection {
    pub evidence_map: HashMap<StructKey, ConcurrencyEvidenceSet>,
    pub truncated_facts: usize,
}

#[derive(Clone, Debug)]
enum CalleeRef {
    Method {
        owner: String,
        owner_module: Option<String>,
        trait_name: Option<String>,
        name: String,
    },
    Free {
        path: Vec<String>,
        name: String,
    },
}

#[derive(Clone, Debug)]
struct FunctionCallSite {
    caller: FunctionKey,
    callee: CalleeRef,
    file: String,
    line: usize,
    hotness_score: f32,
    in_concurrent_context: bool,
    semantic_contexts: Vec<String>,
    through_shared_indirection: bool,
    through_raw_pointer: bool,
    receiver_binding: Option<VarBinding>,
    argument_bindings: Vec<Option<VarBinding>>,
}

struct CallSiteFlow {
    force_concurrent: bool,
    through_shared_indirection: bool,
    through_raw_pointer: bool,
    receiver_binding: Option<VarBinding>,
    argument_bindings: Vec<Option<VarBinding>>,
}

#[derive(Clone, Debug)]
struct MacroSemanticSummary {
    indexed_argument: usize,
    index_argument: Option<usize>,
    access_kind: AtomicAccessKind,
}

#[derive(Clone, Debug)]
struct GlobalTypeBinding {
    name: String,
    module_path: String,
    ty: String,
}

type ModuleImports = HashMap<(String, String), Vec<(Option<String>, Vec<String>)>>;

#[derive(Default)]
struct SemanticDeclarationIndex {
    imports: ModuleImports,
    macros: HashMap<(String, String), Vec<MacroSemanticSummary>>,
    globals: HashMap<(String, String), Vec<GlobalTypeBinding>>,
    native_namespace_shadows: HashSet<(String, String)>,
}

/// Collects concurrency evidence for all struct types across all parsed files.
/// Returns a map keyed by crate/module/type to avoid cross-contamination.
pub fn collect_concurrency_evidence(
    files: &[ParsedFile],
    structs: &[StructInfo],
) -> HashMap<StructKey, ConcurrencyEvidenceSet> {
    collect_concurrency_evidence_with_options(files, structs, true)
}

/// Collect concurrency evidence with an explicit interprocedural switch.
///
/// Keeping the regular entry point above preserves the production default;
/// this variant exists for controlled evaluation rather than as a user-facing
/// approximation of a different analyzer.
pub fn collect_concurrency_evidence_with_options(
    files: &[ParsedFile],
    structs: &[StructInfo],
    use_interprocedural_evidence: bool,
) -> HashMap<StructKey, ConcurrencyEvidenceSet> {
    collect_concurrency_evidence_with_stats(files, structs, use_interprocedural_evidence)
        .evidence_map
}

pub fn collect_concurrency_evidence_with_stats(
    files: &[ParsedFile],
    structs: &[StructInfo],
    use_interprocedural_evidence: bool,
) -> ConcurrencyEvidenceCollection {
    let mut evidence_map: HashMap<StructKey, ConcurrencyEvidenceSet> = HashMap::new();
    let struct_fields = build_struct_field_index(structs);
    let semantic_declarations = collect_semantic_declarations(files);
    let mut function_summaries: HashMap<FunctionKey, FunctionSummary> = HashMap::new();
    let mut call_sites = Vec::new();
    let escaped_functions = escaped_callable_names(files);
    let owned_defaults = owned_default_types(files);

    for pf in files {
        let crate_name = pf
            .crate_name
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        let mut collector = EvidenceCollector {
            file: &pf.path,
            source: &pf.source,
            crate_name: crate_name.clone(),
            module_path: pf.module_path.clone(),
            in_concurrent_context: false,
            concurrent_context_depth: 0,
            current_impl_type: None,
            current_impl_trait: None,
            current_impl_is_generic: false,
            current_function: None,
            current_function_key: None,
            current_semantic_contexts: Vec::new(),
            current_receiver_mode: None,
            async_context_depth: 0,
            unsafe_context_depth: 0,
            index_control_depth: 0,
            evidence_map: &mut evidence_map,
            function_summaries: &mut function_summaries,
            call_sites: &mut call_sites,
            loop_analyzer: LoopAnalyzer::new(),
            struct_fields: &struct_fields,
            macro_summaries: &semantic_declarations.macros,
            global_bindings: &semantic_declarations.globals,
            native_namespace_shadows: &semantic_declarations.native_namespace_shadows,
            imports: &semantic_declarations.imports,
            scoped_vars: vec![HashMap::new()],
            scoped_symbolic_vars: vec![HashSet::new()],
            scoped_indices: vec![HashMap::new()],
            held_guards: Vec::new(),
            escaped_functions: &escaped_functions,
            owned_defaults: &owned_defaults,
        };
        collector.visit_file(&pf.ast);

        let mut wrapper_collector = WrapperTypeCollector {
            file: &pf.path,
            crate_name: crate_name.clone(),
            module_path: pf.module_path.clone(),
            evidence_map: &mut evidence_map,
            struct_fields: &struct_fields,
        };
        wrapper_collector.visit_file(&pf.ast);
    }

    let propagation_truncations = if use_interprocedural_evidence {
        propagate_function_summaries(&mut evidence_map, &mut function_summaries, &call_sites)
    } else {
        0
    };
    let truncated_facts = propagation_truncations
        + function_summaries
            .values()
            .map(|summary| summary.truncated_accesses)
            .sum::<usize>();
    if truncated_facts > 0 {
        for item in evidence_map.values_mut().flat_map(|set| &mut set.evidence) {
            item.semantic_contexts
                .push("rust_object_evidence_incomplete".into());
        }
    }
    sort_evidence_sets(&mut evidence_map);
    ConcurrencyEvidenceCollection {
        evidence_map,
        truncated_facts,
    }
}

struct EvidenceCollector<'a> {
    file: &'a str,
    #[allow(dead_code)]
    source: &'a str,
    crate_name: String,
    module_path: String,
    in_concurrent_context: bool,
    concurrent_context_depth: usize,
    current_impl_type: Option<String>,
    current_impl_trait: Option<String>,
    current_impl_is_generic: bool,
    current_function: Option<String>,
    current_function_key: Option<FunctionKey>,
    current_semantic_contexts: Vec<String>,
    current_receiver_mode: Option<AccessMode>,
    async_context_depth: usize,
    unsafe_context_depth: usize,
    index_control_depth: usize,
    evidence_map: &'a mut HashMap<StructKey, ConcurrencyEvidenceSet>,
    function_summaries: &'a mut HashMap<FunctionKey, FunctionSummary>,
    call_sites: &'a mut Vec<FunctionCallSite>,
    loop_analyzer: LoopAnalyzer,
    struct_fields: &'a HashMap<StructKey, HashMap<String, String>>,
    macro_summaries: &'a HashMap<(String, String), Vec<MacroSemanticSummary>>,
    global_bindings: &'a HashMap<(String, String), Vec<GlobalTypeBinding>>,
    native_namespace_shadows: &'a HashSet<(String, String)>,
    imports: &'a ModuleImports,
    scoped_vars: Vec<HashMap<String, VarBinding>>,
    scoped_symbolic_vars: Vec<HashSet<String>>,
    scoped_indices: Vec<HashMap<String, IndexBinding>>,
    held_guards: Vec<HeldGuard>,
    escaped_functions: &'a HashSet<String>,
    owned_defaults: &'a HashSet<StructKey>,
}

#[derive(Clone)]
struct HeldGuard {
    owner: String,
    identity: String,
    origin: Option<ValueOrigin>,
    depth: usize,
}

#[derive(Clone, Copy)]
struct IndexBinding {
    value: IndexValue,
    mutable: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueOrigin {
    Receiver,
    Parameter(usize),
}

#[derive(Clone, Debug)]
struct VarBinding {
    object_identity: Option<String>,
    object_suffix: Option<String>,
    struct_name: String,
    access_path: String,
    access_mode: AccessMode,
    outer_wrapper: Option<String>,
    through_shared_indirection: bool,
    through_raw_pointer: bool,
    origin: Option<ValueOrigin>,
}

#[derive(Clone, Debug)]
struct ResolvedAccess {
    object_identity: Option<String>,
    object_suffix: Option<String>,
    struct_name: String,
    field_name: String,
    access_path: String,
    is_indexed: bool,
    element_index: Option<IndexValue>,
    access_mode: AccessMode,
    through_shared_indirection: bool,
    through_raw_pointer: bool,
    through_wrapper_projection: bool,
    origin: Option<ValueOrigin>,
}

impl<'a> EvidenceCollector<'a> {
    fn add_evidence(&mut self, struct_name: &str, mut item: EvidenceItem) {
        let Some(key) = self.resolve_struct_key(struct_name) else {
            return;
        };

        let mut contexts = self.active_semantic_contexts();
        contexts.extend(
            self.held_guards
                .iter()
                .filter(|guard| {
                    guard.origin.is_none()
                        || guard.origin == semantic_value_origin(&item.semantic_contexts)
                })
                .map(|guard| format!("rust_guarded_by:{}", guard.identity)),
        );
        for context in contexts {
            if !item.semantic_contexts.contains(&context) {
                item.semantic_contexts.push(context);
            }
        }
        if item.function_name.is_none() {
            item.function_name = self.current_function.clone();
        }
        if item.call_path.is_empty()
            && let Some(function) = self.current_function_key.as_ref()
        {
            item.call_path.push(function.display_name());
        }

        if let Some(function) = self.current_function_key.clone() {
            let summary = self.function_summaries.entry(function).or_default();
            push_function_access(
                summary,
                FunctionAccess {
                    struct_key: key.clone(),
                    item: item.clone(),
                },
            );
        }

        self.evidence_map
            .entry(key)
            .or_default()
            .evidence
            .push(item);
    }

    fn active_semantic_contexts(&self) -> Vec<String> {
        let mut contexts = self.current_semantic_contexts.clone();
        if self.async_context_depth > 0 && !contexts.iter().any(|item| item == "async_block") {
            contexts.push("async_block".to_string());
        }
        if self.unsafe_context_depth > 0 && !contexts.iter().any(|item| item == "unsafe_block") {
            contexts.push("unsafe_block".to_string());
        }
        contexts
    }

    fn register_current_function(&mut self, key: &FunctionKey) {
        self.function_summaries.entry(key.clone()).or_default();
    }

    fn access_is_concurrent(&self, access: &ResolvedAccess) -> bool {
        self.in_concurrent_context
            || (access.through_shared_indirection
                && self.current_semantic_contexts.iter().any(|context| {
                    matches!(
                        context.as_str(),
                        "clone_impl" | "drop_impl" | "handle_lifecycle"
                    )
                }))
    }

    fn record_call_site(&mut self, callee: CalleeRef, node: &impl Spanned, flow: CallSiteFlow) {
        let Some(caller) = self.current_function_key.clone() else {
            return;
        };
        let mut contexts = self.active_semantic_contexts();
        contexts.extend(
            self.held_guards
                .iter()
                .map(|guard| format!("rust_guarded_by:{}", guard.identity)),
        );
        self.call_sites.push(FunctionCallSite {
            caller,
            callee,
            file: self.file.to_string(),
            line: self.span_line(node),
            hotness_score: self
                .loop_analyzer
                .calculate_hotness(&self.loop_analyzer.current_loop_context()),
            in_concurrent_context: self.in_concurrent_context || flow.force_concurrent,
            semantic_contexts: contexts,
            through_shared_indirection: flow.through_shared_indirection,
            through_raw_pointer: flow.through_raw_pointer,
            receiver_binding: flow.receiver_binding,
            argument_bindings: flow.argument_bindings,
        });
    }

    fn record_method_call_site(&mut self, node: &ExprMethodCall) {
        let method = node.method.to_string();
        let Some(binding) = self.binding_from_expr(&node.receiver) else {
            return;
        };
        if method == "clone"
            && binding
                .outer_wrapper
                .as_deref()
                .is_some_and(|wrapper| matches!(wrapper, "Arc" | "Rc" | "Box"))
        {
            return;
        }
        let lifecycle_on_shared = binding.through_shared_indirection
            && self.current_semantic_contexts.iter().any(|context| {
                matches!(
                    context.as_str(),
                    "clone_impl" | "drop_impl" | "handle_lifecycle"
                )
            });
        self.record_call_site(
            CalleeRef::Method {
                owner_module: self
                    .resolve_struct_key(&binding.struct_name)
                    .map(|key| key.module_path),
                owner: binding.struct_name.clone(),
                trait_name: None,
                name: method,
            },
            node,
            CallSiteFlow {
                force_concurrent: lifecycle_on_shared,
                through_shared_indirection: binding.through_shared_indirection,
                through_raw_pointer: binding.through_raw_pointer,
                receiver_binding: Some(binding),
                argument_bindings: node
                    .args
                    .iter()
                    .map(|argument| self.binding_from_expr(argument))
                    .collect(),
            },
        );
    }

    fn record_function_call_site(&mut self, node: &ExprCall) {
        let Expr::Path(path) = node.func.as_ref() else {
            return;
        };
        let name = match path.path.segments.last() {
            Some(segment) => segment.ident.to_string(),
            None => return,
        };
        let segments: Vec<String> = path
            .path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect();
        let first_binding = node
            .args
            .first()
            .and_then(|argument| self.binding_from_expr(argument));
        let argument_bindings: Vec<Option<VarBinding>> = node
            .args
            .iter()
            .map(|argument| self.binding_from_expr(argument))
            .collect();

        if let Some(qself) = &path.qself
            && let Some(owner) = concrete_type_name(&qself.ty.to_token_stream().to_string())
            && self.known_struct(&owner)
        {
            let owner_module = self.resolve_struct_key(&owner).map(|key| key.module_path);
            let trait_name = qself
                .position
                .checked_sub(1)
                .and_then(|position| segments.get(position))
                .cloned();
            let matching_binding = first_binding
                .as_ref()
                .filter(|binding| binding.struct_name == owner);
            self.record_call_site(
                CalleeRef::Method {
                    owner,
                    owner_module,
                    trait_name,
                    name,
                },
                node,
                CallSiteFlow {
                    force_concurrent: false,
                    through_shared_indirection: matching_binding
                        .is_some_and(|binding| binding.through_shared_indirection),
                    through_raw_pointer: matching_binding
                        .is_some_and(|binding| binding.through_raw_pointer),
                    receiver_binding: matching_binding.cloned(),
                    argument_bindings: argument_bindings.clone(),
                },
            );
            return;
        }

        if segments.len() >= 2 {
            let owner = &segments[segments.len() - 2];
            if self.known_struct(owner) {
                let matching_binding = first_binding
                    .as_ref()
                    .filter(|binding| binding.struct_name == *owner);
                self.record_call_site(
                    CalleeRef::Method {
                        owner_module: self.resolve_struct_key(owner).map(|key| key.module_path),
                        owner: owner.clone(),
                        trait_name: None,
                        name,
                    },
                    node,
                    CallSiteFlow {
                        force_concurrent: false,
                        through_shared_indirection: matching_binding
                            .is_some_and(|binding| binding.through_shared_indirection),
                        through_raw_pointer: matching_binding
                            .is_some_and(|binding| binding.through_raw_pointer),
                        receiver_binding: matching_binding.cloned(),
                        argument_bindings: argument_bindings.clone(),
                    },
                );
                return;
            }
        }

        if segments.len() >= 2
            && let Some(binding) = first_binding
            && let Some(trait_name) = segments.get(segments.len().saturating_sub(2))
            && looks_like_type_or_trait_name(trait_name)
            && !is_transparent_binding_wrapper(trait_name)
        {
            self.record_call_site(
                CalleeRef::Method {
                    owner_module: self
                        .resolve_struct_key(&binding.struct_name)
                        .map(|key| key.module_path),
                    owner: binding.struct_name.clone(),
                    trait_name: Some(trait_name.clone()),
                    name,
                },
                node,
                CallSiteFlow {
                    force_concurrent: binding.through_shared_indirection
                        && self.current_semantic_contexts.iter().any(|context| {
                            matches!(
                                context.as_str(),
                                "clone_impl" | "drop_impl" | "handle_lifecycle"
                            )
                        }),
                    through_shared_indirection: binding.through_shared_indirection,
                    through_raw_pointer: binding.through_raw_pointer,
                    receiver_binding: Some(binding),
                    argument_bindings,
                },
            );
            return;
        }

        self.record_call_site(
            CalleeRef::Free {
                path: segments,
                name,
            },
            node,
            CallSiteFlow {
                force_concurrent: false,
                through_shared_indirection: false,
                through_raw_pointer: false,
                receiver_binding: None,
                argument_bindings,
            },
        );
    }

    fn enter_concurrent(&mut self) {
        self.in_concurrent_context = true;
        self.concurrent_context_depth += 1;
    }

    fn leave_concurrent(&mut self) {
        self.concurrent_context_depth = self.concurrent_context_depth.saturating_sub(1);
        if self.concurrent_context_depth == 0 {
            self.in_concurrent_context = false;
        }
    }

    fn span_line(&self, node: &impl Spanned) -> usize {
        node.span().start().line
    }

    fn enter_scope(&mut self) {
        self.scoped_vars.push(HashMap::new());
        self.scoped_symbolic_vars.push(HashSet::new());
        self.scoped_indices.push(HashMap::new());
    }

    fn leave_scope(&mut self) {
        if self.scoped_vars.len() > 1 {
            let depth = self.scoped_vars.len();
            self.held_guards.retain(|guard| guard.depth < depth);
            self.scoped_vars.pop();
            self.scoped_symbolic_vars.pop();
            self.scoped_indices.pop();
        }
    }

    fn bind_var(&mut self, name: String, binding: VarBinding) {
        if let Some(scope) = self.scoped_vars.last_mut() {
            scope.insert(name, binding);
        }
    }

    fn lookup_var(&self, name: &str) -> Option<VarBinding> {
        self.scoped_vars
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn acquired_guard(&self, local: &syn::Local) -> Option<HeldGuard> {
        let Pat::Ident(owner) = &local.pat else {
            return None;
        };
        let mut expr = local.init.as_ref()?.expr.as_ref();
        while let Expr::MethodCall(call) = expr {
            if matches!(call.method.to_string().as_str(), "unwrap" | "expect") {
                expr = &call.receiver;
            } else {
                break;
            }
        }
        let Expr::MethodCall(call) = expr else {
            return None;
        };
        let method = call.method.to_string();
        if !call.args.is_empty() || !matches!(method.as_str(), "lock" | "write") {
            return None;
        }
        let (identity, origin, ty) = if let Some(access) = self.resolve_access(&call.receiver) {
            let origin = access.origin?;
            let key = self.resolve_struct_key(&access.struct_name)?;
            let identity = format!(
                "relative:{}:{}:{}:{}",
                key.crate_name,
                key.qualified_name(),
                value_origin_context(origin),
                access.field_name
            );
            (
                identity,
                Some(origin),
                self.field_type_tokens(&access.struct_name, &access.field_name)?
                    .to_owned(),
            )
        } else if let Expr::Path(path) = call.receiver.as_ref() {
            let mut parts = path
                .path
                .segments
                .iter()
                .map(|part| part.ident.to_string())
                .collect::<Vec<_>>();
            if parts.len() == 1 {
                let name = &parts[0];
                if self.lexical_shadow(name) {
                    // An unresolved local Mutex is still a lexical shadow;
                    // it must not borrow a same-spelled static's lock identity.
                    return None;
                }
                if self
                    .global_bindings
                    .get(&(self.crate_name.clone(), name.clone()))
                    .is_some_and(|items| {
                        items
                            .iter()
                            .any(|item| item.module_path == self.module_path)
                    })
                {
                    parts =
                        resolve_module_use_path(&self.module_path, &["self".into(), name.clone()]);
                } else {
                    let imports = self
                        .imports
                        .get(&(self.crate_name.clone(), self.module_path.clone()))?;
                    let matches = imports
                        .iter()
                        .filter(|(alias, target)| {
                            alias.as_ref().or_else(|| target.last()) == Some(name)
                        })
                        .collect::<Vec<_>>();
                    let [(_, target)] = matches.as_slice() else {
                        return None;
                    };
                    parts = target.clone();
                }
            } else {
                if !matches!(parts[0].as_str(), "crate" | "self" | "super")
                    && self.lexical_shadow(&parts[0])
                {
                    return None;
                }
                parts = resolve_module_use_path(&self.module_path, &parts);
            }
            let name = parts.pop()?;
            let candidates = self
                .global_bindings
                .get(&(self.crate_name.clone(), name.clone()))?
                .iter()
                .filter(|item| item.module_path == parts.join("::"))
                .collect::<Vec<_>>();
            let [declaration] = candidates.as_slice() else {
                return None;
            };
            (
                format!(
                    "global:{}:{}:{name}",
                    self.crate_name, declaration.module_path
                ),
                None,
                declaration.ty.clone(),
            )
        } else {
            return None;
        };
        let wrapper = top_level_wrapper_name(&ty)?;
        if !matches!(
            (wrapper.as_str(), method.as_str()),
            ("Mutex", "lock") | ("RwLock", "write")
        ) || !self.native_lock_type(&ty)
        {
            return None;
        }
        Some(HeldGuard {
            owner: owner.ident.to_string(),
            identity,
            origin,
            depth: self.scoped_vars.len(),
        })
    }

    fn invalidate_guards_used_by(&mut self, expression: &Expr) {
        let used = token_identifiers(&expression.to_token_stream());
        self.held_guards
            .retain(|guard| !used.contains(&guard.owner));
    }

    fn lexical_shadow(&self, name: &str) -> bool {
        self.scoped_indices
            .iter()
            .any(|scope| scope.contains_key(name) || scope.contains_key("*"))
    }

    fn native_namespace_shadow(&self, name: &str) -> bool {
        self.lexical_shadow(name)
            || self
                .native_namespace_shadows
                .contains(&(self.crate_name.clone(), name.to_owned()))
    }

    fn invalidate_object_binding(&mut self, expression: &Expr) {
        match expression {
            Expr::Path(path) if path.path.segments.len() == 1 => {
                let name = path.path.segments[0].ident.to_string();
                for scope in self.scoped_vars.iter_mut().rev() {
                    if let Some(binding) = scope.get_mut(&name) {
                        binding.object_identity = None;
                        binding.object_suffix = None;
                        binding.origin = None;
                        break;
                    }
                }
            }
            Expr::Paren(expr) => self.invalidate_object_binding(&expr.expr),
            Expr::Unary(expr) => self.invalidate_object_binding(&expr.expr),
            _ => {}
        }
    }

    fn invalidate_opaque_macro_effects(&mut self) {
        // A macro can capture definition-site locals even with no input tokens.
        // Without expansion, neither a live guard nor a mutable handle's
        // allocation identity is a proof that survives the invocation.
        self.held_guards.clear();
        let mutable_names: HashSet<_> = self
            .scoped_indices
            .iter()
            .flat_map(|scope| scope.iter())
            .filter(|(_, index)| index.mutable)
            .map(|(name, _)| name.clone())
            .collect();
        for variables in &mut self.scoped_vars {
            for (name, binding) in variables {
                if mutable_names.contains(name) {
                    binding.object_identity = None;
                    binding.object_suffix = None;
                    binding.origin = None;
                }
            }
        }
    }

    fn native_lock_type(&self, ty: &str) -> bool {
        let Ok(syn::Type::Path(ty)) = syn::parse_str::<syn::Type>(ty) else {
            return false;
        };
        let parts = ty
            .path
            .segments
            .iter()
            .map(|part| part.ident.to_string())
            .collect::<Vec<_>>();
        let native = |parts: &[String]| {
            matches!(
                parts
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>()
                    .as_slice(),
                ["std", "sync", "Mutex" | "RwLock"] | ["parking_lot", "Mutex" | "RwLock"]
            )
        };
        if parts.len() > 1 {
            return native(&parts)
                && (ty.path.leading_colon.is_some() || !self.native_namespace_shadow(&parts[0]))
                && (ty.path.leading_colon.is_some() || !self.known_struct(parts.last().unwrap()));
        }
        let Some(name) = parts.first() else {
            return false;
        };
        if self.known_struct(name) {
            return false;
        }
        if self.lexical_shadow(name) {
            return false;
        }
        let Some(imports) = self
            .imports
            .get(&(self.crate_name.clone(), self.module_path.clone()))
        else {
            return false;
        };
        let mut targets = imports
            .iter()
            .filter(|(alias, path)| alias.as_ref().or_else(|| path.last()) == Some(name))
            .map(|(_, path)| path)
            .collect::<Vec<_>>();
        targets.sort();
        targets.dedup();
        matches!(targets.as_slice(), [target] if native(target) && !self.native_namespace_shadow(&target[0]))
    }

    fn native_allocator_path(&self, parts: &[String]) -> bool {
        let native = |parts: &[String]| {
            matches!(
                parts
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>()
                    .as_slice(),
                ["std" | "alloc", "sync", "Arc"] | ["std" | "alloc", "boxed", "Box"]
            )
        };
        if parts.len() > 1 {
            return native(parts)
                && !self.known_struct(parts.last().unwrap())
                && !self.native_namespace_shadow(&parts[0]);
        }
        let Some(name) = parts.first() else {
            return false;
        };
        if self.known_struct(name) {
            return false;
        }
        if self.lexical_shadow(name) {
            return false;
        }
        let mut targets = self
            .imports
            .get(&(self.crate_name.clone(), self.module_path.clone()))
            .into_iter()
            .flatten()
            .filter(|(alias, path)| alias.as_ref().or_else(|| path.last()) == Some(name))
            .map(|(_, path)| path)
            .collect::<Vec<_>>();
        targets.sort();
        targets.dedup();
        matches!(targets.as_slice(), [target] if native(target) && !self.native_namespace_shadow(&target[0]))
            || (targets.is_empty() && name == "Box")
    }

    fn index_value(&self, expression: &Expr) -> IndexValue {
        rust_indices::evaluate(expression, &|name| {
            self.scoped_indices
                .iter()
                .rev()
                .find_map(|scope| scope.get(name).map(|binding| binding.value))
                .unwrap_or(IndexValue::Unknown)
        })
    }

    fn bind_index_pattern(&mut self, pattern: &Pat, value: IndexValue) {
        struct Bindings(Vec<(String, bool)>);
        impl<'ast> Visit<'ast> for Bindings {
            fn visit_pat_ident(&mut self, pattern: &'ast syn::PatIdent) {
                self.0
                    .push((pattern.ident.to_string(), pattern.mutability.is_some()));
                syn::visit::visit_pat_ident(self, pattern);
            }
        }
        let mut names = Bindings(Vec::new());
        names.visit_pat(pattern);
        if let Some(scope) = self.scoped_indices.last_mut() {
            for (name, mutable) in names.0 {
                scope.insert(name, IndexBinding { value, mutable });
            }
        }
    }

    fn assign_index(&mut self, target: &Expr, value: IndexValue) {
        let Some(name) = index_local_name(target) else {
            return;
        };
        for scope in self.scoped_indices.iter_mut().rev() {
            if let Some(binding) = scope.get_mut(&name) {
                binding.value = if self.index_control_depth > 0 {
                    binding.value.join(value)
                } else {
                    value
                };
                return;
            }
        }
    }

    fn invalidate_index_receiver(&mut self, receiver: &Expr) {
        let Some(name) = index_local_name(receiver) else {
            return;
        };
        self.invalidate_mutable_index(&name);
    }

    fn invalidate_mutable_index(&mut self, name: &str) {
        for scope in self.scoped_indices.iter_mut().rev() {
            if let Some(binding) = scope.get_mut(name) {
                // Unresolved method/macro effects may change mutable integers.
                // Never upgrade an unknown binding to a known numeric fact.
                if binding.mutable && binding.value != IndexValue::Unknown {
                    binding.value = IndexValue::Integer;
                }
                return;
            }
        }
    }

    fn invalidate_loop_indices(&mut self, body: &syn::Block) {
        #[derive(Default)]
        struct Assignments(Vec<(String, bool)>);
        impl<'ast> Visit<'ast> for Assignments {
            fn visit_expr_assign(&mut self, expression: &'ast syn::ExprAssign) {
                if let Some(name) = index_local_name(&expression.left) {
                    self.0.push((name, false));
                }
                syn::visit::visit_expr_assign(self, expression);
            }
            fn visit_expr_binary(&mut self, expression: &'ast syn::ExprBinary) {
                if is_compound_assign(&expression.op)
                    && let Some(name) = index_local_name(&expression.left)
                {
                    self.0.push((name, false));
                }
                syn::visit::visit_expr_binary(self, expression);
            }
            fn visit_expr_reference(&mut self, expression: &'ast syn::ExprReference) {
                if expression.mutability.is_some()
                    && let Some(name) = index_local_name(&expression.expr)
                {
                    self.0.push((name, false));
                }
                syn::visit::visit_expr_reference(self, expression);
            }
            fn visit_expr_method_call(&mut self, expression: &'ast ExprMethodCall) {
                if let Some(name) = index_local_name(&expression.receiver) {
                    self.0.push((name, true));
                }
                syn::visit::visit_expr_method_call(self, expression);
            }
            fn visit_expr_raw_addr(&mut self, expression: &'ast syn::ExprRawAddr) {
                if matches!(expression.mutability, syn::PointerMutability::Mut(_))
                    && let Some(name) = index_local_name(&expression.expr)
                {
                    self.0.push((name, false));
                }
                syn::visit::visit_expr_raw_addr(self, expression);
            }
            fn visit_expr_macro(&mut self, expression: &'ast syn::ExprMacro) {
                self.0.extend(
                    token_identifiers(&expression.mac.tokens)
                        .into_iter()
                        .map(|name| (name, true)),
                );
            }
            fn visit_stmt_macro(&mut self, statement: &'ast syn::StmtMacro) {
                self.0.extend(
                    token_identifiers(&statement.mac.tokens)
                        .into_iter()
                        .map(|name| (name, true)),
                );
            }
        }
        let mut assignments = Assignments::default();
        assignments.visit_block(body);
        for (name, requires_mutable) in assignments.0 {
            for scope in self.scoped_indices.iter_mut().rev() {
                if let Some(binding) = scope.get_mut(&name) {
                    if binding.value != IndexValue::Unknown
                        && (!requires_mutable || binding.mutable)
                    {
                        binding.value = IndexValue::Integer;
                    }
                    break;
                }
            }
        }
    }

    fn element_index(&self, expression: &Expr, field: &str) -> Option<IndexValue> {
        fn selects_field(expression: &Expr, name: &str) -> bool {
            match expression {
                Expr::Field(expr) => expr.member.to_token_stream().to_string() == name,
                Expr::Reference(expr) => selects_field(&expr.expr, name),
                Expr::Paren(expr) => selects_field(&expr.expr, name),
                Expr::Group(expr) => selects_field(&expr.expr, name),
                _ => false,
            }
        }
        match expression {
            Expr::MethodCall(expr) if self.is_native_element_accessor(expr) => {
                let access = self.resolve_access(&expr.receiver)?;
                let index = self.index_value(&expr.args[0]);
                (access.field_name == field && index != IndexValue::Unknown).then_some(index)
            }
            Expr::MethodCall(expr) if self.is_element_option_projection(expr) => {
                self.element_index(&expr.receiver, field)
            }
            Expr::Index(expr) if selects_field(&expr.expr, field) => {
                Some(self.index_value(&expr.index))
            }
            Expr::Index(expr) => self.element_index(&expr.expr, field),
            Expr::Field(expr) => self.element_index(&expr.base, field),
            Expr::Reference(expr) => self.element_index(&expr.expr, field),
            Expr::Unary(expr) => self.element_index(&expr.expr, field),
            Expr::Paren(expr) => self.element_index(&expr.expr, field),
            Expr::Group(expr) => self.element_index(&expr.expr, field),
            Expr::Cast(expr) => self.element_index(&expr.expr, field),
            _ => None,
        }
    }

    fn is_native_element_accessor(&self, expression: &ExprMethodCall) -> bool {
        matches!(
            expression.method.to_string().as_str(),
            "get" | "get_mut" | "get_unchecked" | "get_unchecked_mut"
        ) && expression.args.len() == 1
            && self
                .resolve_access(&expression.receiver)
                .is_some_and(|access| {
                    self.field_type_tokens(&access.struct_name, &access.field_name)
                        .and_then(|ty| syn::parse_str::<syn::Type>(ty).ok())
                        .is_some_and(|ty| is_native_sequence_type(&ty))
                })
    }

    fn is_element_option_projection(&self, expression: &ExprMethodCall) -> bool {
        let arguments_match = match expression.method.to_string().as_str() {
            "unwrap" => expression.args.is_empty(),
            "expect" => expression.args.len() == 1,
            _ => false,
        };
        arguments_match
            && matches!(expression.receiver.as_ref(), Expr::MethodCall(receiver)
                if matches!(receiver.method.to_string().as_str(), "get" | "get_mut")
                    && self.is_native_element_accessor(receiver))
    }

    fn bind_symbolic_pattern(&mut self, pattern: &Pat) {
        let mut names = Vec::new();
        collect_pattern_identifiers(pattern, &mut names);
        if let Some(scope) = self.scoped_symbolic_vars.last_mut() {
            scope.extend(names);
        }
    }

    fn expression_depends_on_symbolic(&self, expression: &Expr) -> bool {
        struct DependencyVisitor<'a> {
            scopes: &'a [HashSet<String>],
            found: bool,
        }

        impl<'ast> Visit<'ast> for DependencyVisitor<'_> {
            fn visit_expr_path(&mut self, node: &'ast syn::ExprPath) {
                if let Some(name) = node
                    .path
                    .segments
                    .last()
                    .map(|segment| segment.ident.to_string())
                    && self.scopes.iter().rev().any(|scope| scope.contains(&name))
                {
                    self.found = true;
                    return;
                }
                syn::visit::visit_expr_path(self, node);
            }
        }

        let mut visitor = DependencyVisitor {
            scopes: &self.scoped_symbolic_vars,
            found: false,
        };
        visitor.visit_expr(expression);
        visitor.found
    }

    fn known_struct(&self, struct_name: &str) -> bool {
        self.resolve_struct_key(struct_name).is_some()
    }

    fn field_type(&self, struct_name: &str, field_name: &str) -> Option<String> {
        let ty = self.field_type_tokens(struct_name, field_name)?;
        concrete_type_name(ty)
    }

    fn field_type_tokens(&self, struct_name: &str, field_name: &str) -> Option<&str> {
        let key = self.resolve_struct_key(struct_name)?;
        self.struct_fields
            .get(&key)?
            .get(field_name)
            .map(String::as_str)
    }

    fn resolve_struct_key(&self, struct_name: &str) -> Option<StructKey> {
        resolve_struct_key(
            self.struct_fields,
            &self.crate_name,
            &self.module_path,
            struct_name,
        )
    }

    fn binding_from_type(&self, ty: &str, access_path: String) -> Option<VarBinding> {
        let struct_name = concrete_type_name(ty)?;
        if self.known_struct(&struct_name) {
            let outer_wrapper = top_level_wrapper_name(ty);
            let through_raw_pointer = type_is_raw_pointer_like(ty);
            Some(VarBinding {
                object_identity: None,
                object_suffix: Some(String::new()),
                struct_name,
                access_path,
                access_mode: access_mode_from_type_tokens(ty),
                through_shared_indirection: type_has_shared_indirection(ty),
                through_raw_pointer,
                outer_wrapper,
                origin: None,
            })
        } else {
            None
        }
    }

    fn binding_from_pat_type(&self, pat_ty: &PatType) -> Option<(String, VarBinding)> {
        let Pat::Ident(ident) = pat_ty.pat.as_ref() else {
            return None;
        };
        let name = ident.ident.to_string();
        let binding =
            self.binding_from_type(&pat_ty.ty.to_token_stream().to_string(), name.clone())?;
        Some((name, binding))
    }

    fn binding_from_expr(&self, expr: &Expr) -> Option<VarBinding> {
        match expr {
            Expr::Path(path) => {
                let name = path.path.segments.last()?.ident.to_string();
                if name == "self" || name == "Self" {
                    Some(VarBinding {
                        object_identity: None,
                        object_suffix: Some(String::new()),
                        struct_name: self.current_impl_type.clone()?,
                        access_path: "self".to_string(),
                        access_mode: self.current_receiver_mode.unwrap_or(AccessMode::Unknown),
                        outer_wrapper: None,
                        through_shared_indirection: false,
                        through_raw_pointer: false,
                        origin: Some(ValueOrigin::Receiver),
                    })
                } else {
                    (path.path.segments.len() == 1)
                        .then(|| self.lookup_var(&name))
                        .flatten()
                        .or_else(|| self.binding_from_global(&path.path))
                }
            }
            Expr::Reference(reference) => {
                self.binding_from_expr(&reference.expr).map(|mut binding| {
                    binding.access_mode = if reference.mutability.is_some() {
                        AccessMode::Exclusive
                    } else {
                        AccessMode::Shared
                    };
                    binding
                })
            }
            Expr::Unary(unary) => self.binding_from_expr(&unary.expr),
            Expr::Paren(paren) => self.binding_from_expr(&paren.expr),
            Expr::Await(await_expr) => self.binding_from_expr(&await_expr.base),
            Expr::Cast(cast) => self.binding_from_expr(&cast.expr).map(|mut binding| {
                if type_is_raw_pointer_like(&cast.ty.to_token_stream().to_string()) {
                    binding.access_mode = AccessMode::Unknown;
                    binding.outer_wrapper = Some("raw_pointer".to_string());
                    binding.through_raw_pointer = true;
                }
                binding
            }),
            Expr::Call(call) => {
                let func = call.func.to_token_stream().to_string();
                if let Expr::Path(path) = call.func.as_ref() {
                    let parts = path
                        .path
                        .segments
                        .iter()
                        .map(|segment| segment.ident.to_string())
                        .collect::<Vec<_>>();
                    if parts.last().is_some_and(|name| name == "new")
                        && parts
                            .iter()
                            .rev()
                            .nth(1)
                            .is_some_and(|name| matches!(name.as_str(), "Arc" | "Box"))
                        && self.native_allocator_path(&parts[..parts.len() - 1])
                        && call.args.len() == 1
                        && let Some(mut binding) = self.binding_from_expr(&call.args[0])
                    {
                        let wrapper = parts[parts.len() - 2].clone();
                        if binding.outer_wrapper.is_none()
                            && binding.access_mode.is_exclusive()
                            && !binding.through_shared_indirection
                            && !binding.through_raw_pointer
                        {
                            binding.object_identity = Some(format!(
                                "allocation:{}:{}:{}",
                                self.file,
                                expr.span().start().line,
                                expr.span().start().column
                            ));
                            binding.object_suffix = Some(String::new());
                        }
                        binding.outer_wrapper = Some(wrapper.clone());
                        binding.through_shared_indirection |= wrapper == "Arc";
                        binding.access_mode = if binding.through_shared_indirection {
                            AccessMode::Shared
                        } else {
                            AccessMode::Exclusive
                        };
                        return Some(binding);
                    }
                    let owner = parts[..parts.len().saturating_sub(1)].join("::");
                    if parts.last().is_some_and(|name| name == "default")
                        && !owner.is_empty()
                        && self
                            .resolve_struct_key(&owner)
                            .is_some_and(|key| self.owned_defaults.contains(&key))
                        && let Some(mut binding) = self.binding_from_type(&owner, func.clone())
                    {
                        binding.object_identity = Some(format!(
                            "value:{}:{}:{}",
                            self.file,
                            expr.span().start().line,
                            expr.span().start().column
                        ));
                        return Some(binding);
                    }
                }
                if (func.contains("Arc :: clone") || func.contains("std :: sync :: Arc :: clone"))
                    && call.args.len() == 1
                {
                    call.args
                        .first()
                        .and_then(|arg| self.binding_from_expr(arg))
                        .map(|mut binding| {
                            binding.access_path = expr.to_token_stream().to_string();
                            binding.access_mode = AccessMode::Shared;
                            binding.through_shared_indirection = true;
                            binding
                        })
                } else if func.ends_with("clone") && call.args.len() == 1 {
                    call.args
                        .first()
                        .and_then(|arg| self.binding_from_expr(arg))
                        .map(|mut binding| {
                            binding.access_path = expr.to_token_stream().to_string();
                            if !binding.through_shared_indirection && !binding.through_raw_pointer {
                                binding.access_mode = AccessMode::Exclusive;
                            }
                            binding
                        })
                } else if (func.contains("Arc :: as_ptr")
                    || func.contains("Rc :: as_ptr")
                    || func.contains("NonNull :: as_ptr"))
                    && call.args.len() == 1
                {
                    call.args
                        .first()
                        .and_then(|arg| self.binding_from_expr(arg))
                        .map(|mut binding| {
                            binding.access_path = expr.to_token_stream().to_string();
                            binding.access_mode = AccessMode::Unknown;
                            binding.outer_wrapper = Some("raw_pointer".to_string());
                            binding.through_raw_pointer = true;
                            binding
                        })
                } else if call.args.len() == 1
                    && path_tail_name(call.func.as_ref())
                        .is_some_and(|name| is_transparent_binding_wrapper(&name))
                {
                    call.args
                        .first()
                        .and_then(|argument| self.binding_from_expr(argument))
                } else {
                    None
                }
            }
            Expr::MethodCall(method) => {
                if method.method == "clone" {
                    self.binding_from_expr(&method.receiver).map(|mut binding| {
                        binding.access_path = expr.to_token_stream().to_string();
                        if !binding.through_shared_indirection && !binding.through_raw_pointer {
                            binding.access_mode = AccessMode::Exclusive;
                        }
                        binding
                    })
                } else if matches!(method.method.to_string().as_str(), "as_ptr" | "as_mut_ptr") {
                    self.binding_from_expr(&method.receiver).map(|mut binding| {
                        binding.access_path = expr.to_token_stream().to_string();
                        binding.access_mode = AccessMode::Unknown;
                        binding.outer_wrapper = Some("raw_pointer".to_string());
                        binding.through_raw_pointer = true;
                        binding
                    })
                } else if method.method == "as_mut" {
                    self.binding_from_expr(&method.receiver).map(|mut binding| {
                        binding.access_path = expr.to_token_stream().to_string();
                        binding.access_mode = AccessMode::Exclusive;
                        binding
                    })
                } else if method.method == "as_ref" {
                    self.binding_from_expr(&method.receiver).map(|mut binding| {
                        binding.access_path = expr.to_token_stream().to_string();
                        binding.access_mode = AccessMode::Shared;
                        binding
                    })
                } else if matches!(
                    method.method.to_string().as_str(),
                    "lock" | "try_lock" | "write" | "try_write" | "borrow_mut"
                ) {
                    self.binding_from_expr(&method.receiver).map(|mut binding| {
                        binding.access_path = expr.to_token_stream().to_string();
                        binding.access_mode = AccessMode::Exclusive;
                        binding.outer_wrapper = Some("exclusive_guard".to_string());
                        binding.through_shared_indirection = false;
                        binding
                    })
                } else if matches!(method.method.to_string().as_str(), "unwrap" | "expect") {
                    self.binding_from_expr(&method.receiver).map(|mut binding| {
                        binding.access_path = expr.to_token_stream().to_string();
                        binding
                    })
                } else {
                    None
                }
            }
            Expr::Field(_) | Expr::Index(_) => self.resolve_access(expr).and_then(|access| {
                let next_type = self.field_type(&access.struct_name, &access.field_name)?;
                if self.known_struct(&next_type) {
                    let outer_wrapper = self
                        .field_type_tokens(&access.struct_name, &access.field_name)
                        .and_then(top_level_wrapper_name);
                    let through_shared_indirection = access.through_shared_indirection
                        || self
                            .field_type_tokens(&access.struct_name, &access.field_name)
                            .is_some_and(type_has_shared_indirection);
                    let through_raw_pointer = access.through_raw_pointer
                        || outer_wrapper.as_deref() == Some("raw_pointer")
                        || self
                            .field_type_tokens(&access.struct_name, &access.field_name)
                            .is_some_and(type_is_raw_pointer_like);
                    Some(VarBinding {
                        object_identity: if through_shared_indirection || through_raw_pointer {
                            None
                        } else {
                            access
                                .object_identity
                                .map(|identity| format!("{identity}.{}", access.field_name))
                        },
                        object_suffix: if through_shared_indirection || through_raw_pointer {
                            None
                        } else {
                            access
                                .object_suffix
                                .map(|suffix| format!("{suffix}.{}", access.field_name))
                        },
                        struct_name: next_type,
                        access_path: access.access_path,
                        access_mode: if through_raw_pointer {
                            AccessMode::Unknown
                        } else if through_shared_indirection {
                            AccessMode::Shared
                        } else {
                            access.access_mode
                        },
                        outer_wrapper,
                        through_shared_indirection,
                        through_raw_pointer,
                        origin: access.origin,
                    })
                } else {
                    None
                }
            }),
            Expr::Struct(record) => {
                let mut binding = self.binding_from_type(
                    &record.path.to_token_stream().to_string(),
                    expr.to_token_stream().to_string(),
                )?;
                binding.object_identity = Some(format!(
                    "value:{}:{}:{}",
                    self.file,
                    expr.span().start().line,
                    expr.span().start().column
                ));
                Some(binding)
            }
            _ => None,
        }
    }

    fn binding_from_global(&self, path: &syn::Path) -> Option<VarBinding> {
        let parts: Vec<String> = path
            .segments
            .iter()
            .map(|part| part.ident.to_string())
            .collect();
        let name = parts.last()?;
        if parts.len() == 1 && self.lexical_shadow(name)
            || parts.first().is_some_and(|prefix| {
                !matches!(prefix.as_str(), "crate" | "self" | "super")
                    && self.lexical_shadow(prefix)
            })
        {
            return None;
        }
        let mut targets = Vec::new();
        if parts.len() > 1 {
            targets.push(resolve_module_use_path(&self.module_path, &parts));
        } else {
            let local = self
                .global_bindings
                .get(&(self.crate_name.clone(), name.clone()));
            if local.is_some_and(|items| {
                items
                    .iter()
                    .any(|item| item.module_path == self.module_path)
            }) {
                targets.push(resolve_module_use_path(
                    &self.module_path,
                    &["self".into(), name.clone()],
                ));
            } else if let Some(imports) = self
                .imports
                .get(&(self.crate_name.clone(), self.module_path.clone()))
            {
                // Explicit imports shadow glob imports. Ambiguous globs stay unresolved.
                targets.extend(
                    imports
                        .iter()
                        .filter(|(alias, _)| alias.as_ref() == Some(name))
                        .map(|(_, path)| path.clone()),
                );
                if targets.is_empty() {
                    targets.extend(imports.iter().filter(|(alias, _)| alias.is_none()).map(
                        |(_, path)| {
                            let mut target = path.clone();
                            target.push(name.clone());
                            target
                        },
                    ));
                }
            }
        }
        let mut selected = Vec::new();
        for target in &targets {
            let (global_name, module) = target.split_last()?;
            if let Some(candidates) = self
                .global_bindings
                .get(&(self.crate_name.clone(), global_name.clone()))
            {
                selected.extend(
                    candidates
                        .iter()
                        .filter(|candidate| candidate.module_path == module.join("::")),
                );
            }
        }
        if targets.is_empty() {
            // Preserve the existing unambiguous source-only fallback.
            selected.extend(
                self.global_bindings
                    .get(&(self.crate_name.clone(), name.clone()))?
                    .iter(),
            );
        }
        selected.sort_by(|a, b| a.module_path.cmp(&b.module_path).then(a.ty.cmp(&b.ty)));
        selected.dedup_by(|a, b| a.module_path == b.module_path && a.ty == b.ty);
        let [selected] = selected.as_slice() else {
            return None;
        };
        // Resolve the declaration's type in its owning module, never in the
        // importing module: two architectures may both declare State/GLOBAL.
        let ty_name = concrete_type_name(&selected.ty)?;
        let key = resolve_struct_key(
            self.struct_fields,
            &self.crate_name,
            &selected.module_path,
            &ty_name,
        )?;
        Some(VarBinding {
            object_identity: (!type_has_shared_indirection(&selected.ty)
                && !type_is_raw_pointer_like(&selected.ty))
            .then(|| {
                format!(
                    "global:{}:{}:{}",
                    self.crate_name, selected.module_path, selected.name
                )
            }),
            object_suffix: Some(String::new()),
            struct_name: format!("crate::{}", key.qualified_name()),
            access_path: path.to_token_stream().to_string(),
            access_mode: AccessMode::Unknown,
            outer_wrapper: top_level_wrapper_name(&selected.ty),
            through_shared_indirection: type_has_shared_indirection(&selected.ty),
            through_raw_pointer: type_is_raw_pointer_like(&selected.ty),
            origin: None,
        })
    }

    fn record_macro_expansion_access(&mut self, node: &syn::ExprMacro) {
        let Some(name) = node
            .mac
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
        else {
            return;
        };
        let Some(summaries) = self
            .macro_summaries
            .get(&(self.crate_name.clone(), name.clone()))
        else {
            return;
        };
        let Ok(arguments) =
            Punctuated::<Expr, Token![,]>::parse_terminated.parse2(node.mac.tokens.clone())
        else {
            return;
        };
        let arguments: Vec<Expr> = arguments.into_iter().collect();
        for summary in summaries {
            let Some(container) = arguments.get(summary.indexed_argument) else {
                continue;
            };
            let Some(access) = self.resolve_access(container) else {
                continue;
            };
            let line = self.span_line(node);
            let loop_ctx = self.loop_analyzer.current_loop_context();
            let mut contexts = access_semantic_contexts(&access);
            contexts.push("macro_expansion_summary".to_string());
            if let Some(index) = summary
                .index_argument
                .and_then(|index| arguments.get(index))
            {
                contexts.push(self.index_value(index).context());
            }
            let index = summary
                .index_argument
                .and_then(|index| arguments.get(index))
                .map(ToTokens::to_token_stream)
                .map(|tokens| tokens.to_string())
                .unwrap_or_else(|| "unknown".to_string());
            self.add_evidence(
                &access.struct_name,
                EvidenceItem {
                    kind: EvidenceKind::HotSyncFieldOps,
                    access_kind: Some(summary.access_kind.clone()),
                    field_name: Some(access.field_name.clone()),
                    loop_context: loop_ctx.clone(),
                    hotness_score: self.loop_analyzer.calculate_hotness(&loop_ctx),
                    in_concurrent_context: self.access_is_concurrent(&access),
                    access_mode: access.access_mode,
                    function_name: self.current_function.clone(),
                    propagation_depth: 0,
                    call_path: Vec::new(),
                    semantic_contexts: contexts,
                    through_shared_indirection: access.through_shared_indirection,
                    through_raw_pointer: access.through_raw_pointer,
                    description: format!(
                        "declarative macro '{name}!' expands indexed synchronization on '{}' with index '{index}' at {}:{line}",
                        access.access_path, self.file
                    ),
                    file: self.file.to_string(),
                    line,
                },
            );
        }
    }

    fn check_sync_method_on_field(&mut self, node: &'_ ExprMethodCall) {
        let method = node.method.to_string();
        if method == "clone" {
            if let Some(access) = self.resolve_access(&node.receiver)
                && let Some(ty) = self.field_type_tokens(&access.struct_name, &access.field_name)
                && top_level_wrapper_name(ty).is_some_and(|wrapper| {
                    matches!(wrapper.as_str(), "Rc" | "Arc") && !self.known_struct(&wrapper)
                })
            {
                self.record_plain_value_read(&node.receiver, self.span_line(node));
            }
            return;
        }

        let (kind, access_kind) = match method.as_str() {
            "load" => (EvidenceKind::AtomicFieldOps, AtomicAccessKind::Read),
            "get" => (EvidenceKind::HotSyncFieldOps, AtomicAccessKind::Read),
            "store" => (EvidenceKind::AtomicFieldOps, AtomicAccessKind::Write),
            "fetch_add"
            | "fetch_sub"
            | "fetch_and"
            | "fetch_or"
            | "fetch_xor"
            | "fetch_nand"
            | "fetch_min"
            | "fetch_max"
            | "swap"
            | "compare_exchange"
            | "compare_exchange_weak" => (
                EvidenceKind::AtomicFieldOps,
                AtomicAccessKind::ReadModifyWrite,
            ),
            "set" => (EvidenceKind::HotSyncFieldOps, AtomicAccessKind::Write),
            "lock" | "try_lock" | "read" | "try_read" | "write" | "try_write" | "borrow_mut"
            | "notify_one" | "notify_waiters" | "wake" | "wake_by_ref" | "register" | "push"
            | "pop" | "send" | "recv" => (
                EvidenceKind::HotSyncFieldOps,
                AtomicAccessKind::ReadModifyWrite,
            ),
            _ => return,
        };

        if let Some(access) = self.resolve_access(&node.receiver) {
            let mut access_contexts = access_semantic_contexts(&access);
            if access.is_indexed
                && self
                    .field_type_tokens(&access.struct_name, &access.field_name)
                    .is_some_and(|ty| indexed_pointee_type(ty, &node.receiver))
            {
                // Auto-deref operates on an independently allocated payload,
                // not on the contiguous Arc/Box/reference slot in the vector.
                access_contexts.push("container_element_pointee".to_string());
            }
            // `.get()` is not a universal read operation.  Ordinary value
            // getters (including Cell::get) return a value, while
            // UnsafeCell::get exposes a mutable raw pointer whose later use
            // may write the location.  Preserve that language-level escape
            // conservatively without turning every project-defined getter
            // into an RMW witness.
            let access_kind = if method == "get"
                && self
                    .field_type_tokens(&access.struct_name, &access.field_name)
                    .is_some_and(|ty| ty.contains("UnsafeCell"))
            {
                AtomicAccessKind::ReadModifyWrite
            } else {
                access_kind
            };
            let line = self.span_line(node);
            let loop_ctx = self.loop_analyzer.current_loop_context();
            let hotness = self.loop_analyzer.calculate_hotness(&loop_ctx);

            self.add_evidence(
                &access.struct_name,
                EvidenceItem {
                    kind,
                    access_kind: Some(access_kind),
                    field_name: Some(access.field_name.clone()),
                    loop_context: loop_ctx,
                    hotness_score: hotness,
                    in_concurrent_context: self.access_is_concurrent(&access),
                    access_mode: access.access_mode,
                    function_name: self.current_function.clone(),
                    propagation_depth: 0,
                    call_path: Vec::new(),
                    semantic_contexts: access_contexts,
                    through_shared_indirection: access.through_shared_indirection,
                    through_raw_pointer: access.through_raw_pointer,
                    description: format!(
                        "sync op '.{method}()' on path '{}' at {}:{line}",
                        access.access_path, self.file
                    ),
                    file: self.file.to_string(),
                    line,
                },
            );
        }
    }

    fn resolve_access(&self, expr: &Expr) -> Option<ResolvedAccess> {
        let mut segments = Vec::new();
        let mut indexed = false;
        let base = self.collect_access_path(expr, &mut segments, &mut indexed)?;
        if segments.is_empty() {
            return None;
        }

        let mut current_struct = base.struct_name;
        let mut current_path = base.access_path;
        let mut access_mode = base.access_mode;
        let mut through_shared_indirection = base.through_shared_indirection;
        let mut through_raw_pointer = base.through_raw_pointer;
        let mut object_identity = base.object_identity;
        let mut object_suffix = base.object_suffix;
        for (idx, segment) in segments.iter().enumerate() {
            if !current_path.is_empty() {
                current_path.push('.');
            }
            current_path.push_str(segment);

            let is_last = idx == segments.len() - 1;
            if is_last {
                return Some(ResolvedAccess {
                    object_identity,
                    object_suffix,
                    struct_name: current_struct,
                    field_name: segment.clone(),
                    access_path: current_path,
                    is_indexed: indexed,
                    element_index: self.element_index(expr, segment),
                    access_mode,
                    through_shared_indirection,
                    through_raw_pointer,
                    through_wrapper_projection: false,
                    origin: base.origin,
                });
            }

            // Source-level layout tracks named outer fields, while tuple
            // newtypes commonly expose their payload as `.0` (for example
            // `self.counter.0.fetch_add(...)`).  Collapse that transparent
            // projection back to the outer named field instead of inventing a
            // numeric field on the wrapper type.  The wrapper's own alignment
            // and stride remain part of the layout model.
            if segments
                .get(idx + 1)
                .is_some_and(|next| next.parse::<usize>().is_ok())
            {
                for projection in &segments[idx + 1..] {
                    current_path.push('.');
                    current_path.push_str(projection);
                }
                return Some(ResolvedAccess {
                    object_identity,
                    object_suffix,
                    struct_name: current_struct,
                    field_name: segment.clone(),
                    access_path: current_path,
                    is_indexed: indexed,
                    element_index: self.element_index(expr, segment),
                    access_mode,
                    through_shared_indirection,
                    through_raw_pointer,
                    through_wrapper_projection: true,
                    origin: base.origin,
                });
            }

            let field_ty = self.field_type_tokens(&current_struct, segment)?;
            if type_has_shared_indirection(field_ty) || type_is_raw_pointer_like(field_ty) {
                object_identity = None;
                object_suffix = None;
            } else {
                object_identity = object_identity.map(|identity| format!("{identity}.{segment}"));
                object_suffix = object_suffix.map(|suffix| format!("{suffix}.{segment}"));
                if syn::parse_str::<syn::Type>(field_ty)
                    .ok()
                    .is_some_and(|ty| is_native_sequence_type(&ty))
                {
                    let index = self
                        .element_index(expr, segment)
                        .and_then(|index| index.constant());
                    object_identity = index.and_then(|index| {
                        object_identity.map(|identity| format!("{identity}[{index}]"))
                    });
                    object_suffix = index
                        .and_then(|index| object_suffix.map(|suffix| format!("{suffix}[{index}]")));
                }
            }
            if type_has_shared_indirection(field_ty) {
                access_mode = AccessMode::Shared;
                through_shared_indirection = true;
            }
            if type_is_raw_pointer_like(field_ty) {
                access_mode = AccessMode::Unknown;
                through_raw_pointer = true;
            }
            current_struct = self.field_type(&current_struct, segment)?;
            if !self.known_struct(&current_struct) {
                return None;
            }
        }
        None
    }

    fn collect_access_path(
        &self,
        expr: &Expr,
        segments: &mut Vec<String>,
        indexed: &mut bool,
    ) -> Option<VarBinding> {
        match expr {
            Expr::Field(field) => {
                segments.insert(0, field.member.to_token_stream().to_string());
                self.collect_access_path(&field.base, segments, indexed)
            }
            Expr::Index(index) => {
                *indexed = true;
                self.collect_access_path(&index.expr, segments, indexed)
            }
            Expr::MethodCall(method) if self.is_native_element_accessor(method) => {
                *indexed = true;
                self.collect_access_path(&method.receiver, segments, indexed)
            }
            Expr::MethodCall(method) if self.is_element_option_projection(method) => {
                self.collect_access_path(&method.receiver, segments, indexed)
            }
            Expr::Path(path) => {
                let name = path.path.segments.last()?.ident.to_string();
                if name == "self" || name == "Self" {
                    Some(VarBinding {
                        object_identity: None,
                        object_suffix: Some(String::new()),
                        struct_name: self.current_impl_type.clone()?,
                        access_path: "self".to_string(),
                        access_mode: self.current_receiver_mode.unwrap_or(AccessMode::Unknown),
                        outer_wrapper: None,
                        through_shared_indirection: false,
                        through_raw_pointer: false,
                        origin: Some(ValueOrigin::Receiver),
                    })
                } else {
                    (path.path.segments.len() == 1)
                        .then(|| self.lookup_var(&name))
                        .flatten()
                        .or_else(|| self.binding_from_global(&path.path))
                        .or_else(|| {
                            if self.known_struct(&name) {
                                Some(VarBinding {
                                    object_identity: None,
                                    object_suffix: Some(String::new()),
                                    struct_name: name.clone(),
                                    access_path: name,
                                    access_mode: AccessMode::Unknown,
                                    outer_wrapper: None,
                                    through_shared_indirection: false,
                                    through_raw_pointer: false,
                                    origin: None,
                                })
                            } else {
                                None
                            }
                        })
                }
            }
            Expr::Reference(reference) => {
                self.collect_access_path(&reference.expr, segments, indexed)
            }
            Expr::Unary(unary) => self.collect_access_path(&unary.expr, segments, indexed),
            Expr::Paren(paren) => self.collect_access_path(&paren.expr, segments, indexed),
            Expr::Group(group) => self.collect_access_path(&group.expr, segments, indexed),
            Expr::Cast(cast) => self.collect_access_path(&cast.expr, segments, indexed),
            _ => None,
        }
    }

    fn is_spawn_or_scope(method: &str) -> bool {
        matches!(method, "spawn")
    }

    fn is_parallel_iter(method: &str) -> bool {
        matches!(method, "par_iter" | "par_iter_mut" | "into_par_iter")
    }

    fn record_plain_value_read(&mut self, expr: &Expr, line: usize) {
        // Only a value expression establishes a load. References, address
        // construction, assignments and arbitrary method receivers do not.
        match expr {
            Expr::Paren(node) => {
                self.record_plain_value_read(&node.expr, line);
                return;
            }
            Expr::Group(node) => {
                self.record_plain_value_read(&node.expr, line);
                return;
            }
            Expr::Field(_) => {}
            _ => return,
        }
        if let Some(access) = self.resolve_access(expr) {
            let loop_ctx = self.loop_analyzer.current_loop_context();
            let hotness = self.loop_analyzer.calculate_hotness(&loop_ctx);
            self.add_evidence(
                &access.struct_name,
                EvidenceItem {
                    kind: EvidenceKind::PlainFieldRead,
                    access_kind: Some(AtomicAccessKind::Read),
                    field_name: Some(access.field_name.clone()),
                    loop_context: loop_ctx,
                    hotness_score: hotness,
                    in_concurrent_context: self.access_is_concurrent(&access),
                    access_mode: access.access_mode,
                    function_name: self.current_function.clone(),
                    propagation_depth: 0,
                    call_path: Vec::new(),
                    semantic_contexts: access_semantic_contexts(&access),
                    through_shared_indirection: access.through_shared_indirection,
                    through_raw_pointer: access.through_raw_pointer,
                    description: format!(
                        "plain field read on path '{}' at {}:{line}",
                        access.access_path, self.file
                    ),
                    file: self.file.to_string(),
                    line,
                },
            );
        }
    }

    fn record_plain_field_write(&mut self, expr: &Expr, line: usize) {
        if let Some(access) = self.resolve_access(expr) {
            let loop_ctx = self.loop_analyzer.current_loop_context();
            let hotness = self.loop_analyzer.calculate_hotness(&loop_ctx);
            self.add_evidence(
                &access.struct_name,
                EvidenceItem {
                    kind: EvidenceKind::PlainFieldWrite,
                    access_kind: Some(AtomicAccessKind::Write),
                    field_name: Some(access.field_name.clone()),
                    loop_context: loop_ctx,
                    hotness_score: hotness,
                    in_concurrent_context: self.access_is_concurrent(&access),
                    access_mode: access.access_mode,
                    function_name: self.current_function.clone(),
                    propagation_depth: 0,
                    call_path: Vec::new(),
                    semantic_contexts: access_semantic_contexts(&access),
                    through_shared_indirection: access.through_shared_indirection,
                    through_raw_pointer: access.through_raw_pointer,
                    description: format!(
                        "plain field write on path '{}' at {}:{line}",
                        access.access_path, self.file
                    ),
                    file: self.file.to_string(),
                    line,
                },
            );
        }
    }

    fn record_compound_field_write(&mut self, expr: &Expr, line: usize) {
        if let Some(access) = self.resolve_access(expr) {
            let loop_ctx = self.loop_analyzer.current_loop_context();
            let hotness = self.loop_analyzer.calculate_hotness(&loop_ctx);
            self.add_evidence(
                &access.struct_name,
                EvidenceItem {
                    kind: EvidenceKind::PlainFieldWrite,
                    access_kind: Some(AtomicAccessKind::ReadModifyWrite),
                    field_name: Some(access.field_name.clone()),
                    loop_context: loop_ctx,
                    hotness_score: hotness,
                    in_concurrent_context: self.access_is_concurrent(&access),
                    access_mode: access.access_mode,
                    function_name: self.current_function.clone(),
                    propagation_depth: 0,
                    call_path: Vec::new(),
                    semantic_contexts: access_semantic_contexts(&access),
                    through_shared_indirection: access.through_shared_indirection,
                    through_raw_pointer: access.through_raw_pointer,
                    description: format!(
                        "compound field write on path '{}' at {}:{line}",
                        access.access_path, self.file
                    ),
                    file: self.file.to_string(),
                    line,
                },
            );
        }
    }

    fn record_concurrent_field_access(&mut self, expr: &Expr, line: usize) {
        if let Some(access) = self.resolve_access(expr) {
            let loop_ctx = self.loop_analyzer.current_loop_context();
            let hotness = self.loop_analyzer.calculate_hotness(&loop_ctx);
            let indexed = if access.is_indexed { " indexed" } else { "" };
            self.add_evidence(
                &access.struct_name,
                EvidenceItem {
                    kind: EvidenceKind::FieldAccessInConcurrentContext,
                    access_kind: None,
                    field_name: Some(access.field_name.clone()),
                    loop_context: loop_ctx,
                    hotness_score: hotness,
                    in_concurrent_context: true,
                    access_mode: access.access_mode,
                    function_name: self.current_function.clone(),
                    propagation_depth: 0,
                    call_path: Vec::new(),
                    semantic_contexts: access_semantic_contexts(&access),
                    through_shared_indirection: access.through_shared_indirection,
                    through_raw_pointer: access.through_raw_pointer,
                    description: format!(
                        "{indexed}field access on path '{}' in concurrent context at {}:{line}",
                        access.access_path, self.file
                    ),
                    file: self.file.to_string(),
                    line,
                },
            );
        }
    }

    fn handle_local_binding(&mut self, node: &syn::Local) {
        if let Pat::Type(pat_ty) = &node.pat
            && let Some((name, mut binding)) = self.binding_from_pat_type(pat_ty)
        {
            binding.object_identity = node
                .init
                .as_ref()
                .and_then(|init| self.binding_from_expr(&init.expr))
                .and_then(|value| value.object_identity);
            if !crate::helpers::is_indirection_type(&pat_ty.ty.to_token_stream().to_string()) {
                binding.object_identity = Some(format!(
                    "value:{}:{}:{}",
                    self.file,
                    node.span().start().line,
                    node.span().start().column
                ));
            }
            self.bind_var(name, binding);
            return;
        }
        if let Some(binding) = node
            .init
            .as_ref()
            .and_then(|init| self.binding_from_expr(&init.expr))
        {
            self.bind_pattern_from_binding(&node.pat, &binding);
        } else if node
            .init
            .as_ref()
            .is_some_and(|init| self.expression_depends_on_symbolic(&init.expr))
        {
            self.bind_symbolic_pattern(&node.pat);
        }
    }

    fn bind_pattern_from_binding(&mut self, pattern: &Pat, binding: &VarBinding) {
        match pattern {
            Pat::Ident(ident) => {
                let mut bound = binding.clone();
                let name = ident.ident.to_string();
                bound.access_path = name.clone();
                self.bind_var(name, bound);
            }
            Pat::Reference(reference) => {
                self.bind_pattern_from_binding(&reference.pat, binding);
            }
            Pat::Type(pat_type) => self.bind_pattern_from_binding(&pat_type.pat, binding),
            Pat::Tuple(tuple) => {
                for element in &tuple.elems {
                    self.bind_pattern_from_binding(element, binding);
                }
            }
            Pat::TupleStruct(tuple) => {
                for element in &tuple.elems {
                    self.bind_pattern_from_binding(element, binding);
                }
            }
            Pat::Struct(record) => {
                for field in &record.fields {
                    self.bind_pattern_from_binding(&field.pat, binding);
                }
            }
            Pat::Slice(slice) => {
                for element in &slice.elems {
                    self.bind_pattern_from_binding(element, binding);
                }
            }
            Pat::Paren(paren) => self.bind_pattern_from_binding(&paren.pat, binding),
            _ => {}
        }
    }
}

impl<'ast, 'a> Visit<'ast> for EvidenceCollector<'a> {
    fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        if let Some((None, trait_path, _)) = &node.trait_
            && trait_path.segments.last().is_some_and(|segment| {
                matches!(segment.ident.to_string().as_str(), "Send" | "Sync")
            })
            && let Some(type_name) = concrete_type_name(&node.self_ty.to_token_stream().to_string())
        {
            let line = self.span_line(node);
            let trait_name = trait_path.segments.last().unwrap().ident.to_string();
            self.add_evidence(
                &type_name,
                EvidenceItem {
                    kind: EvidenceKind::SendSyncCapability,
                    access_kind: None,
                    field_name: None,
                    loop_context: None,
                    hotness_score: 1.0,
                    in_concurrent_context: false,
                    access_mode: AccessMode::Shared,
                    function_name: None,
                    propagation_depth: 0,
                    call_path: Vec::new(),
                    semantic_contexts: vec!["send_sync_capability".to_string()],
                    through_shared_indirection: false,
                    through_raw_pointer: false,
                    description: format!(
                        "explicit {trait_name} capability for {type_name} at {}:{line}",
                        self.file
                    ),
                    file: self.file.to_string(),
                    line,
                },
            );
        }
        let prev_type = self.current_impl_type.take();
        let prev_trait = self.current_impl_trait.take();
        let prev_generic = self.current_impl_is_generic;
        self.current_impl_type = concrete_type_name(&node.self_ty.to_token_stream().to_string());
        self.current_impl_trait = node.trait_.as_ref().and_then(|(_, path, _)| {
            path.segments
                .last()
                .map(|segment| segment.ident.to_string())
        });
        self.current_impl_is_generic = !node.generics.params.is_empty();
        syn::visit::visit_item_impl(self, node);
        self.current_impl_type = prev_type;
        self.current_impl_trait = prev_trait;
        self.current_impl_is_generic = prev_generic;
    }

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
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
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        let saved_guards = std::mem::take(&mut self.held_guards);
        let key = FunctionKey {
            crate_name: self.crate_name.clone(),
            module_path: self.module_path.clone(),
            owner: self.current_impl_type.clone(),
            trait_name: self.current_impl_trait.clone(),
            name: node.sig.ident.to_string(),
        };
        self.register_current_function(&key);
        let prev_function = self.current_function.replace(key.display_name());
        let prev_key = self.current_function_key.replace(key);
        let prev_contexts = std::mem::take(&mut self.current_semantic_contexts);
        self.current_semantic_contexts = function_semantic_contexts(
            &node.sig,
            self.current_impl_type.as_deref(),
            self.current_impl_trait.as_deref(),
            self.current_impl_is_generic,
        );
        if !matches!(node.vis, syn::Visibility::Inherited)
            || self.current_impl_trait.is_some()
            || self.escaped_functions.contains(&node.sig.ident.to_string())
        {
            self.current_semantic_contexts
                .push("rust_callable_exposed".into());
        }
        let prev_receiver_mode = self.current_receiver_mode.replace(AccessMode::Unknown);
        self.enter_scope();
        let mut parameter_index = 0;
        for input in &node.sig.inputs {
            match input {
                syn::FnArg::Receiver(receiver) => {
                    self.current_receiver_mode = Some(access_mode_from_receiver(receiver));
                }
                syn::FnArg::Typed(pat_ty) => {
                    self.bind_index_pattern(&pat_ty.pat, IndexValue::from_type(&pat_ty.ty));
                    if let Some((name, mut binding)) = self.binding_from_pat_type(pat_ty) {
                        let agent_local = binding.access_mode.is_exclusive();
                        binding.origin = Some(ValueOrigin::Parameter(parameter_index));
                        self.bind_var(name, binding);
                        if agent_local {
                            self.bind_symbolic_pattern(&pat_ty.pat);
                        }
                    } else {
                        if type_can_partition_agents(&pat_ty.ty.to_token_stream().to_string()) {
                            self.bind_symbolic_pattern(&pat_ty.pat);
                        }
                    }
                    parameter_index += 1;
                }
            }
        }
        syn::visit::visit_impl_item_fn(self, node);
        self.leave_scope();
        self.current_function = prev_function;
        self.current_function_key = prev_key;
        self.current_semantic_contexts = prev_contexts;
        self.current_receiver_mode = prev_receiver_mode;
        self.held_guards = saved_guards;
    }

    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        let saved_guards = std::mem::take(&mut self.held_guards);
        let key = FunctionKey {
            crate_name: self.crate_name.clone(),
            module_path: self.module_path.clone(),
            owner: None,
            trait_name: None,
            name: node.sig.ident.to_string(),
        };
        self.register_current_function(&key);
        let prev_function = self.current_function.replace(key.display_name());
        let prev_key = self.current_function_key.replace(key);
        let prev_contexts = std::mem::take(&mut self.current_semantic_contexts);
        self.current_semantic_contexts =
            function_semantic_contexts(&node.sig, None, None, !node.sig.generics.params.is_empty());
        if !matches!(node.vis, syn::Visibility::Inherited)
            || self.escaped_functions.contains(&node.sig.ident.to_string())
        {
            self.current_semantic_contexts
                .push("rust_callable_exposed".into());
        }
        self.enter_scope();
        let mut parameter_index = 0;
        for input in &node.sig.inputs {
            if let syn::FnArg::Typed(pat_ty) = input {
                self.bind_index_pattern(&pat_ty.pat, IndexValue::from_type(&pat_ty.ty));
            }
            if let syn::FnArg::Typed(pat_ty) = input
                && let Some((name, mut binding)) = self.binding_from_pat_type(pat_ty)
            {
                let agent_local = binding.access_mode.is_exclusive();
                binding.origin = Some(ValueOrigin::Parameter(parameter_index));
                self.bind_var(name, binding);
                if agent_local {
                    self.bind_symbolic_pattern(&pat_ty.pat);
                }
            } else if let syn::FnArg::Typed(pat_ty) = input
                && type_can_partition_agents(&pat_ty.ty.to_token_stream().to_string())
            {
                self.bind_symbolic_pattern(&pat_ty.pat);
            }
            if matches!(input, syn::FnArg::Typed(_)) {
                parameter_index += 1;
            }
        }
        syn::visit::visit_item_fn(self, node);
        self.leave_scope();
        self.current_function = prev_function;
        self.current_function_key = prev_key;
        self.current_semantic_contexts = prev_contexts;
        self.held_guards = saved_guards;
    }

    fn visit_block(&mut self, node: &'ast syn::Block) {
        self.enter_scope();
        // Items/imports are visible throughout their block, including before
        // their textual declaration. Unknown shadows cannot name a global
        // storage object or a native allocator/lock by spelling alone.
        let scope = self.scoped_indices.last_mut().unwrap();
        for statement in &node.stmts {
            let names = match statement {
                syn::Stmt::Item(syn::Item::Use(item)) => {
                    let mut imports = Vec::new();
                    collect_module_uses(&item.tree, &[], &mut imports);
                    imports
                        .into_iter()
                        .map(|(alias, _)| alias.unwrap_or_else(|| "*".into()))
                        .collect::<Vec<_>>()
                }
                syn::Stmt::Item(syn::Item::Const(item)) => vec![item.ident.to_string()],
                syn::Stmt::Item(syn::Item::Type(item)) => vec![item.ident.to_string()],
                syn::Stmt::Item(syn::Item::Mod(item)) => vec![item.ident.to_string()],
                _ => Vec::new(),
            };
            for name in names {
                scope.insert(
                    name,
                    IndexBinding {
                        value: IndexValue::Unknown,
                        mutable: false,
                    },
                );
            }
        }
        syn::visit::visit_block(self, node);
        if let Some(syn::Stmt::Expr(expr, None)) = node.stmts.last() {
            self.record_plain_value_read(expr, self.span_line(expr));
        }
        self.leave_scope();
    }

    fn visit_expr_closure(&mut self, node: &'ast syn::ExprClosure) {
        // The enclosing thread's lockset does not dominate a deferred worker.
        let saved = std::mem::take(&mut self.held_guards);
        self.current_semantic_contexts.push(format!(
            "rust_execution_domain:{}:{}:{}",
            self.file,
            node.span().start().line,
            node.span().start().column
        ));
        self.enter_scope();
        let saved_receiver_mode = self.current_receiver_mode;
        if node.capture.is_none() {
            // A borrowed owner is not exclusively owned by this closure. Atomic
            // fields in a stack/Box value can be shared by scoped workers.
            // Explicit mutable references and callee signatures still determine
            // the capability of operations that actually require exclusivity.
            let captured = self.scoped_vars[..self.scoped_vars.len() - 1]
                .iter()
                .flat_map(|scope| scope.iter())
                .map(|(name, binding)| {
                    let mut binding = binding.clone();
                    if binding.access_mode.is_exclusive() && !binding.through_raw_pointer {
                        binding.access_mode = AccessMode::Shared;
                    }
                    (name.clone(), binding)
                })
                .collect::<HashMap<_, _>>();
            self.scoped_vars.last_mut().unwrap().extend(captured);
            if self.current_receiver_mode == Some(AccessMode::Exclusive) {
                self.current_receiver_mode = Some(AccessMode::Shared);
            }
        }
        for input in &node.inputs {
            let value = match input {
                Pat::Type(pat_ty) => IndexValue::from_type(&pat_ty.ty),
                _ => IndexValue::Unknown,
            };
            self.bind_index_pattern(input, value);
            if let Pat::Type(pat_ty) = input
                && let Some((name, binding)) = self.binding_from_pat_type(pat_ty)
            {
                let agent_local = binding.access_mode.is_exclusive();
                self.bind_var(name, binding);
                if agent_local {
                    self.bind_symbolic_pattern(input);
                }
            } else if let Pat::Type(pat_ty) = input {
                if type_can_partition_agents(&pat_ty.ty.to_token_stream().to_string()) {
                    self.bind_symbolic_pattern(input);
                }
            } else {
                self.bind_symbolic_pattern(input);
            }
        }
        syn::visit::visit_expr_closure(self, node);
        self.current_semantic_contexts.pop();
        self.leave_scope();
        self.current_receiver_mode = saved_receiver_mode;
        self.held_guards = saved;
        self.invalidate_guards_used_by(&node.body);
    }

    fn visit_local(&mut self, node: &'ast syn::Local) {
        if let Some(init) = &node.init {
            self.record_plain_value_read(&init.expr, self.span_line(&init.expr));
        }
        let value = node
            .init
            .as_ref()
            .map(|init| self.index_value(&init.expr))
            .unwrap_or(IndexValue::Unknown);
        syn::visit::visit_local(self, node);
        // A let binding is not in scope in its own initializer.
        let guard = self.acquired_guard(node);
        self.handle_local_binding(node);
        self.bind_index_pattern(&node.pat, value);
        if let Some(guard) = guard {
            self.held_guards.push(guard);
        }
    }

    fn visit_expr_for_loop(&mut self, node: &'ast syn::ExprForLoop) {
        self.invalidate_loop_indices(&node.body);
        self.index_control_depth += 1;
        // Enter loop context
        self.loop_analyzer.current_depth += 1;
        let iter_est = crate::dataflow::LoopAnalyzer::estimate_iterations(&node.expr);
        self.loop_analyzer
            .loop_stack
            .push(crate::dataflow::LoopInfo {
                depth: self.loop_analyzer.current_depth,
                iteration_estimate: iter_est,
            });

        self.visit_expr(&node.expr);
        self.enter_scope();
        let range = match node.expr.as_ref() {
            Expr::Range(range) => range
                .start
                .as_deref()
                .and_then(|expr| self.index_value(expr).constant())
                .zip(
                    range
                        .end
                        .as_deref()
                        .and_then(|expr| self.index_value(expr).constant()),
                )
                .map(|(start, end)| {
                    (
                        start,
                        end.saturating_sub(start).saturating_add(usize::from(
                            matches!(range.limits, syn::RangeLimits::Closed(_)) && end >= start,
                        )),
                    )
                }),
            _ => None,
        };
        self.bind_index_pattern(
            &node.pat,
            match range {
                Some((start, 1)) => IndexValue::Constant(start),
                _ => IndexValue::Integer,
            },
        );
        if range.is_none_or(|(_, length)| length != 0) {
            self.visit_block(&node.body);
        }
        self.leave_scope();
        self.index_control_depth -= 1;

        // Exit loop context
        self.loop_analyzer.loop_stack.pop();
        self.loop_analyzer.current_depth = self.loop_analyzer.current_depth.saturating_sub(1);
    }

    fn visit_expr_while(&mut self, node: &'ast syn::ExprWhile) {
        self.invalidate_loop_indices(&node.body);
        self.index_control_depth += 1;
        self.loop_analyzer.current_depth += 1;
        self.loop_analyzer
            .loop_stack
            .push(crate::dataflow::LoopInfo {
                depth: self.loop_analyzer.current_depth,
                iteration_estimate: crate::types::IterationEstimate::Dynamic,
            });

        self.enter_scope();
        self.visit_expr(&node.cond);
        self.visit_block(&node.body);
        self.leave_scope();
        self.index_control_depth -= 1;

        self.loop_analyzer.loop_stack.pop();
        self.loop_analyzer.current_depth = self.loop_analyzer.current_depth.saturating_sub(1);
    }

    fn visit_expr_loop(&mut self, node: &'ast syn::ExprLoop) {
        self.invalidate_loop_indices(&node.body);
        self.index_control_depth += 1;
        self.loop_analyzer.current_depth += 1;
        self.loop_analyzer
            .loop_stack
            .push(crate::dataflow::LoopInfo {
                depth: self.loop_analyzer.current_depth,
                iteration_estimate: crate::types::IterationEstimate::Unknown,
            });

        syn::visit::visit_expr_loop(self, node);
        self.index_control_depth -= 1;

        self.loop_analyzer.loop_stack.pop();
        self.loop_analyzer.current_depth = self.loop_analyzer.current_depth.saturating_sub(1);
    }

    fn visit_expr_if(&mut self, node: &'ast syn::ExprIf) {
        self.index_control_depth += 1;
        let line = self.span_line(node);
        let symbolic_partition = match node.cond.as_ref() {
            Expr::Let(expr_let) => self.expression_depends_on_symbolic(&expr_let.expr),
            condition => self.expression_depends_on_symbolic(condition),
        };
        self.enter_scope();
        self.visit_expr(&node.cond);
        if symbolic_partition {
            self.current_semantic_contexts
                .push(format!("control_partition:then:{}:{line}", self.file));
        }
        self.visit_block(&node.then_branch);
        if symbolic_partition {
            self.current_semantic_contexts.pop();
        }
        self.leave_scope();
        if let Some((_, else_branch)) = &node.else_branch {
            if symbolic_partition {
                self.current_semantic_contexts
                    .push(format!("control_partition:else:{}:{line}", self.file));
            }
            self.visit_expr(else_branch);
            if symbolic_partition {
                self.current_semantic_contexts.pop();
            }
        }
        self.index_control_depth -= 1;
    }

    fn visit_expr_let(&mut self, node: &'ast syn::ExprLet) {
        // Conditions (including let chains) bind their patterns only after
        // evaluating the scrutinee. The enclosing if/while owns this scope.
        let symbolic = self.expression_depends_on_symbolic(&node.expr);
        self.visit_expr(&node.expr);
        self.bind_index_pattern(&node.pat, IndexValue::Unknown);
        if let Some(binding) = self.binding_from_expr(&node.expr) {
            self.bind_pattern_from_binding(&node.pat, &binding);
        } else if symbolic {
            self.bind_symbolic_pattern(&node.pat);
        }
    }

    fn visit_expr_match(&mut self, node: &'ast syn::ExprMatch) {
        self.index_control_depth += 1;
        let symbolic_partition = self.expression_depends_on_symbolic(&node.expr);
        self.visit_expr(&node.expr);
        let binding = self.binding_from_expr(&node.expr);
        for (index, arm) in node.arms.iter().enumerate() {
            self.enter_scope();
            self.bind_index_pattern(&arm.pat, IndexValue::Unknown);
            if let Some(binding) = &binding {
                self.bind_pattern_from_binding(&arm.pat, binding);
            } else if symbolic_partition {
                self.bind_symbolic_pattern(&arm.pat);
            }
            if let Some((_, guard)) = &arm.guard {
                self.visit_expr(guard);
            }
            if symbolic_partition {
                self.current_semantic_contexts.push(format!(
                    "control_partition:match:{}:{}:{index}",
                    self.file,
                    self.span_line(node)
                ));
            }
            self.visit_expr(&arm.body);
            if symbolic_partition {
                self.current_semantic_contexts.pop();
            }
            self.leave_scope();
        }
        self.index_control_depth -= 1;
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        self.invalidate_guards_used_by(&node.receiver);
        for argument in &node.args {
            self.invalidate_guards_used_by(argument);
        }
        if node.method == "force_unlock" {
            self.held_guards.clear();
        }
        if self
            .binding_from_expr(&node.receiver)
            .is_some_and(|binding| binding.outer_wrapper.is_some())
        {
            // Method lookup may auto-borrow a handle mutably. An unresolved
            // method can replace an Arc/Box slot, so do not carry its previous
            // pointee identity into this call or later accesses.
            self.invalidate_object_binding(&node.receiver);
        }
        self.invalidate_index_receiver(&node.receiver);
        self.check_sync_method_on_field(node);
        self.record_method_call_site(node);

        let method = node.method.to_string();
        let enters_concurrent = Self::is_spawn_or_scope(&method) || Self::is_parallel_iter(&method);

        if enters_concurrent {
            let kind = if Self::is_parallel_iter(&method) {
                EvidenceKind::UsedInParallelIter
            } else {
                EvidenceKind::UsedInSpawn
            };

            // If we're inside an impl, the struct itself is used in concurrent context
            if let Some(impl_ty) = self.current_impl_type.clone() {
                let line = self.span_line(node);
                let file = self.file.to_string();
                self.add_evidence(
                    &impl_ty,
                    EvidenceItem {
                        kind: kind.clone(),
                        access_kind: None,
                        field_name: None,
                        loop_context: None,
                        hotness_score: 1.0,
                        in_concurrent_context: true,
                        access_mode: AccessMode::Unknown,
                        function_name: self.current_function.clone(),
                        propagation_depth: 0,
                        call_path: Vec::new(),
                        semantic_contexts: Vec::new(),
                        through_shared_indirection: false,
                        through_raw_pointer: false,
                        description: format!("'.{method}()' call inside impl at {file}:{line}"),
                        file,
                        line,
                    },
                );
            }

            self.visit_expr(&node.receiver);
            self.enter_concurrent();
            for arg in &node.args {
                self.visit_expr(arg);
            }
            self.leave_concurrent();
            return;
        }

        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_expr_macro(&mut self, node: &'ast syn::ExprMacro) {
        self.invalidate_opaque_macro_effects();
        // Macro input tokens are not ordinary visited expressions. A mutable
        // identifier may be assigned or have its address taken by expansion.
        for name in token_identifiers(&node.mac.tokens) {
            self.invalidate_mutable_index(&name);
        }
        self.record_macro_expansion_access(node);
        syn::visit::visit_expr_macro(self, node);
    }

    fn visit_stmt_macro(&mut self, node: &'ast syn::StmtMacro) {
        self.invalidate_opaque_macro_effects();
        for name in token_identifiers(&node.mac.tokens) {
            self.invalidate_mutable_index(&name);
        }
        syn::visit::visit_stmt_macro(self, node);
    }

    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        for argument in &node.args {
            self.invalidate_guards_used_by(argument);
        }
        self.record_function_call_site(node);
        let is_concurrent = is_concurrent_call(&node.func);

        if is_concurrent {
            if let Some(impl_ty) = self.current_impl_type.clone() {
                let line = self.span_line(node);
                let file = self.file.to_string();
                self.add_evidence(
                    &impl_ty,
                    EvidenceItem {
                        kind: EvidenceKind::UsedInSpawn,
                        access_kind: None,
                        field_name: None,
                        loop_context: None,
                        hotness_score: 1.0,
                        in_concurrent_context: true,
                        access_mode: AccessMode::Unknown,
                        function_name: self.current_function.clone(),
                        propagation_depth: 0,
                        call_path: Vec::new(),
                        semantic_contexts: Vec::new(),
                        through_shared_indirection: false,
                        through_raw_pointer: false,
                        description: format!("concurrent call inside impl at {file}:{line}"),
                        file,
                        line,
                    },
                );
            }

            self.visit_expr(&node.func);
            self.enter_concurrent();
            for arg in &node.args {
                self.visit_expr(arg);
            }
            self.leave_concurrent();
            return;
        }

        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_reference(&mut self, node: &'ast syn::ExprReference) {
        if node.mutability.is_some() {
            self.invalidate_guards_used_by(&node.expr);
            self.invalidate_object_binding(&node.expr);
            // The borrow can escape through either a call or a local alias.
            self.assign_index(&node.expr, IndexValue::Integer);
        }
        syn::visit::visit_expr_reference(self, node);
    }

    fn visit_expr_raw_addr(&mut self, node: &'ast syn::ExprRawAddr) {
        if matches!(node.mutability, syn::PointerMutability::Mut(_)) {
            self.assign_index(&node.expr, IndexValue::Integer);
        }
        syn::visit::visit_expr_raw_addr(self, node);
    }

    fn visit_expr_field(&mut self, node: &'ast ExprField) {
        if self.in_concurrent_context {
            self.record_concurrent_field_access(&Expr::Field(node.clone()), self.span_line(node));
        }
        syn::visit::visit_expr_field(self, node);
    }

    fn visit_expr_return(&mut self, node: &'ast syn::ExprReturn) {
        if let Some(expr) = &node.expr {
            self.record_plain_value_read(expr, self.span_line(expr));
        }
        syn::visit::visit_expr_return(self, node);
    }

    fn visit_expr_assign(&mut self, node: &'ast syn::ExprAssign) {
        self.invalidate_guards_used_by(&node.left);
        self.invalidate_object_binding(&node.left);
        let line = self.span_line(node);
        self.record_plain_field_write(&node.left, line);
        self.assign_index(&node.left, self.index_value(&node.right));
        syn::visit::visit_expr_assign(self, node);
    }

    fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
        if is_compound_assign(&node.op) {
            let line = self.span_line(node);
            self.record_compound_field_write(&node.left, line);
            self.assign_index(&node.left, IndexValue::Integer);
        } else {
            self.record_plain_value_read(&node.left, self.span_line(&node.left));
            self.record_plain_value_read(&node.right, self.span_line(&node.right));
        }
        syn::visit::visit_expr_binary(self, node);
    }

    fn visit_expr_async(&mut self, node: &'ast syn::ExprAsync) {
        let saved = std::mem::take(&mut self.held_guards);
        self.async_context_depth += 1;
        syn::visit::visit_expr_async(self, node);
        self.async_context_depth = self.async_context_depth.saturating_sub(1);
        self.held_guards = saved;
        self.invalidate_guards_used_by(&Expr::Async(node.clone()));
    }

    fn visit_expr_unsafe(&mut self, node: &'ast syn::ExprUnsafe) {
        self.unsafe_context_depth += 1;
        syn::visit::visit_expr_unsafe(self, node);
        self.unsafe_context_depth = self.unsafe_context_depth.saturating_sub(1);
    }
}

fn function_semantic_contexts(
    signature: &syn::Signature,
    owner: Option<&str>,
    trait_name: Option<&str>,
    impl_is_generic: bool,
) -> Vec<String> {
    let mut contexts = Vec::new();
    if trait_name.is_some() {
        contexts.push("trait_impl".to_string());
    }
    if trait_name == Some("Clone") {
        contexts.push("clone_impl".to_string());
    }
    if trait_name == Some("Drop") {
        contexts.push("drop_impl".to_string());
    }
    if impl_is_generic || !signature.generics.params.is_empty() {
        contexts.push("generic".to_string());
    }
    if signature.asyncness.is_some() {
        contexts.push("async_fn".to_string());
    }
    if signature.unsafety.is_some() {
        contexts.push("unsafe_fn".to_string());
    }
    if signature.inputs.iter().any(
        |input| matches!(input, syn::FnArg::Receiver(receiver) if receiver.reference.is_none()),
    ) {
        contexts.push("consuming_self".to_string());
    }
    if owner.is_some_and(is_handle_like_type)
        && is_handle_lifecycle_method(&signature.ident.to_string())
    {
        contexts.push("handle_lifecycle".to_string());
    }
    contexts
}

fn is_handle_like_type(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    [
        "handle",
        "guard",
        "sender",
        "receiver",
        "worker",
        "permit",
        "token",
        "task",
        "lease",
        "connection",
        "channel",
    ]
    .iter()
    .any(|token| lower.contains(token))
}

fn is_handle_lifecycle_method(name: &str) -> bool {
    matches!(
        name,
        "clone"
            | "drop"
            | "close"
            | "shutdown"
            | "disconnect"
            | "register"
            | "unregister"
            | "attach"
            | "detach"
            | "acquire"
            | "release"
            | "downgrade"
            | "upgrade"
    )
}

fn looks_like_type_or_trait_name(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

fn owned_default_types(files: &[ParsedFile]) -> HashSet<StructKey> {
    struct Defaults {
        crate_name: String,
        module: String,
        derived: HashSet<StructKey>,
        shadowed_crates: HashSet<String>,
    }
    impl<'ast> Visit<'ast> for Defaults {
        fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
            let previous = self.module.clone();
            self.module = join_module_path(&self.module, &node.ident.to_string());
            syn::visit::visit_item_mod(self, node);
            self.module = previous;
        }
        fn visit_item_struct(&mut self, node: &'ast syn::ItemStruct) {
            let key = StructKey::new(
                self.crate_name.clone(),
                self.module.clone(),
                node.ident.to_string(),
            );
            let mut default = false;
            for attr in &node.attrs {
                if attr.path().is_ident("derive") {
                    let Ok(paths) =
                        attr.parse_args_with(Punctuated::<syn::Path, Token![,]>::parse_terminated)
                    else {
                        return;
                    };
                    if paths.iter().any(|path| {
                        ![
                            "Default",
                            "Debug",
                            "Clone",
                            "Copy",
                            "PartialEq",
                            "Eq",
                            "Ord",
                            "PartialOrd",
                            "Hash",
                        ]
                        .iter()
                        .any(|name| path.is_ident(name))
                    }) {
                        return;
                    }
                    default |= paths.iter().any(|path| path.is_ident("Default"));
                } else if ![
                    "repr",
                    "doc",
                    "cfg",
                    "cfg_attr",
                    "allow",
                    "deny",
                    "warn",
                    "forbid",
                    "must_use",
                    "non_exhaustive",
                ]
                .iter()
                .any(|name| attr.path().is_ident(name))
                {
                    return;
                }
            }
            if default {
                self.derived.insert(key);
            }
        }
        fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
            if node.trait_.is_none() && node.items.iter().any(|item| matches!(item, syn::ImplItem::Fn(method) if method.sig.ident == "default")) {
                // Qualified/aliased self types need name resolution. Until
                // proved, do not use a guessed Default return type to establish
                // distinct allocations anywhere in this crate.
                self.shadowed_crates.insert(self.crate_name.clone());
            }
            syn::visit::visit_item_impl(self, node);
        }
    }
    let mut collector = Defaults {
        crate_name: String::new(),
        module: String::new(),
        derived: HashSet::new(),
        shadowed_crates: HashSet::new(),
    };
    for file in files {
        collector.crate_name = file.crate_name.clone().unwrap_or_else(|| "unknown".into());
        collector.module = file.module_path.clone();
        collector.visit_file(&file.ast);
    }
    collector
        .derived
        .retain(|key| !collector.shadowed_crates.contains(&key.crate_name));
    collector.derived
}

fn escaped_callable_names(files: &[ParsedFile]) -> HashSet<String> {
    struct Escapes(HashSet<String>);
    impl<'ast> Visit<'ast> for Escapes {
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if !matches!(node.func.as_ref(), Expr::Path(_)) {
                self.visit_expr(&node.func);
            }
            for argument in &node.args {
                self.visit_expr(argument);
            }
        }
        fn visit_expr_path(&mut self, node: &'ast syn::ExprPath) {
            if let Some(name) = node.path.segments.last() {
                self.0.insert(name.ident.to_string());
            }
        }
        fn visit_expr_macro(&mut self, node: &'ast syn::ExprMacro) {
            self.0.extend(token_identifiers(&node.mac.tokens));
        }
        fn visit_stmt_macro(&mut self, node: &'ast syn::StmtMacro) {
            self.0.extend(token_identifiers(&node.mac.tokens));
        }
    }
    let mut escapes = Escapes(HashSet::new());
    for file in files {
        escapes.visit_file(&file.ast);
    }
    escapes.0
}

fn indexed_pointee_type(container: &str, receiver: &Expr) -> bool {
    fn argument(ty: &syn::Type) -> Option<&syn::Type> {
        let syn::Type::Path(path) = ty else {
            return None;
        };
        let syn::PathArguments::AngleBracketed(args) = &path.path.segments.last()?.arguments else {
            return None;
        };
        args.args.iter().find_map(|arg| match arg {
            syn::GenericArgument::Type(ty) => Some(ty),
            _ => None,
        })
    }
    fn element(ty: &syn::Type) -> Option<&syn::Type> {
        match ty {
            syn::Type::Array(array) => Some(&array.elem),
            syn::Type::Slice(slice) => Some(&slice.elem),
            syn::Type::Path(path) => match path.path.segments.last()?.ident.to_string().as_str() {
                "Vec" => argument(ty),
                "Box" | "Arc" => element(argument(ty)?),
                _ => None,
            },
            _ => None,
        }
    }
    fn indirect(ty: &syn::Type) -> bool {
        match ty {
            syn::Type::Reference(_) | syn::Type::Ptr(_) => true,
            syn::Type::Path(path) => path.path.segments.last().is_some_and(|segment| {
                matches!(
                    segment.ident.to_string().as_str(),
                    "Arc" | "Rc" | "Box" | "NonNull"
                )
            }),
            _ => false,
        }
    }
    fn projections(expression: &Expr, members: &mut Vec<syn::Member>) {
        match expression {
            Expr::Field(field) => {
                projections(&field.base, members);
                members.push(field.member.clone());
            }
            Expr::Paren(expr) => projections(&expr.expr, members),
            Expr::Reference(expr) => projections(&expr.expr, members),
            // Stop at the selected element; enclosing fields identify its array.
            _ => {}
        }
    }
    let Ok(container) = syn::parse_str::<syn::Type>(container) else {
        return false;
    };
    let Some(mut ty) = element(&container) else {
        return false;
    };
    let mut members = Vec::new();
    projections(receiver, &mut members);
    for member in members {
        if indirect(ty) {
            return true;
        }
        match (ty, member) {
            (syn::Type::Tuple(tuple), syn::Member::Unnamed(index)) => {
                let Some(next) = tuple.elems.iter().nth(index.index as usize) else {
                    return false;
                };
                ty = next;
            }
            _ => return false,
        }
    }
    indirect(ty)
}

fn access_semantic_contexts(access: &ResolvedAccess) -> Vec<String> {
    let mut contexts = Vec::new();
    if let Some(identity) = &access.object_identity {
        contexts.push(format!("rust_object_identity:{identity}"));
    }
    match &access.object_suffix {
        Some(suffix) if !suffix.is_empty() => contexts.push(format!("rust_object_suffix:{suffix}")),
        None => contexts.push("rust_object_suffix_unresolved".to_string()),
        _ => {}
    }
    if let Some(index) = access.element_index {
        contexts.push(index.context());
    }
    if access.through_shared_indirection {
        contexts.push("shared_indirection".to_string());
    }
    if access.through_raw_pointer {
        contexts.push("raw_pointer".to_string());
    }
    if access.through_wrapper_projection {
        contexts.push("transparent_wrapper_projection".to_string());
    }
    if let Some(origin) = access.origin {
        contexts.push(value_origin_context(origin));
    }
    contexts
}

fn collect_pattern_identifiers(pattern: &Pat, output: &mut Vec<String>) {
    struct Identifiers<'a>(&'a mut Vec<String>);
    impl<'ast> Visit<'ast> for Identifiers<'_> {
        fn visit_pat_ident(&mut self, node: &'ast syn::PatIdent) {
            self.0.push(node.ident.to_string());
            syn::visit::visit_pat_ident(self, node);
        }
    }
    Identifiers(output).visit_pat(pattern);
}

fn index_local_name(expression: &Expr) -> Option<String> {
    match expression {
        Expr::Path(path) => path.path.get_ident().map(ToString::to_string),
        Expr::Paren(expr) => index_local_name(&expr.expr),
        Expr::Group(expr) => index_local_name(&expr.expr),
        _ => None,
    }
}

fn token_identifiers(tokens: &proc_macro2::TokenStream) -> Vec<String> {
    let mut identifiers = Vec::new();
    let mut pending: Vec<_> = tokens.clone().into_iter().collect();
    while let Some(token) = pending.pop() {
        match token {
            proc_macro2::TokenTree::Ident(name) => identifiers.push(name.to_string()),
            proc_macro2::TokenTree::Group(group) => pending.extend(group.stream()),
            _ => {}
        }
    }
    identifiers
}

fn type_can_partition_agents(ty: &str) -> bool {
    let compact: String = ty
        .chars()
        .filter(|character| !character.is_whitespace())
        .collect();
    let collection_like = [
        "Vec<",
        "VecDeque<",
        "HashMap<",
        "BTreeMap<",
        "HashSet<",
        "BTreeSet<",
        "BinaryHeap<",
        "LinkedList<",
        "String",
        "str",
        "[",
    ]
    .iter()
    .any(|shape| compact.contains(shape));
    !collection_like
}

fn value_origin_context(origin: ValueOrigin) -> String {
    match origin {
        ValueOrigin::Receiver => "value_origin:receiver".to_string(),
        ValueOrigin::Parameter(index) => format!("value_origin:parameter:{index}"),
    }
}

fn semantic_value_origin(contexts: &[String]) -> Option<ValueOrigin> {
    contexts.iter().find_map(|context| {
        if context == "value_origin:receiver" {
            Some(ValueOrigin::Receiver)
        } else {
            context
                .strip_prefix("value_origin:parameter:")
                .and_then(|index| index.parse().ok())
                .map(ValueOrigin::Parameter)
        }
    })
}

fn replace_semantic_value_origin(contexts: &mut Vec<String>, origin: Option<ValueOrigin>) {
    contexts.retain(|context| !context.starts_with("value_origin:"));
    if let Some(origin) = origin {
        contexts.push(value_origin_context(origin));
    }
}

fn push_function_access(summary: &mut FunctionSummary, mut access: FunctionAccess) -> bool {
    access.item.semantic_contexts.sort();
    access.item.semantic_contexts.dedup();
    let identity = function_access_identity(&access);
    if let Some(existing) = summary
        .accesses
        .iter_mut()
        .find(|item| function_access_identity(item) == identity)
    {
        if access.item.hotness_score > existing.item.hotness_score {
            existing.item.hotness_score = access.item.hotness_score;
            existing.item.loop_context = access.item.loop_context;
        }
        if access.item.propagation_depth < existing.item.propagation_depth
            || (access.item.propagation_depth == existing.item.propagation_depth
                && access.item.call_path < existing.item.call_path)
        {
            existing.item.propagation_depth = access.item.propagation_depth;
            existing.item.call_path = access.item.call_path;
            existing.item.description = access.item.description;
        }
        return false;
    }
    if summary.accesses.len() >= MAX_ACCESSES_PER_FUNCTION {
        summary.truncated_accesses = summary.truncated_accesses.saturating_add(1);
        return false;
    }
    summary.accesses.push(access);
    true
}

fn function_access_identity(access: &FunctionAccess) -> String {
    let mut contexts = access.item.semantic_contexts.clone();
    contexts.sort();
    contexts.dedup();
    format!(
        "{}:{}:{:?}:{:?}:{:?}:{}:{}:{}:{}:{}:{}",
        access.struct_key.crate_name,
        access.struct_key.qualified_name(),
        access.item.kind,
        access.item.access_kind,
        access.item.access_mode,
        access.item.field_name.as_deref().unwrap_or(""),
        access.item.function_name.as_deref().unwrap_or(""),
        access.item.in_concurrent_context,
        access.item.through_shared_indirection,
        access.item.through_raw_pointer,
        contexts.join(","),
    )
}

fn propagate_function_summaries(
    evidence_map: &mut HashMap<StructKey, ConcurrencyEvidenceSet>,
    summaries: &mut HashMap<FunctionKey, FunctionSummary>,
    call_sites: &[FunctionCallSite],
) -> usize {
    let mut truncated_facts = 0usize;
    for _ in 0..MAX_INTERPROCEDURAL_DEPTH {
        let snapshot = summaries.clone();
        let known_functions: Vec<FunctionKey> = snapshot.keys().cloned().collect();
        let mut additions: Vec<(FunctionKey, FunctionAccess)> = Vec::new();

        for call in call_sites {
            let resolved_callees = resolve_callees(call, &known_functions);
            truncated_facts =
                truncated_facts.saturating_add(resolved_callees.len().saturating_sub(8));
            for callee in resolved_callees.into_iter().take(8) {
                let Some(callee_summary) = snapshot.get(&callee) else {
                    continue;
                };
                for access in &callee_summary.accesses {
                    if access.item.propagation_depth >= MAX_INTERPROCEDURAL_DEPTH {
                        truncated_facts = truncated_facts.saturating_add(1);
                        continue;
                    }
                    let mut propagated = access.clone();
                    let value_binding = semantic_value_origin(&propagated.item.semantic_contexts)
                        .and_then(|origin| match origin {
                            ValueOrigin::Receiver => call.receiver_binding.as_ref(),
                            ValueOrigin::Parameter(index) => {
                                call.argument_bindings.get(index).and_then(Option::as_ref)
                            }
                        });
                    let call_through_shared = value_binding
                        .is_some_and(|binding| binding.through_shared_indirection)
                        || (semantic_value_origin(&propagated.item.semantic_contexts).is_none()
                            && call.through_shared_indirection);
                    let call_through_raw = value_binding
                        .is_some_and(|binding| binding.through_raw_pointer)
                        || (semantic_value_origin(&propagated.item.semantic_contexts).is_none()
                            && call.through_raw_pointer);
                    if let Some(binding) = value_binding {
                        let suffix = propagated
                            .item
                            .semantic_contexts
                            .iter()
                            .find_map(|context| context.strip_prefix("rust_object_suffix:"))
                            .unwrap_or("")
                            .to_owned();
                        let unresolved = binding.object_suffix.is_none()
                            || propagated
                                .item
                                .semantic_contexts
                                .iter()
                                .any(|context| context == "rust_object_suffix_unresolved");
                        propagated.item.semantic_contexts.retain(|context| {
                            !context.starts_with("rust_object_suffix:")
                                && context != "rust_object_suffix_unresolved"
                        });
                        if unresolved {
                            propagated
                                .item
                                .semantic_contexts
                                .retain(|context| !context.starts_with("rust_object_identity:"));
                            propagated
                                .item
                                .semantic_contexts
                                .push("rust_object_suffix_unresolved".into());
                        } else if let Some(identity) = &binding.object_identity {
                            propagated
                                .item
                                .semantic_contexts
                                .retain(|context| !context.starts_with("rust_object_identity:"));
                            propagated
                                .item
                                .semantic_contexts
                                .push(format!("rust_object_identity:{identity}{suffix}"));
                        } else {
                            let suffix = format!(
                                "{}{suffix}",
                                binding.object_suffix.as_deref().unwrap_or("")
                            );
                            if !suffix.is_empty() {
                                propagated
                                    .item
                                    .semantic_contexts
                                    .push(format!("rust_object_suffix:{suffix}"));
                            }
                        }
                        replace_semantic_value_origin(
                            &mut propagated.item.semantic_contexts,
                            binding.origin,
                        );
                    }
                    propagated.item.propagation_depth += 1;
                    propagated.item.through_shared_indirection |= call_through_shared;
                    propagated.item.through_raw_pointer |= call_through_raw;
                    if call_through_raw {
                        propagated.item.access_mode = AccessMode::Unknown;
                    }
                    if propagated.item.through_shared_indirection
                        && !propagated
                            .item
                            .semantic_contexts
                            .iter()
                            .any(|context| context == "shared_indirection")
                    {
                        propagated
                            .item
                            .semantic_contexts
                            .push("shared_indirection".to_string());
                    }
                    if propagated.item.through_raw_pointer
                        && !propagated
                            .item
                            .semantic_contexts
                            .iter()
                            .any(|context| context == "raw_pointer")
                    {
                        propagated
                            .item
                            .semantic_contexts
                            .push("raw_pointer".to_string());
                    }
                    let lifecycle_on_shared = propagated.item.through_shared_indirection
                        && call.semantic_contexts.iter().any(|context| {
                            matches!(
                                context.as_str(),
                                "clone_impl" | "drop_impl" | "handle_lifecycle"
                            )
                        });
                    propagated.item.in_concurrent_context |=
                        call.in_concurrent_context || lifecycle_on_shared;
                    propagated.item.hotness_score =
                        propagated.item.hotness_score.max(call.hotness_score);
                    for context in &call.semantic_contexts {
                        if !propagated.item.semantic_contexts.contains(context) {
                            propagated.item.semantic_contexts.push(context.clone());
                        }
                    }
                    let caller_name = call.caller.display_name();
                    if propagated.item.call_path.first() != Some(&caller_name) {
                        propagated.item.call_path.insert(0, caller_name.clone());
                    }
                    propagated.item.description = format!(
                        "interprocedural access via '{}' -> '{}' at {}:{} (depth {}): {}",
                        caller_name,
                        callee.display_name(),
                        call.file,
                        call.line,
                        propagated.item.propagation_depth,
                        propagated.item.description
                    );
                    additions.push((call.caller.clone(), propagated));
                }
            }
        }

        let mut changed = false;
        for (caller, access) in additions {
            changed |= push_function_access(summaries.entry(caller).or_default(), access);
        }
        if !changed {
            break;
        }
    }

    for summary in summaries.values() {
        for access in summary
            .accesses
            .iter()
            .filter(|access| access.item.propagation_depth > 0)
        {
            let evidence = &mut evidence_map
                .entry(access.struct_key.clone())
                .or_default()
                .evidence;
            let identity = function_access_identity(access);
            if let Some(existing) = evidence.iter_mut().find(|item| {
                function_access_identity(&FunctionAccess {
                    struct_key: access.struct_key.clone(),
                    item: (**item).clone(),
                }) == identity
            }) {
                if access.item.hotness_score > existing.hotness_score {
                    existing.hotness_score = access.item.hotness_score;
                    existing.loop_context = access.item.loop_context.clone();
                }
                if access.item.propagation_depth < existing.propagation_depth
                    || (access.item.propagation_depth == existing.propagation_depth
                        && access.item.call_path < existing.call_path)
                {
                    existing.propagation_depth = access.item.propagation_depth;
                    existing.call_path = access.item.call_path.clone();
                    existing.description = access.item.description.clone();
                }
            } else {
                evidence.push(access.item.clone());
            }
        }
    }
    truncated_facts
}

fn sort_evidence_sets(evidence_map: &mut HashMap<StructKey, ConcurrencyEvidenceSet>) {
    for set in evidence_map.values_mut() {
        for item in &mut set.evidence {
            item.semantic_contexts.sort();
            item.semantic_contexts.dedup();
        }
        set.evidence.sort_by(|left, right| {
            left.file
                .cmp(&right.file)
                .then(left.line.cmp(&right.line))
                .then(left.field_name.cmp(&right.field_name))
                .then(evidence_kind_rank(&left.kind).cmp(&evidence_kind_rank(&right.kind)))
                .then(
                    access_kind_rank(left.access_kind.as_ref())
                        .cmp(&access_kind_rank(right.access_kind.as_ref())),
                )
                .then(access_mode_rank(left.access_mode).cmp(&access_mode_rank(right.access_mode)))
                .then(left.propagation_depth.cmp(&right.propagation_depth))
                .then(left.call_path.cmp(&right.call_path))
                .then(left.semantic_contexts.cmp(&right.semantic_contexts))
                .then(left.description.cmp(&right.description))
        });
    }
}

fn evidence_kind_rank(kind: &EvidenceKind) -> u8 {
    match kind {
        EvidenceKind::ArcWrapped => 0,
        EvidenceKind::MutexWrapped => 1,
        EvidenceKind::RwLockWrapped => 2,
        EvidenceKind::SendSyncCapability => 3,
        EvidenceKind::UsedInSpawn => 4,
        EvidenceKind::UsedInParallelIter => 5,
        EvidenceKind::AtomicFieldOps => 6,
        EvidenceKind::HotSyncFieldOps => 7,
        EvidenceKind::PlainFieldWrite => 8,
        EvidenceKind::PlainFieldRead => 10,
        EvidenceKind::FieldAccessInConcurrentContext => 9,
    }
}

fn access_kind_rank(kind: Option<&AtomicAccessKind>) -> u8 {
    match kind {
        None => 0,
        Some(AtomicAccessKind::Read) => 1,
        Some(AtomicAccessKind::Write) => 2,
        Some(AtomicAccessKind::ReadModifyWrite) => 3,
    }
}

fn access_mode_rank(mode: AccessMode) -> u8 {
    match mode {
        AccessMode::Unknown => 0,
        AccessMode::Shared => 1,
        AccessMode::Exclusive => 2,
    }
}

fn resolve_callees(call: &FunctionCallSite, functions: &[FunctionKey]) -> Vec<FunctionKey> {
    let mut matches: Vec<FunctionKey> = match &call.callee {
        CalleeRef::Method {
            owner,
            owner_module,
            trait_name,
            name,
        } => {
            let candidates: Vec<FunctionKey> = functions
                .iter()
                .filter(|function| {
                    function.crate_name == call.caller.crate_name
                        && function.owner.as_deref() == Some(owner)
                        && function.name == *name
                        && trait_name
                            .as_ref()
                            .is_none_or(|expected| function.trait_name.as_ref() == Some(expected))
                })
                .cloned()
                .collect();
            let module_matches: Vec<FunctionKey> = owner_module
                .as_ref()
                .map(|module| {
                    candidates
                        .iter()
                        .filter(|function| function.module_path == *module)
                        .cloned()
                        .collect()
                })
                .unwrap_or_default();
            if module_matches.len() == 1 {
                module_matches
            } else if candidates.len() == 1 {
                candidates
            } else {
                Vec::new()
            }
        }
        CalleeRef::Free { path, name } => {
            let exact_module = free_call_module(&call.caller.module_path, path);
            let exact: Vec<FunctionKey> = functions
                .iter()
                .filter(|function| {
                    function.crate_name == call.caller.crate_name
                        && function.owner.is_none()
                        && function.name == *name
                        && function.module_path == exact_module
                })
                .cloned()
                .collect();
            if !exact.is_empty() {
                exact
            } else if path.len() == 1 {
                let candidates: Vec<FunctionKey> = functions
                    .iter()
                    .filter(|function| {
                        function.crate_name == call.caller.crate_name
                            && function.owner.is_none()
                            && function.name == *name
                    })
                    .cloned()
                    .collect();
                if candidates.len() == 1 {
                    candidates
                } else {
                    Vec::new()
                }
            } else {
                Vec::new()
            }
        }
    };
    matches.sort_by_key(FunctionKey::display_name);
    matches.dedup();
    matches
}

fn free_call_module(current_module: &str, path: &[String]) -> String {
    if path.len() <= 1 {
        return current_module.to_string();
    }
    let mut module_segments = path[..path.len() - 1].to_vec();
    if module_segments
        .first()
        .is_some_and(|segment| segment == "crate")
    {
        module_segments.remove(0);
        return module_segments.join("::");
    }
    if module_segments
        .first()
        .is_some_and(|segment| segment == "self")
    {
        module_segments.remove(0);
        return join_module_path(current_module, &module_segments.join("::"));
    }
    if module_segments
        .first()
        .is_some_and(|segment| segment == "super")
    {
        module_segments.remove(0);
        let parent = current_module
            .rsplit_once("::")
            .map_or("", |(base, _)| base);
        return join_module_path(parent, &module_segments.join("::"));
    }
    module_segments.join("::")
}

fn build_struct_field_index(structs: &[StructInfo]) -> HashMap<StructKey, HashMap<String, String>> {
    let mut index = HashMap::new();
    for si in structs {
        let fields = si
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.ty_str.clone()))
            .collect();
        index.insert(StructKey::from_struct(si), fields);
    }
    index
}

// Module-level imports only. Function-local imports must not leak into sibling
// functions; unresolved external/re-export paths remain outside this summary.
fn collect_module_uses(
    tree: &syn::UseTree,
    prefix: &[String],
    output: &mut Vec<(Option<String>, Vec<String>)>,
) {
    let mut path = prefix.to_vec();
    match tree {
        syn::UseTree::Path(item) => {
            path.push(item.ident.to_string());
            collect_module_uses(&item.tree, &path, output);
        }
        syn::UseTree::Name(item) => {
            path.push(item.ident.to_string());
            output.push((Some(item.ident.to_string()), path));
        }
        syn::UseTree::Rename(item) => {
            path.push(item.ident.to_string());
            output.push((Some(item.rename.to_string()), path));
        }
        syn::UseTree::Glob(_) => output.push((None, path)),
        syn::UseTree::Group(group) => {
            for item in &group.items {
                collect_module_uses(item, &path, output);
            }
        }
    }
}

fn resolve_module_use_path(module: &str, path: &[String]) -> Vec<String> {
    let mut result: Vec<String> = Vec::new();
    let mut parts = path.iter().peekable();
    match parts.peek().map(|part| part.as_str()) {
        Some("crate") => {
            parts.next();
        }
        Some("self" | "super") => {
            result.extend(
                module
                    .split("::")
                    .filter(|p| !p.is_empty())
                    .map(str::to_string),
            );
        }
        _ => {}
    }
    for part in parts {
        match part.as_str() {
            "self" => {}
            "super" => {
                result.pop();
            }
            _ => result.push(part.clone()),
        }
    }
    result
}

fn collect_semantic_declarations(files: &[ParsedFile]) -> SemanticDeclarationIndex {
    let mut index = SemanticDeclarationIndex::default();
    for file in files {
        let mut collector = SemanticDeclarationCollector {
            crate_name: file
                .crate_name
                .clone()
                .unwrap_or_else(|| "unknown".to_string()),
            module_path: file.module_path.clone(),
            index: &mut index,
            block_depth: 0,
        };
        collector.visit_file(&file.ast);
    }
    index
}

struct SemanticDeclarationCollector<'a> {
    block_depth: usize,
    crate_name: String,
    module_path: String,
    index: &'a mut SemanticDeclarationIndex,
}

impl<'ast> Visit<'ast> for SemanticDeclarationCollector<'_> {
    fn visit_block(&mut self, node: &'ast syn::Block) {
        self.block_depth += 1;
        syn::visit::visit_block(self, node);
        self.block_depth -= 1;
    }

    fn visit_item_use(&mut self, node: &'ast syn::ItemUse) {
        if self.block_depth != 0 || cfg_is_test_only(&node.attrs) {
            return;
        }
        let mut imports = Vec::new();
        collect_module_uses(&node.tree, &[], &mut imports);
        self.index
            .imports
            .entry((self.crate_name.clone(), self.module_path.clone()))
            .or_default()
            .extend(
                imports.into_iter().map(|(alias, path)| {
                    (alias, resolve_module_use_path(&self.module_path, &path))
                }),
            );
    }

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        let namespace = node.ident.to_string();
        if matches!(namespace.as_str(), "std" | "alloc" | "parking_lot") {
            self.index
                .native_namespace_shadows
                .insert((self.crate_name.clone(), namespace));
        }
        let Some((_, items)) = &node.content else {
            return;
        };
        let previous = self.module_path.clone();
        self.module_path = join_module_path(&self.module_path, &node.ident.to_string());
        for item in items {
            self.visit_item(item);
        }
        self.module_path = previous;
    }

    fn visit_item_macro(&mut self, node: &'ast syn::ItemMacro) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        if let Some(name) = node.ident.as_ref().map(ToString::to_string)
            && let Some(summary) = summarize_declarative_macro(&node.mac.tokens)
        {
            self.index
                .macros
                .entry((self.crate_name.clone(), name))
                .or_default()
                .push(summary);
        }
    }

    fn visit_item_static(&mut self, node: &'ast syn::ItemStatic) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        self.index
            .globals
            .entry((self.crate_name.clone(), node.ident.to_string()))
            .or_default()
            .push(GlobalTypeBinding {
                name: node.ident.to_string(),
                module_path: self.module_path.clone(),
                ty: node.ty.to_token_stream().to_string(),
            });
        syn::visit::visit_item_static(self, node);
    }
}

fn summarize_declarative_macro(tokens: &proc_macro2::TokenStream) -> Option<MacroSemanticSummary> {
    let text = tokens.to_string();
    let (matcher, expansion) = text.split_once("=>")?;
    let mut parameters = Vec::new();
    let matcher_chars: Vec<char> = matcher.chars().collect();
    let mut cursor = 0;
    while cursor < matcher_chars.len() {
        if matcher_chars[cursor] != '$' {
            cursor += 1;
            continue;
        }
        cursor += 1;
        while cursor < matcher_chars.len() && matcher_chars[cursor].is_whitespace() {
            cursor += 1;
        }
        let start = cursor;
        while cursor < matcher_chars.len()
            && (matcher_chars[cursor].is_alphanumeric() || matcher_chars[cursor] == '_')
        {
            cursor += 1;
        }
        let candidate: String = matcher_chars[start..cursor].iter().collect();
        if !candidate.is_empty() && candidate != "crate" && !parameters.contains(&candidate) {
            parameters.push(candidate);
        }
    }
    if parameters.len() < 2 {
        return None;
    }
    let mutating = [
        ". lock",
        ". try_lock",
        ". write",
        ". borrow_mut",
        ". get_mut",
        ". get_unchecked_mut",
        ". store",
        ". swap",
        ". fetch_",
        ". insert",
        ". push",
    ]
    .iter()
    .any(|token| expansion.contains(token));
    if !mutating {
        return None;
    }
    let indexed_argument = parameters.iter().position(|parameter| {
        let marker = format!("$ {parameter}");
        expansion.contains(&format!("{marker} ["))
            || expansion.contains(&format!("{marker} . get"))
            || expansion.contains(&format!("{marker} . index"))
    })?;
    let index_argument = parameters
        .iter()
        .enumerate()
        .find(|(index, parameter)| {
            *index != indexed_argument && expansion.contains(&format!("$ {parameter}"))
        })
        .map(|(index, _)| index);
    Some(MacroSemanticSummary {
        indexed_argument,
        index_argument,
        access_kind: AtomicAccessKind::ReadModifyWrite,
    })
}

fn resolve_struct_key(
    struct_fields: &HashMap<StructKey, HashMap<String, String>>,
    crate_name: &str,
    module_path: &str,
    struct_name: &str,
) -> Option<StructKey> {
    if let Some(qualified) = struct_name.strip_prefix("crate::") {
        let (module, name) = qualified.rsplit_once("::").unwrap_or(("", qualified));
        let key = StructKey::new(crate_name.to_string(), module.to_string(), name.to_string());
        return struct_fields.contains_key(&key).then_some(key);
    }
    let local = StructKey::new(
        crate_name.to_string(),
        module_path.to_string(),
        struct_name.to_string(),
    );
    if struct_fields.contains_key(&local) {
        return Some(local);
    }
    let root = StructKey::new(
        crate_name.to_string(),
        String::new(),
        struct_name.to_string(),
    );
    if struct_fields.contains_key(&root) {
        return Some(root);
    }

    let scoped_matches: Vec<StructKey> = struct_fields
        .keys()
        .filter(|key| {
            key.crate_name == crate_name
                && key.name == struct_name
                && (module_path.is_empty()
                    || key.module_path == module_path
                    || key.module_path.starts_with(&format!("{module_path}::")))
        })
        .cloned()
        .collect();
    if scoped_matches.len() == 1 {
        return scoped_matches.into_iter().next();
    }

    let crate_wide_matches: Vec<StructKey> = struct_fields
        .keys()
        .filter(|key| key.crate_name == crate_name && key.name == struct_name)
        .cloned()
        .collect();
    (crate_wide_matches.len() == 1)
        .then(|| crate_wide_matches.into_iter().next())
        .flatten()
}

struct WrapperTypeCollector<'a> {
    file: &'a str,
    crate_name: String,
    module_path: String,
    evidence_map: &'a mut HashMap<StructKey, ConcurrencyEvidenceSet>,
    struct_fields: &'a HashMap<StructKey, HashMap<String, String>>,
}

impl WrapperTypeCollector<'_> {
    fn add_wrapper_evidence(
        &mut self,
        wrapper: &str,
        kind: EvidenceKind,
        struct_name: &str,
        line: usize,
    ) {
        let Some(key) = resolve_struct_key(
            self.struct_fields,
            &self.crate_name,
            &self.module_path,
            struct_name,
        ) else {
            return;
        };
        self.evidence_map
            .entry(key)
            .or_default()
            .evidence
            .push(EvidenceItem {
                kind,
                access_kind: None,
                field_name: None,
                loop_context: None,
                hotness_score: 1.0,
                in_concurrent_context: false,
                access_mode: AccessMode::Unknown,
                function_name: None,
                propagation_depth: 0,
                call_path: Vec::new(),
                semantic_contexts: Vec::new(),
                through_shared_indirection: false,
                through_raw_pointer: false,
                description: format!(
                    "{wrapper}<{struct_name}> type found at {}:{line}",
                    self.file
                ),
                file: self.file.to_string(),
                line,
            });
    }

    fn inspect_type(&mut self, ty: &syn::Type, line: usize) {
        let syn::Type::Path(type_path) = ty else {
            return;
        };
        for segment in &type_path.path.segments {
            let wrapper = segment.ident.to_string();
            let kind = match wrapper.as_str() {
                "Arc" => Some(EvidenceKind::ArcWrapped),
                "Mutex" => Some(EvidenceKind::MutexWrapped),
                "RwLock" => Some(EvidenceKind::RwLockWrapped),
                _ => None,
            };
            if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                for arg in &args.args {
                    if let syn::GenericArgument::Type(inner_ty) = arg
                        && let Some(kind) = kind.clone()
                        && let Some(struct_name) = self.direct_known_struct_name(inner_ty)
                    {
                        self.add_wrapper_evidence(&wrapper, kind.clone(), &struct_name, line);
                    }
                }
            }
        }
    }

    fn direct_known_struct_name(&self, ty: &syn::Type) -> Option<String> {
        let ty = match ty {
            syn::Type::Reference(reference) => reference.elem.as_ref(),
            syn::Type::Paren(paren) => paren.elem.as_ref(),
            syn::Type::Group(group) => group.elem.as_ref(),
            other => other,
        };
        let syn::Type::Path(type_path) = ty else {
            return None;
        };
        let name = type_path.path.segments.last()?.ident.to_string();
        resolve_struct_key(
            self.struct_fields,
            &self.crate_name,
            &self.module_path,
            &name,
        )
        .map(|_| name)
    }
}

impl<'ast> Visit<'ast> for WrapperTypeCollector<'_> {
    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
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

    fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        syn::visit::visit_item_impl(self, node);
    }

    fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        syn::visit::visit_impl_item_fn(self, node);
    }

    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        syn::visit::visit_item_fn(self, node);
    }

    fn visit_type(&mut self, node: &'ast syn::Type) {
        self.inspect_type(node, node.span().start().line);
        syn::visit::visit_type(self, node);
    }
}

fn join_module_path(base: &str, child: &str) -> String {
    if base.is_empty() {
        child.to_string()
    } else {
        format!("{base}::{child}")
    }
}

fn cfg_is_test_only(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if attr.path().is_ident("test") {
            return true;
        }
        if !attr.path().is_ident("cfg") {
            return false;
        }
        let compact: String = attr
            .meta
            .to_token_stream()
            .to_string()
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect();
        compact == "cfg(test)"
            || (compact.starts_with("cfg(all(")
                && compact
                    .trim_start_matches("cfg(all(")
                    .trim_end_matches("))")
                    .split(',')
                    .any(|term| term == "test"))
    })
}

fn is_concurrent_call(func: &Expr) -> bool {
    let Expr::Path(path) = func else {
        return false;
    };
    let segments: Vec<String> = path
        .path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect();
    let Some(last) = segments.last().map(String::as_str) else {
        return false;
    };

    matches!(last, "spawn")
        && segments.iter().any(|segment| {
            matches!(
                segment.as_str(),
                "thread" | "tokio" | "task" | "std" | "async_std" | "crossbeam"
            )
        })
        || last == "join" && segments.iter().any(|segment| segment == "rayon")
}

fn concrete_type_name(ty: &str) -> Option<String> {
    syn::parse_str::<syn::Type>(ty)
        .ok()
        .and_then(|parsed| concrete_type_name_from_syn(&parsed))
        .or_else(|| extract_wrapped_type_name(ty))
        .or_else(|| normalize_type_name(ty))
}

fn path_tail_name(expr: &Expr) -> Option<String> {
    let Expr::Path(path) = expr else {
        return None;
    };
    path.path
        .segments
        .last()
        .map(|segment| segment.ident.to_string())
}

fn concrete_type_name_from_syn(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Reference(reference) => concrete_type_name_from_syn(&reference.elem),
        syn::Type::Ptr(pointer) => concrete_type_name_from_syn(&pointer.elem),
        syn::Type::Paren(paren) => concrete_type_name_from_syn(&paren.elem),
        syn::Type::Group(group) => concrete_type_name_from_syn(&group.elem),
        syn::Type::Path(type_path) => {
            let segment = type_path.path.segments.last()?;
            let name = segment.ident.to_string();
            if is_transparent_binding_wrapper(&name)
                && let syn::PathArguments::AngleBracketed(args) = &segment.arguments
            {
                for arg in &args.args {
                    if let syn::GenericArgument::Type(inner) = arg {
                        return concrete_type_name_from_syn(inner);
                    }
                }
            }
            Some(name)
        }
        _ => None,
    }
}

fn is_transparent_binding_wrapper(name: &str) -> bool {
    matches!(
        name,
        "Arc"
            | "Rc"
            | "Box"
            | "Pin"
            | "Option"
            | "Result"
            | "Mutex"
            | "RwLock"
            | "UnsafeCell"
            | "Cell"
            | "RefCell"
            | "NonNull"
            | "ManuallyDrop"
    )
}

fn top_level_wrapper_name(ty: &str) -> Option<String> {
    let parsed = syn::parse_str::<syn::Type>(ty).ok()?;
    top_level_wrapper_from_syn(&parsed)
}

/// Recover native slice indexing through owned/shared sequence wrappers.
/// A project-defined getter is not necessarily an element projection.
fn is_native_sequence_type(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Array(_) | syn::Type::Slice(_) => true,
        syn::Type::Reference(reference) => is_native_sequence_type(&reference.elem),
        syn::Type::Paren(paren) => is_native_sequence_type(&paren.elem),
        syn::Type::Group(group) => is_native_sequence_type(&group.elem),
        syn::Type::Path(path) => path.path.segments.last().is_some_and(|segment| {
            if segment.ident == "Vec" {
                return true;
            }
            matches!(segment.ident.to_string().as_str(), "Box" | "Arc" | "Rc")
                && matches!(&segment.arguments, syn::PathArguments::AngleBracketed(arguments)
                    if arguments.args.iter().any(|argument|
                        matches!(argument, syn::GenericArgument::Type(inner)
                            if is_native_sequence_type(inner))))
        }),
        _ => false,
    }
}

fn top_level_wrapper_from_syn(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Reference(reference) => top_level_wrapper_from_syn(&reference.elem),
        syn::Type::Ptr(_) => Some("raw_pointer".to_string()),
        syn::Type::Paren(paren) => top_level_wrapper_from_syn(&paren.elem),
        syn::Type::Group(group) => top_level_wrapper_from_syn(&group.elem),
        syn::Type::Path(type_path) => type_path
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string()),
        _ => None,
    }
}

fn type_is_raw_pointer_like(ty: &str) -> bool {
    let Ok(parsed) = syn::parse_str::<syn::Type>(ty) else {
        let compact: String = ty.chars().filter(|ch| !ch.is_whitespace()).collect();
        return compact.starts_with("*const")
            || compact.starts_with("*mut")
            || compact.contains("NonNull<");
    };
    type_is_raw_pointer_like_syn(&parsed)
}

fn type_is_raw_pointer_like_syn(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Ptr(_) => true,
        syn::Type::Reference(reference) => type_is_raw_pointer_like_syn(&reference.elem),
        syn::Type::Paren(paren) => type_is_raw_pointer_like_syn(&paren.elem),
        syn::Type::Group(group) => type_is_raw_pointer_like_syn(&group.elem),
        syn::Type::Path(type_path) => type_path
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "NonNull"),
        _ => false,
    }
}

fn is_shared_indirection_wrapper(wrapper: &str) -> bool {
    matches!(wrapper, "Arc" | "Mutex" | "RwLock")
}

fn type_has_shared_indirection(ty: &str) -> bool {
    let Ok(parsed) = syn::parse_str::<syn::Type>(ty) else {
        let compact: String = ty
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect();
        return ["Arc<", "Mutex<", "RwLock<"]
            .iter()
            .any(|wrapper| compact.contains(wrapper));
    };
    type_has_shared_indirection_syn(&parsed)
}

fn type_has_shared_indirection_syn(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Reference(reference) => type_has_shared_indirection_syn(&reference.elem),
        syn::Type::Ptr(pointer) => type_has_shared_indirection_syn(&pointer.elem),
        syn::Type::Paren(paren) => type_has_shared_indirection_syn(&paren.elem),
        syn::Type::Group(group) => type_has_shared_indirection_syn(&group.elem),
        syn::Type::Path(type_path) => type_path.path.segments.iter().any(|segment| {
            is_shared_indirection_wrapper(&segment.ident.to_string())
                || match &segment.arguments {
                    syn::PathArguments::AngleBracketed(arguments) => {
                        arguments.args.iter().any(|argument| {
                            matches!(
                                argument,
                                syn::GenericArgument::Type(inner)
                                    if type_has_shared_indirection_syn(inner)
                            )
                        })
                    }
                    _ => false,
                }
        }),
        _ => false,
    }
}

fn extract_wrapped_type_name(ty: &str) -> Option<String> {
    if let Some(reference) = parse_reference_prefix(ty) {
        return extract_wrapped_type_name(reference.rest)
            .or_else(|| normalize_type_name(reference.rest));
    }

    let compact: String = ty.chars().filter(|ch| !ch.is_whitespace()).collect();
    for wrapper in [
        "Arc",
        "Rc",
        "Option",
        "Result",
        "Mutex",
        "RwLock",
        "Box",
        "Pin",
        "UnsafeCell",
        "Cell",
        "RefCell",
        "NonNull",
        "ManuallyDrop",
    ] {
        if let Some(rest) = compact
            .strip_prefix(wrapper)
            .and_then(|rest| rest.strip_prefix('<'))
        {
            return extract_inner_type_name(rest);
        }
        if let Some((_, rest)) = compact.split_once(&format!("::{wrapper}<")) {
            return extract_inner_type_name(rest);
        }
    }
    None
}

struct ReferencePrefix<'a> {
    is_mut: bool,
    rest: &'a str,
}

fn parse_reference_prefix(ty: &str) -> Option<ReferencePrefix<'_>> {
    let mut rest = ty.trim_start().strip_prefix('&')?.trim_start();
    if let Some(after_quote) = rest.strip_prefix('\'') {
        let lifetime_len = after_quote
            .char_indices()
            .find(|(_, ch)| !is_lifetime_char(*ch))
            .map(|(idx, _)| idx)
            .unwrap_or(after_quote.len());
        rest = after_quote[lifetime_len..].trim_start();
    }
    let (is_mut, rest) = if let Some(after_mut) = rest.strip_prefix("mut ") {
        (true, after_mut)
    } else {
        (false, rest)
    };
    Some(ReferencePrefix { is_mut, rest })
}

fn is_lifetime_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn access_mode_from_type_tokens(ty: &str) -> AccessMode {
    if type_is_raw_pointer_like(ty) {
        return AccessMode::Unknown;
    }
    if let Some(reference) = parse_reference_prefix(ty) {
        if top_level_wrapper_name(reference.rest)
            .as_deref()
            .is_some_and(is_shared_indirection_wrapper)
        {
            return AccessMode::Shared;
        }
        return if reference.is_mut {
            AccessMode::Exclusive
        } else {
            AccessMode::Shared
        };
    }

    let compact: String = ty.chars().filter(|ch| !ch.is_whitespace()).collect();
    if compact.contains("Arc<") || compact.contains("Mutex<") || compact.contains("RwLock<") {
        AccessMode::Shared
    } else {
        AccessMode::Exclusive
    }
}

fn access_mode_from_receiver(receiver: &syn::Receiver) -> AccessMode {
    if receiver.reference.is_some() {
        if receiver.mutability.is_some() {
            AccessMode::Exclusive
        } else {
            AccessMode::Shared
        }
    } else {
        AccessMode::Exclusive
    }
}

fn is_compound_assign(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::AddAssign(_)
            | BinOp::SubAssign(_)
            | BinOp::MulAssign(_)
            | BinOp::DivAssign(_)
            | BinOp::RemAssign(_)
            | BinOp::BitXorAssign(_)
            | BinOp::BitAndAssign(_)
            | BinOp::BitOrAssign(_)
            | BinOp::ShlAssign(_)
            | BinOp::ShrAssign(_)
    )
}

/// Extracts the first type name from inside angle brackets, unwrapping nested wrappers.
fn extract_inner_type_name(s: &str) -> Option<String> {
    let s = s.trim();
    let wrappers = [
        "Mutex <",
        "Mutex<",
        "RwLock <",
        "RwLock<",
        "UnsafeCell <",
        "UnsafeCell<",
    ];
    for w in &wrappers {
        if let Some(rest) = s.strip_prefix(w) {
            return extract_inner_type_name(rest);
        }
    }

    let head = s.split('>').next().unwrap_or(s).trim();
    let name = normalize_type_name(head)?;
    if name.chars().next().is_none_or(|c| !c.is_uppercase()) {
        return None;
    }

    Some(name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn imported_globals_keep_declaration_module_identity() {
        for (imports, expression, expected) in [
            (
                "use crate::left::*;",
                "GLOBAL.value.fetch_add(1)",
                Some("left"),
            ),
            (
                "use crate::right::GLOBAL;",
                "GLOBAL.value.fetch_add(1)",
                Some("right"),
            ),
            (
                "use crate::left::{GLOBAL as SELECTED};",
                "SELECTED.value.fetch_add(1)",
                Some("left"),
            ),
            (
                "use super::left::*;",
                "GLOBAL.value.fetch_add(1)",
                Some("left"),
            ),
            ("", "crate::right::GLOBAL.value.fetch_add(1)", Some("right")),
            (
                "use crate::left::*; use crate::right::*;",
                "GLOBAL.value.fetch_add(1)",
                None,
            ),
            (
                "use crate::left::*; use crate::right::GLOBAL;",
                "GLOBAL.value.fetch_add(1)",
                Some("right"),
            ),
            (
                "use crate::missing::GLOBAL;",
                "GLOBAL.value.fetch_add(1)",
                None,
            ),
        ] {
            let mut files = Vec::new();
            let mut records = Vec::new();
            for module in ["left", "right"] {
                let source = "pub struct State { pub value: AtomicUsize } pub static GLOBAL: State = todo!();";
                let ast = syn::parse_file(source).unwrap();
                let syn::Item::Struct(item) = &ast.items[0] else {
                    unreachable!()
                };
                records.push(crate::struct_layout::analyze_struct_layout(
                    item,
                    source,
                    module,
                    Some("demo"),
                    module,
                    64,
                ));
                files.push(ParsedFile {
                    path: module.into(),
                    module_path: module.into(),
                    source: source.into(),
                    ast,
                    crate_name: Some("demo".into()),
                });
            }
            let source = format!("{imports} fn run() {{ {expression}; }}");
            files.push(ParsedFile {
                path: "reader.rs".into(),
                module_path: "reader".into(),
                ast: syn::parse_file(&source).unwrap(),
                source,
                crate_name: Some("demo".into()),
            });
            let facts = collect_concurrency_evidence(&files, &records);
            for module in ["left", "right"] {
                let key = StructKey::new("demo", module, "State");
                let has_access = facts.get(&key).is_some_and(|set| {
                    set.evidence.iter().any(|item| {
                        item.file == "reader.rs"
                            && item.access_kind == Some(AtomicAccessKind::ReadModifyWrite)
                    })
                });
                assert_eq!(
                    has_access,
                    expected == Some(module),
                    "{imports}: {expression}, target {module}"
                );
            }
        }
    }

    fn test_function(module_path: &str, owner: Option<&str>, name: &str) -> FunctionKey {
        FunctionKey {
            crate_name: "demo".to_string(),
            module_path: module_path.to_string(),
            owner: owner.map(ToOwned::to_owned),
            trait_name: None,
            name: name.to_string(),
        }
    }

    fn test_call(callee: CalleeRef) -> FunctionCallSite {
        FunctionCallSite {
            caller: test_function("caller", None, "run"),
            callee,
            file: "src/lib.rs".to_string(),
            line: 1,
            hotness_score: 1.0,
            in_concurrent_context: false,
            semantic_contexts: Vec::new(),
            through_shared_indirection: false,
            through_raw_pointer: false,
            receiver_binding: None,
            argument_bindings: Vec::new(),
        }
    }

    #[test]
    fn test_extract_inner_type_name_simple() {
        assert_eq!(extract_inner_type_name("Counter>"), Some("Counter".into()));
        assert_eq!(extract_inner_type_name("Inner >"), Some("Inner".into()));
    }

    #[test]
    fn test_extract_inner_type_name_nested() {
        assert_eq!(
            extract_inner_type_name("Mutex<Inner>>"),
            Some("Inner".into())
        );
        // "Mutex < " matches our "Mutex <" pattern, so it extracts Inner
        assert_eq!(
            extract_inner_type_name("Mutex < Inner >>"),
            Some("Inner".into())
        );
    }

    #[test]
    fn test_extract_inner_type_name_not_type() {
        assert_eq!(extract_inner_type_name("u64>"), None);
        assert_eq!(extract_inner_type_name("123"), None);
    }

    #[test]
    fn concrete_type_parser_unwraps_raw_and_shared_layers() {
        assert_eq!(
            concrete_type_name("*const std::sync::Arc<Shared>"),
            Some("Shared".to_string())
        );
        assert!(type_is_raw_pointer_like("*mut Shared"));
        assert_eq!(
            access_mode_from_type_tokens("*mut Shared"),
            AccessMode::Unknown
        );
        assert!(type_has_shared_indirection("Pin<Arc<Shared>>"));
        assert_eq!(
            concrete_type_name("Option<Arc<Shared>>"),
            Some("Shared".to_string())
        );
    }

    #[test]
    fn declarative_macro_summary_recovers_indexed_lock_roles() {
        let tokens = quote::quote! {
            ($container:expr, $slot:expr) => {
                unsafe { $container.get_unchecked($slot).lock().unwrap() }
            };
        };
        let summary = summarize_declarative_macro(&tokens)
            .unwrap_or_else(|| panic!("macro summary for {}", tokens));
        assert_eq!(summary.indexed_argument, 0);
        assert_eq!(summary.index_argument, Some(1));
        assert_eq!(summary.access_kind, AtomicAccessKind::ReadModifyWrite);
    }

    #[test]
    fn semantic_declaration_collector_indexes_macro_rules_name() {
        let source = r#"
macro_rules! indexed_guard {
    ($container:expr, $slot:expr) => {
        unsafe { $container.get_unchecked($slot).lock().unwrap() }
    };
}
struct Scheduler { slots: Vec<std::sync::Mutex<u64>> }
impl Scheduler {
    fn update(&self, slot: usize) {
        let _guard = indexed_guard!(self.slots, slot);
    }
}
"#;
        let ast = syn::parse_file(source).expect("parse macro fixture");
        let mut index = SemanticDeclarationIndex::default();
        SemanticDeclarationCollector {
            block_depth: 0,
            crate_name: "fixture".to_string(),
            module_path: String::new(),
            index: &mut index,
        }
        .visit_file(&ast);
        assert_eq!(
            index
                .macros
                .get(&("fixture".to_string(), "indexed_guard".to_string()))
                .map(Vec::len),
            Some(1)
        );

        let item_struct = ast
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Struct(item_struct) => Some(item_struct),
                _ => None,
            })
            .expect("fixture struct");
        let info = crate::struct_layout::analyze_struct_layout(
            item_struct,
            source,
            "src/lib.rs",
            Some("fixture"),
            "",
            crate::struct_layout::CACHE_LINE_SIZE,
        );
        let evidence = collect_concurrency_evidence(
            &[ParsedFile {
                path: "src/lib.rs".to_string(),
                module_path: String::new(),
                source: source.to_string(),
                ast,
                crate_name: Some("fixture".to_string()),
            }],
            &[info],
        );
        let scheduler = evidence
            .get(&StructKey::new("fixture", "", "Scheduler"))
            .expect("scheduler macro evidence");
        assert!(scheduler.evidence.iter().any(|item| {
            item.field_name.as_deref() == Some("slots")
                && item
                    .semantic_contexts
                    .iter()
                    .any(|context| context == "macro_expansion_summary")
        }));
    }

    #[test]
    fn tuple_newtype_projection_maps_to_outer_layout_field() {
        let source = r#"
use std::sync::atomic::{AtomicUsize, Ordering};
#[repr(align(64))]
struct Padded<T>(T);
struct Ring {
    head: Padded<AtomicUsize>,
    flush: Padded<AtomicUsize>,
}
impl Ring {
    fn release(&self, value: usize) {
        self.head.0.store(value, Ordering::Release);
    }
    fn publish(&self, value: usize) {
        self.flush.0.store(value, Ordering::Release);
    }
}
"#;
        let ast = syn::parse_file(source).expect("parse newtype projection fixture");
        let mut structs: Vec<_> = ast
            .items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Struct(item_struct) => {
                    Some(crate::struct_layout::analyze_struct_layout(
                        item_struct,
                        source,
                        "src/lib.rs",
                        Some("fixture"),
                        "",
                        128,
                    ))
                }
                _ => None,
            })
            .collect();
        crate::struct_layout::enrich_structs_with_type_registry(&mut structs, 128);
        let evidence = collect_concurrency_evidence(
            &[ParsedFile {
                path: "src/lib.rs".to_string(),
                module_path: String::new(),
                source: source.to_string(),
                ast,
                crate_name: Some("fixture".to_string()),
            }],
            &structs,
        );
        let ring = evidence
            .get(&StructKey::new("fixture", "", "Ring"))
            .expect("Ring evidence");

        for expected in ["head", "flush"] {
            assert!(ring.evidence.iter().any(|item| {
                item.field_name.as_deref() == Some(expected)
                    && item.access_kind == Some(AtomicAccessKind::Write)
                    && item
                        .semantic_contexts
                        .iter()
                        .any(|context| context == "transparent_wrapper_projection")
            }));
        }
    }

    #[test]
    fn mutable_option_projection_and_mutex_guard_preserve_exclusivity() {
        let source = r#"
use std::sync::{Arc, Mutex};
struct Stats { count: u64, errors: u64 }
fn update_optional(stat: &mut Option<&mut Stats>) {
    if let Some(stat) = stat.as_mut() { stat.count += 1; }
}
fn update_guarded(metrics: Arc<Mutex<Stats>>) {
    let mut metrics = metrics.lock().unwrap();
    metrics.errors += 1;
}
"#;
        let ast = syn::parse_file(source).expect("parse exclusive projection fixture");
        let structs: Vec<_> = ast
            .items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Struct(item_struct) => {
                    Some(crate::struct_layout::analyze_struct_layout(
                        item_struct,
                        source,
                        "src/lib.rs",
                        Some("fixture"),
                        "",
                        crate::struct_layout::CACHE_LINE_SIZE,
                    ))
                }
                _ => None,
            })
            .collect();
        let evidence = collect_concurrency_evidence(
            &[ParsedFile {
                path: "src/lib.rs".to_string(),
                module_path: String::new(),
                source: source.to_string(),
                ast,
                crate_name: Some("fixture".to_string()),
            }],
            &structs,
        );
        let stats = evidence
            .get(&StructKey::new("fixture", "", "Stats"))
            .expect("stats evidence");
        for field in ["count", "errors"] {
            assert!(stats.evidence.iter().any(|item| {
                item.field_name.as_deref() == Some(field)
                    && item.access_kind == Some(AtomicAccessKind::ReadModifyWrite)
                    && item.access_mode == AccessMode::Exclusive
                    && !item.through_shared_indirection
                    && !item.through_raw_pointer
            }));
        }
    }

    #[test]
    fn unsafe_cell_get_is_mutable_escape_but_ordinary_getter_is_read() {
        let source = r#"
use std::cell::UnsafeCell;
struct Setting(u64);
impl Setting { fn get(&self) -> u64 { self.0 } }
struct State { slot: UnsafeCell<u64>, config: Setting }
impl State {
    unsafe fn write(&self) { unsafe { *self.slot.get() = 1; } }
    fn read(&self) -> u64 { self.config.get() }
}
"#;
        let ast = syn::parse_file(source).expect("parse getter fixture");
        let structs: Vec<_> = ast
            .items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Struct(item_struct) => {
                    Some(crate::struct_layout::analyze_struct_layout(
                        item_struct,
                        source,
                        "src/lib.rs",
                        Some("fixture"),
                        "",
                        crate::struct_layout::CACHE_LINE_SIZE,
                    ))
                }
                _ => None,
            })
            .collect();
        let evidence = collect_concurrency_evidence(
            &[ParsedFile {
                path: "src/lib.rs".to_string(),
                module_path: String::new(),
                source: source.to_string(),
                ast,
                crate_name: Some("fixture".to_string()),
            }],
            &structs,
        );
        let state = evidence
            .get(&StructKey::new("fixture", "", "State"))
            .expect("state evidence");
        assert!(state.evidence.iter().any(|item| {
            item.field_name.as_deref() == Some("slot")
                && item.access_kind == Some(AtomicAccessKind::ReadModifyWrite)
        }));
        assert!(state.evidence.iter().any(|item| {
            item.field_name.as_deref() == Some("config")
                && item.access_kind == Some(AtomicAccessKind::Read)
        }));
    }

    #[test]
    fn indexed_tuple_projection_maps_to_outer_container_field() {
        let source = r#"
use std::sync::atomic::{AtomicU32, Ordering};
struct Histogram { buckets: Box<[(f64, AtomicU32); 26]> }
impl Histogram {
    fn record(&self, index: usize) {
        self.buckets[index].1.fetch_add(1, Ordering::Relaxed);
    }
}
"#;
        let ast = syn::parse_file(source).expect("parse tuple-array fixture");
        let info = ast
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Struct(item_struct) => {
                    Some(crate::struct_layout::analyze_struct_layout(
                        item_struct,
                        source,
                        "src/lib.rs",
                        Some("fixture"),
                        "",
                        crate::struct_layout::CACHE_LINE_SIZE,
                    ))
                }
                _ => None,
            })
            .expect("fixture struct");
        let evidence = collect_concurrency_evidence(
            &[ParsedFile {
                path: "src/lib.rs".to_string(),
                module_path: String::new(),
                source: source.to_string(),
                ast,
                crate_name: Some("fixture".to_string()),
            }],
            &[info],
        );
        let histogram = evidence
            .get(&StructKey::new("fixture", "", "Histogram"))
            .expect("histogram evidence");
        assert!(
            histogram.evidence.iter().any(|item| {
                item.field_name.as_deref() == Some("buckets")
                    && item.access_kind == Some(AtomicAccessKind::ReadModifyWrite)
            }),
            "indexed tuple access should resolve to buckets: {:?}",
            histogram.evidence
        );
    }

    #[test]
    fn external_multisegment_call_does_not_fall_back_to_same_named_local_function() {
        let local_spawn = test_function("helpers", None, "spawn");
        let call = test_call(CalleeRef::Free {
            path: vec!["tokio".to_string(), "spawn".to_string()],
            name: "spawn".to_string(),
        });
        assert!(resolve_callees(&call, &[local_spawn]).is_empty());
    }

    #[test]
    fn ambiguous_method_owner_requires_module_identity() {
        let hot = test_function("hot", Some("State"), "record");
        let cold = test_function("cold", Some("State"), "record");
        let ambiguous = test_call(CalleeRef::Method {
            owner: "State".to_string(),
            owner_module: None,
            trait_name: None,
            name: "record".to_string(),
        });
        assert!(resolve_callees(&ambiguous, &[hot.clone(), cold.clone()]).is_empty());

        let resolved = test_call(CalleeRef::Method {
            owner: "State".to_string(),
            owner_module: Some("hot".to_string()),
            trait_name: None,
            name: "record".to_string(),
        });
        assert_eq!(resolve_callees(&resolved, &[hot.clone(), cold]), vec![hot]);
    }
}
