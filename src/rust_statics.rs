//! Static storage risks backed by resolved declarations and actual operations.
//! Arrays use element layout; distinct globals retain unknown linker placement.

use std::collections::{HashMap, HashSet};

use quote::ToTokens;
use syn::{parse::Parser, spanned::Spanned, visit::Visit};

use crate::helpers::{is_hot_static_singleton_type, normalize_type_name};
use crate::pattern_model::{build_pattern_context, core_predicate_holds};
use crate::rust_findings::make_finding;
use crate::rust_storage::{Index, Position, position};
use crate::types::{
    AccessMode, AccessPattern, AnalysisOptions, AtomicAccessKind, CandidateKind, ColocationPattern,
    ConcurrencyEvidenceSet, EvidenceItem, EvidenceKind, Finding, ParallelismEvidence, ParsedFile,
    RiskCategory, Severity, StructInfo,
};

struct StaticItemInfo {
    name: String,
    ty_str: String,
    line: usize,
    position: Position,
    file: usize,
    identity: String,
    type_model: StaticTypeModel,
    array_element: Option<String>,
    array_length: Option<usize>,
}

#[derive(Clone, Default)]
struct StaticTypeModel {
    outer_type: Option<String>,
    payload_type: Option<String>,
}

#[derive(Clone)]
struct Reference {
    identity: String,
    element_index: Option<String>,
    receiver_type: String,
    index_constants: HashMap<String, usize>,
}

struct ReferenceAccessor {
    reference: Reference,
    parameters: Vec<String>,
}

struct Collector<'a> {
    index: &'a Index,
    file: &'a ParsedFile,
    declarations: &'a HashMap<String, StaticItemInfo>,
    structs: &'a [StructInfo],
    accessors: &'a HashMap<String, ReferenceAccessor>,
    accesses: &'a mut HashMap<String, Vec<(Reference, EvidenceItem)>>,
    scopes: Vec<HashMap<String, Option<Reference>>>,
    function: Option<String>,
}

impl Collector<'_> {
    fn reference(&self, expr: &syn::Expr) -> Option<Reference> {
        match expr {
            syn::Expr::Path(path) => {
                let name = path.path.to_token_stream().to_string().replace(' ', "");
                if path.path.segments.len() == 1 {
                    for scope in self.scopes.iter().rev() {
                        if let Some(reference) = scope.get(&name) {
                            return reference.clone();
                        }
                    }
                }
                let identity =
                    self.index
                        .resolve_static(self.file, &name, position(expr.span()))?;
                let item = self.declarations.get(&identity)?;
                Some(Reference {
                    identity,
                    element_index: None,
                    receiver_type: item.ty_str.clone(),
                    index_constants: HashMap::new(),
                })
            }
            syn::Expr::Reference(expr) => self.reference(&expr.expr),
            syn::Expr::Unary(expr) if matches!(expr.op, syn::UnOp::Deref(_)) => {
                self.reference(&expr.expr)
            }
            syn::Expr::Paren(expr) => self.reference(&expr.expr),
            syn::Expr::Group(expr) => self.reference(&expr.expr),
            syn::Expr::Return(expr) => self.reference(expr.expr.as_deref()?),
            syn::Expr::Index(expr) => {
                let mut reference = self.reference(&expr.expr)?;
                let item = self.declarations.get(&reference.identity)?;
                reference.receiver_type = item.array_element.clone()?;
                reference.index_constants = index_constants(self.index, self.file, &expr.index);
                reference.element_index = Some(
                    evaluate_index(&expr.index, &reference.index_constants).map_or_else(
                        || expr.index.to_token_stream().to_string(),
                        |index| index.to_string(),
                    ),
                );
                Some(reference)
            }
            syn::Expr::Field(expr) => {
                let mut reference = self.reference(&expr.base)?;
                // Dereferencing a stored pointer changes the storage object;
                // the pointee's field is not part of the containing array slot.
                if crate::helpers::is_indirection_type(&reference.receiver_type) {
                    return None;
                }
                let name = normalize_type_name(&reference.receiver_type)?;
                let field = expr.member.to_token_stream().to_string();
                let module = self
                    .index
                    .module_at(&self.file.path, position(expr.span()))?;
                let records = self
                    .structs
                    .iter()
                    .filter(|record| {
                        record.name == name
                            && record.crate_name == self.file.crate_name
                            && record.module_path == module
                    })
                    .collect::<Vec<_>>();
                let [record] = records.as_slice() else {
                    return None;
                };
                reference.receiver_type = record
                    .fields
                    .iter()
                    .find(|item| item.name == field)?
                    .ty_str
                    .clone();
                Some(reference)
            }
            syn::Expr::Call(call) => {
                let syn::Expr::Path(path) = call.func.as_ref() else {
                    return None;
                };
                let name = path.path.to_token_stream().to_string().replace(' ', "");
                if !name.contains("::") && self.scopes.iter().any(|scope| scope.contains_key(&name))
                {
                    return None;
                }
                let identity =
                    self.index
                        .resolve_function(self.file, &name, position(expr.span()))?;
                // A symbolic returned index stays an assumption about distinct
                // legal invocations, rather than an invented concrete schedule.
                let accessor = self.accessors.get(&identity)?;
                let mut reference = accessor.reference.clone();
                for (parameter, argument) in accessor.parameters.iter().zip(&call.args) {
                    if let Some(value) =
                        evaluate_index(argument, &index_constants(self.index, self.file, argument))
                    {
                        reference.index_constants.insert(parameter.clone(), value);
                    }
                }
                if let Some(expr) = reference
                    .element_index
                    .as_ref()
                    .and_then(|index| syn::parse_str::<syn::Expr>(index).ok())
                    && let Some(index) = evaluate_index(&expr, &reference.index_constants)
                {
                    reference.element_index = Some(index.to_string());
                }
                Some(reference)
            }
            syn::Expr::MethodCall(call) => {
                let mut reference = self.reference(&call.receiver)?;
                match call.method.to_string().as_str() {
                    "unwrap" | "expect" | "as_ref" | "deref" => Some(reference),
                    "get" | "get_mut" | "get_or_init" => {
                        let ty = syn::parse_str::<syn::Type>(&reference.receiver_type).ok()?;
                        let model = static_type_model(&ty);
                        if !matches!(model.outer_type.as_deref(), Some("OnceLock" | "OnceCell")) {
                            return None;
                        }
                        reference.receiver_type = model.payload_type?;
                        Some(reference)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn record(&mut self, reference: Reference, kind: AtomicAccessKind, expr: &syn::Expr) {
        let item = &self.declarations[&reference.identity];
        if item.array_element.is_some() && reference.element_index.is_none() {
            return;
        }
        let operation = expr.to_token_stream().to_string();
        let evidence = EvidenceItem {
            kind: if matches!(expr, syn::Expr::MethodCall(_)) {
                EvidenceKind::HotSyncFieldOps
            } else if matches!(kind, AtomicAccessKind::Read) {
                EvidenceKind::PlainFieldRead
            } else {
                EvidenceKind::PlainFieldWrite
            },
            access_kind: Some(kind),
            field_name: Some(item.name.clone()),
            hotness_score: 1.0,
            loop_context: None,
            in_concurrent_context: false,
            access_mode: AccessMode::Shared,
            function_name: self.function.clone(),
            propagation_depth: 0,
            call_path: Vec::new(),
            semantic_contexts: vec![format!("static_storage:{}", reference.identity)],
            through_shared_indirection: false,
            through_raw_pointer: false,
            description: operation,
            file: self.file.path.clone(),
            line: expr.span().start().line,
        };
        self.accesses
            .entry(reference.identity.clone())
            .or_default()
            .push((reference, evidence));
    }

    fn bind_pattern(&mut self, pattern: &syn::Pat, reference: Option<Reference>) {
        struct Bindings<'a>(
            &'a mut HashMap<String, Option<Reference>>,
            Option<Reference>,
        );
        impl<'ast> Visit<'ast> for Bindings<'_> {
            fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
                self.0.insert(pat.ident.to_string(), self.1.clone());
            }
        }
        if let Some(scope) = self.scopes.last_mut() {
            Bindings(scope, reference).visit_pat(pattern);
        }
    }

    fn visit_function(&mut self, signature: &syn::Signature, block: &syn::Block) {
        // Nested function bodies cannot capture a surrounding local binding.
        let old_scopes = std::mem::take(&mut self.scopes);
        let old_function = self.function.replace(signature.ident.to_string());
        self.scopes.push(HashMap::new());
        for input in &signature.inputs {
            if let syn::FnArg::Typed(input) = input {
                self.bind_pattern(&input.pat, None);
            }
        }
        self.visit_block(block);
        self.scopes = old_scopes;
        self.function = old_function;
    }

    fn visit_place_address(&mut self, expr: &syn::Expr) {
        // Forming a reference evaluates selectors but does not read the place.
        match expr {
            syn::Expr::Path(_) => {}
            syn::Expr::Index(expr) => {
                self.visit_place_address(&expr.expr);
                self.visit_expr(&expr.index);
            }
            syn::Expr::Field(expr) => self.visit_place_address(&expr.base),
            syn::Expr::Paren(expr) => self.visit_place_address(&expr.expr),
            syn::Expr::Group(expr) => self.visit_place_address(&expr.expr),
            syn::Expr::Reference(expr) => self.visit_place_address(&expr.expr),
            syn::Expr::Unary(expr) if matches!(expr.op, syn::UnOp::Deref(_)) => {
                self.visit_place_address(&expr.expr);
            }
            _ => self.visit_expr(expr),
        }
    }

    fn visit_condition(&mut self, expr: &syn::Expr) {
        match expr {
            syn::Expr::Let(expr) => {
                self.visit_expr(&expr.expr);
                self.bind_pattern(&expr.pat, None);
            }
            syn::Expr::Binary(expr) if matches!(expr.op, syn::BinOp::And(_)) => {
                self.visit_condition(&expr.left);
                self.visit_condition(&expr.right);
            }
            _ => self.visit_expr(expr),
        }
    }
}

impl<'ast> Visit<'ast> for Collector<'_> {
    fn visit_item_static(&mut self, _: &'ast syn::ItemStatic) {}
    fn visit_item_const(&mut self, _: &'ast syn::ItemConst) {}

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.visit_function(&item.sig, &item.block);
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        self.visit_function(&item.sig, &item.block);
    }

    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.scopes.push(HashMap::new());
        syn::visit::visit_block(self, block);
        self.scopes.pop();
    }

    fn visit_local(&mut self, item: &'ast syn::Local) {
        let reference = item.init.as_ref().and_then(|init| {
            // A plain by-value assignment or ordinary clone does not preserve
            // the source object. Follow only explicit references/accessors.
            matches!(
                init.expr.as_ref(),
                syn::Expr::Reference(_) | syn::Expr::Call(_)
            )
            .then(|| self.reference(&init.expr))
            .flatten()
        });
        if let Some(init) = &item.init {
            self.visit_expr(&init.expr);
        }
        self.bind_pattern(&item.pat, reference);
    }

    fn visit_expr_closure(&mut self, closure: &'ast syn::ExprClosure) {
        self.scopes.push(HashMap::new());
        for input in &closure.inputs {
            self.bind_pattern(input, None);
        }
        self.visit_expr(&closure.body);
        self.scopes.pop();
    }

    fn visit_expr_for_loop(&mut self, expr: &'ast syn::ExprForLoop) {
        self.visit_expr(&expr.expr);
        self.scopes.push(HashMap::new());
        self.bind_pattern(&expr.pat, None);
        self.visit_block(&expr.body);
        self.scopes.pop();
    }

    fn visit_expr_reference(&mut self, expr: &'ast syn::ExprReference) {
        self.visit_place_address(&expr.expr);
    }

    fn visit_expr_if(&mut self, expr: &'ast syn::ExprIf) {
        self.scopes.push(HashMap::new());
        self.visit_condition(&expr.cond);
        self.visit_block(&expr.then_branch);
        self.scopes.pop();
        if let Some((_, branch)) = &expr.else_branch {
            self.visit_expr(branch);
        }
    }

    fn visit_expr_while(&mut self, expr: &'ast syn::ExprWhile) {
        self.scopes.push(HashMap::new());
        self.visit_condition(&expr.cond);
        self.visit_block(&expr.body);
        self.scopes.pop();
    }

    fn visit_expr_match(&mut self, expr: &'ast syn::ExprMatch) {
        self.visit_expr(&expr.expr);
        for arm in &expr.arms {
            self.scopes.push(HashMap::new());
            self.bind_pattern(&arm.pat, None);
            if let Some((_, guard)) = &arm.guard {
                self.visit_condition(guard);
            }
            self.visit_expr(&arm.body);
            self.scopes.pop();
        }
    }

    fn visit_expr_method_call(&mut self, call: &'ast syn::ExprMethodCall) {
        if let Some(reference) = self.reference(&call.receiver) {
            let item = &self.declarations[&reference.identity];
            let method = call.method.to_string();
            let written = if item.array_element.is_some() || reference.receiver_type != item.ty_str
            {
                payload_method_matches_sync_write_api(&reference.receiver_type, &method)
            } else {
                static_method_matches_declared_write_api(item, &method)
            };
            let kind = if !written {
                AtomicAccessKind::Read
            } else if matches!(method.as_str(), "set" | "store" | "insert") {
                AtomicAccessKind::Write
            } else {
                AtomicAccessKind::ReadModifyWrite
            };
            let expected_type = reference.receiver_type.clone();
            self.record(reference, kind, &syn::Expr::MethodCall(call.clone()));
            for argument in &call.args {
                // Option<&T>::unwrap_or(&Lazy<T>) dereferences the lazy state;
                // merely borrowing a Lazy<T> without this coercion does not.
                if method == "unwrap_or"
                    && let syn::Expr::MethodCall(receiver) = call.receiver.as_ref()
                    && receiver.method == "get"
                    && let Some(lazy) = self.reference(argument)
                    && let Ok(ty) = syn::parse_str::<syn::Type>(&lazy.receiver_type)
                {
                    let model = static_type_model(&ty);
                    if matches!(model.outer_type.as_deref(), Some("Lazy" | "LazyLock"))
                        && model.payload_type.as_deref().is_some_and(|payload| {
                            payload.replace(' ', "") == expected_type.replace(' ', "")
                        })
                    {
                        self.record(lazy, AtomicAccessKind::Read, argument);
                    }
                }
                self.visit_expr(argument);
            }
        } else {
            syn::visit::visit_expr_method_call(self, call);
        }
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        let name = mac.path.to_token_stream().to_string().replace(' ', "");
        let Some(summary) = self
            .index
            .resolve_macro(self.file, &name, position(mac.span()))
        else {
            return;
        };
        let Ok(arguments) =
            syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
                .parse2(mac.tokens.clone())
        else {
            return;
        };
        let arguments = arguments.into_iter().collect::<Vec<_>>();
        for argument in summary.evaluated(&arguments) {
            self.visit_expr(argument);
        }
    }

    fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
        let expr = syn::Expr::Path(path.clone());
        if let Some(reference) = self.reference(&expr) {
            self.record(reference, AtomicAccessKind::Read, &expr);
        }
    }

    fn visit_expr_index(&mut self, index: &'ast syn::ExprIndex) {
        let expr = syn::Expr::Index(index.clone());
        if let Some(reference) = self.reference(&expr) {
            self.record(reference, AtomicAccessKind::Read, &expr);
            self.visit_expr(&index.index);
        } else {
            syn::visit::visit_expr_index(self, index);
        }
    }

    fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
        if let Some(reference) = self.reference(&assign.left) {
            self.record(
                reference,
                AtomicAccessKind::Write,
                &syn::Expr::Assign(assign.clone()),
            );
            self.visit_expr(&assign.right);
        } else {
            syn::visit::visit_expr_assign(self, assign);
        }
    }

    fn visit_expr_binary(&mut self, expr: &'ast syn::ExprBinary) {
        if matches!(
            expr.op,
            syn::BinOp::AddAssign(_)
                | syn::BinOp::SubAssign(_)
                | syn::BinOp::MulAssign(_)
                | syn::BinOp::DivAssign(_)
                | syn::BinOp::RemAssign(_)
                | syn::BinOp::BitXorAssign(_)
                | syn::BinOp::BitAndAssign(_)
                | syn::BinOp::BitOrAssign(_)
                | syn::BinOp::ShlAssign(_)
                | syn::BinOp::ShrAssign(_)
        ) && let Some(reference) = self.reference(&expr.left)
        {
            self.record(
                reference,
                AtomicAccessKind::ReadModifyWrite,
                &syn::Expr::Binary(expr.clone()),
            );
            self.visit_expr(&expr.right);
        } else {
            syn::visit::visit_expr_binary(self, expr);
        }
    }
}

pub(crate) fn collect_findings(
    files: &[ParsedFile],
    structs: &[StructInfo],
    options: &AnalysisOptions,
) -> Vec<Finding> {
    if !options.candidate_enabled(CandidateKind::StaticData)
        || options.ablated(crate::types::AblationComponent::Hotness)
        || options.ablated(crate::types::AblationComponent::Write)
        || options.ablated(crate::types::AblationComponent::MayParallel)
    {
        return Vec::new();
    }
    let index = Index::new(files);
    let mut declarations = HashMap::new();
    struct Declarations<'a> {
        index: &'a Index,
        file: &'a ParsedFile,
        file_index: usize,
        out: &'a mut HashMap<String, StaticItemInfo>,
    }
    impl<'ast> Visit<'ast> for Declarations<'_> {
        fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
            let name = item.ident.to_string();
            let line = item.span().start().line;
            let Some(identity) = self
                .index
                .resolve_static(self.file, &name, position(item.span()))
            else {
                return;
            };
            let (array_element, array_length) = match item.ty.as_ref() {
                syn::Type::Array(array) => (
                    Some(array.elem.to_token_stream().to_string()),
                    evaluate_index(
                        &array.len,
                        &index_constants(self.index, self.file, &array.len),
                    ),
                ),
                _ => (None, None),
            };
            let ty_str = item.ty.to_token_stream().to_string();
            if array_element.is_some() || is_hot_static_singleton_type(&ty_str) {
                self.out.insert(
                    identity.clone(),
                    StaticItemInfo {
                        name,
                        ty_str,
                        line,
                        position: position(item.span()),
                        file: self.file_index,
                        identity,
                        type_model: static_type_model(&item.ty),
                        array_element,
                        array_length,
                    },
                );
            }
        }
    }
    for (file_index, file) in files.iter().enumerate() {
        Declarations {
            index: &index,
            file,
            file_index,
            out: &mut declarations,
        }
        .visit_file(&file.ast);
    }
    let mut accessors = HashMap::new();
    let mut accesses = HashMap::new();
    struct Accessors<'a, 'b> {
        collector: &'a Collector<'b>,
        out: &'a mut HashMap<String, ReferenceAccessor>,
    }
    impl<'ast> Visit<'ast> for Accessors<'_, '_> {
        fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
            if matches!(&item.sig.output, syn::ReturnType::Type(_, ty) if matches!(ty.as_ref(), syn::Type::Reference(_)))
                && let Some(syn::Stmt::Expr(expr, None)) = item.block.stmts.last()
                && let Some(reference) = self.collector.reference(expr)
                && let Some(identity) = self.collector.index.resolve_function(
                    self.collector.file,
                    &item.sig.ident.to_string(),
                    position(item.span()),
                )
            {
                let parameters: Option<Vec<String>> = item
                    .sig
                    .inputs
                    .iter()
                    .map(|argument| {
                        let syn::FnArg::Typed(argument) = argument else {
                            return None;
                        };
                        let syn::Pat::Ident(argument) = argument.pat.as_ref() else {
                            return None;
                        };
                        Some(argument.ident.to_string())
                    })
                    .collect();
                if let Some(parameters) = parameters {
                    self.out.insert(
                        identity,
                        ReferenceAccessor {
                            reference,
                            parameters,
                        },
                    );
                }
            }
            syn::visit::visit_item_fn(self, item);
        }
    }
    let empty_accessors = HashMap::new();
    for file in files {
        let collector = Collector {
            index: &index,
            file,
            declarations: &declarations,
            structs,
            accessors: &empty_accessors,
            accesses: &mut accesses,
            scopes: Vec::new(),
            function: None,
        };
        Accessors {
            collector: &collector,
            out: &mut accessors,
        }
        .visit_file(&file.ast);
    }
    for file in files {
        Collector {
            index: &index,
            file,
            declarations: &declarations,
            structs,
            accessors: &accessors,
            accesses: &mut accesses,
            scopes: Vec::new(),
            function: None,
        }
        .visit_file(&file.ast);
    }
    let mut findings = Vec::new();
    let mut items = declarations.values().collect::<Vec<_>>();
    items.sort_by_key(|item| (item.file, item.line, &item.name));
    for item in &items {
        let Some(operations) = accesses.get(&item.identity) else {
            continue;
        };
        if !operations.iter().any(|(_, operation)| is_write(operation)) {
            continue;
        }
        let (topology, peers) = if item.array_element.is_some() {
            // Plain indexed stores retain the existing program-parallel rule;
            // global storage alone does not supply their caller capability.
            if !operations.iter().any(|(_, operation)| {
                is_write(operation) && operation.kind == EvidenceKind::HotSyncFieldOps
            }) || item.array_length.is_some_and(|len| len < 2)
                || array_elements_isolated(item, files, structs, &index, options.cache_line_size)
                || !distinct_elements_supported(operations, item.array_length)
            {
                continue;
            }
            (ColocationPattern::ContiguousElements, Vec::new())
        } else {
            let peers = items
                .iter()
                .copied()
                .filter(|peer| {
                    peer.identity != item.identity
                        && peer.array_element.is_none()
                        && peer.file == item.file
                        && peer.line.abs_diff(item.line) <= 8
                        && index.module_at(&files[peer.file].path, peer.position)
                            == index.module_at(&files[item.file].path, item.position)
                        && accesses.contains_key(&peer.identity)
                })
                .collect::<Vec<_>>();
            if peers.is_empty() {
                continue;
            }
            (ColocationPattern::StaticStorage, peers)
        };
        let mut field_list = vec![item.name.clone()];
        field_list.extend(peers.iter().map(|peer| peer.name.clone()));
        field_list.sort();
        field_list.dedup();
        let mut evidence = ConcurrencyEvidenceSet::default();
        evidence
            .evidence
            .extend(operations.iter().map(|(_, operation)| operation.clone()));
        for peer in &peers {
            evidence.evidence.extend(
                accesses[&peer.identity]
                    .iter()
                    .map(|(_, operation)| operation.clone()),
            );
        }
        let locations = if topology == ColocationPattern::ContiguousElements {
            vec![format!("{}[i]", item.name), format!("{}[j]", item.name)]
        } else {
            field_list.clone()
        };
        let mut pattern = build_pattern_context(
            None,
            CandidateKind::StaticData,
            locations,
            topology,
            true,
            Some(&evidence),
            None,
            false,
            Some(ParallelismEvidence::SharedReachability),
            false,
            true,
        );
        // One source operation with a symbolic legal index can denote distinct
        // slots in separate invocations. Its real effect supplies the write.
        if topology == ColocationPattern::ContiguousElements {
            pattern.distinct_accesses = true;
            pattern.access_pattern = AccessPattern::WriteUnknownPeer;
            pattern
                .language_specific_assumptions
                .push("global_storage_may_be_accessed_by_independent_callers");
            if item.array_length.is_none() {
                pattern
                    .language_specific_assumptions
                    .push("array_length_may_allow_distinct_elements");
            }
        }
        if !core_predicate_holds(&pattern) {
            continue;
        }
        let file = &files[item.file];
        let mut neighbors = peers
            .iter()
            .map(|peer| peer.name.as_str())
            .collect::<Vec<_>>();
        neighbors.sort();
        let suffix = if neighbors.is_empty() {
            String::new()
        } else {
            format!(" near {}", neighbors.join(", "))
        };
        let mut finding = make_finding(
            RiskCategory::ColdOrConditional,
            CandidateKind::StaticData,
            if topology == ColocationPattern::StaticStorage {
                "全局热点 singleton 可能与相邻 static 伪共享"
            } else {
                "静态连续同步元素可能共享缓存行"
            },
            Severity::Medium,
            &file.path,
            item.line,
            file.crate_name.as_deref(),
            format!("static {}: {}{suffix}", item.name, item.ty_str),
            "按配置的干扰粒度隔离实际访问的 static 或数组元素，并核对链接器布局与并发调用条件。",
            if topology == ColocationPattern::StaticStorage {
                0.62
            } else {
                0.64
            },
            None,
            &field_list,
            &[],
            Some(&evidence),
        );
        finding.rule_id = pattern.rule_id;
        finding.static_pattern = Some(pattern);
        finding.risk_factors = vec![
            "访问证据: 已解析到具体 static 声明的访问操作，且至少一个写/RMW".into(),
            "并发假设: 不同调用者可能并发使用报告中的全局位置".into(),
        ];
        if topology == ColocationPattern::StaticStorage {
            finding.risk_factors.push(
                "布局假设: 链接器可能使不同全局对象共享配置大小的块；声明顺序不决定地址".into(),
            );
        } else {
            finding.storage_identity = Some(item.identity.clone());
        }
        findings.push(finding);
    }
    findings
}

fn is_write(operation: &EvidenceItem) -> bool {
    matches!(
        operation.access_kind,
        Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
    )
}

fn literal_index(expr: &syn::Expr) -> Option<usize> {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(value),
            ..
        }) => value.base10_parse().ok(),
        syn::Expr::Paren(value) => literal_index(&value.expr),
        _ => None,
    }
}

fn index_constants(index: &Index, file: &ParsedFile, expr: &syn::Expr) -> HashMap<String, usize> {
    struct Constants<'a> {
        index: &'a Index,
        file: &'a ParsedFile,
        values: HashMap<String, usize>,
    }
    impl<'ast> Visit<'ast> for Constants<'_> {
        fn visit_expr_path(&mut self, expr: &'ast syn::ExprPath) {
            let name = expr.path.to_token_stream().to_string().replace(' ', "");
            if let Some(value) =
                self.index
                    .resolve_constant(self.file, &name, position(expr.span()))
            {
                self.values.insert(name, value);
            }
        }
    }
    let mut visitor = Constants {
        index,
        file,
        values: HashMap::new(),
    };
    visitor.visit_expr(expr);
    visitor.values
}

fn evaluate_index(expr: &syn::Expr, values: &HashMap<String, usize>) -> Option<usize> {
    if let Some(value) = literal_index(expr) {
        return Some(value);
    }
    match expr {
        syn::Expr::Path(path) => values
            .get(&path.path.to_token_stream().to_string().replace(' ', ""))
            .copied(),
        syn::Expr::Paren(expr) => evaluate_index(&expr.expr, values),
        syn::Expr::Binary(expr) => {
            let left = evaluate_index(&expr.left, values)?;
            let right = evaluate_index(&expr.right, values)?;
            match expr.op {
                syn::BinOp::Add(_) => left.checked_add(right),
                syn::BinOp::Sub(_) => left.checked_sub(right),
                syn::BinOp::Mul(_) => left.checked_mul(right),
                syn::BinOp::Div(_) => left.checked_div(right),
                syn::BinOp::Rem(_) => left.checked_rem(right),
                _ => None,
            }
        }
        _ => None,
    }
}

fn distinct_elements_supported(
    operations: &[(Reference, EvidenceItem)],
    length: Option<usize>,
) -> bool {
    let mut indices = HashSet::new();
    for (reference, _) in operations {
        let Some(index) = &reference.element_index else {
            continue;
        };
        let Some(value) = syn::parse_str::<syn::Expr>(index)
            .ok()
            .as_ref()
            .and_then(literal_index)
        else {
            return true;
        };
        if length.is_none_or(|length| value < length) {
            indices.insert(value);
        }
    }
    indices.len() >= 2
}

fn array_elements_isolated(
    item: &StaticItemInfo,
    files: &[ParsedFile],
    structs: &[StructInfo],
    index: &Index,
    block: usize,
) -> bool {
    let Some(element) = &item.array_element else {
        return false;
    };
    if crate::struct_layout::estimate_type_size(element) == Some(0) {
        return true;
    }
    let Some(name) = normalize_type_name(element) else {
        return false;
    };
    let file = &files[item.file];
    let records = structs
        .iter()
        .filter(|record| {
            record.name == name
                && record.crate_name == file.crate_name
                && Some(record.module_path.as_str()) == index.module_at(&file.path, item.position)
        })
        .collect::<Vec<_>>();
    matches!(records.as_slice(), [record] if record.total_estimated_size == Some(0)
        || record.repr_align_bytes.is_some_and(|alignment| alignment >= block))
}
fn static_type_model(ty: &syn::Type) -> StaticTypeModel {
    let syn::Type::Path(type_path) = ty else {
        return StaticTypeModel::default();
    };
    let Some(segment) = type_path.path.segments.last() else {
        return StaticTypeModel::default();
    };

    let payload_type = match &segment.arguments {
        syn::PathArguments::AngleBracketed(args) => args.args.iter().find_map(|arg| {
            let syn::GenericArgument::Type(ty) = arg else {
                return None;
            };
            Some(ty.to_token_stream().to_string())
        }),
        _ => None,
    };

    StaticTypeModel {
        outer_type: Some(segment.ident.to_string()),
        payload_type,
    }
}

fn static_method_matches_declared_write_api(item: &StaticItemInfo, method: &str) -> bool {
    match item.type_model.outer_type.as_deref() {
        Some("OnceCell" | "OnceLock") => static_cell_state_write_method(method),
        Some("Lazy" | "LazyLock") => item
            .type_model
            .payload_type
            .as_deref()
            .is_some_and(|payload| payload_method_matches_sync_write_api(payload, method)),
        _ => false,
    }
}

fn static_cell_state_write_method(method: &str) -> bool {
    matches!(method, "set" | "take" | "replace" | "insert")
}

fn payload_method_matches_sync_write_api(payload_ty: &str, method: &str) -> bool {
    // A method reached through a reference/Box/Arc mutates its pointee,
    // not the containing pointer slot. Match the actual outer receiver.
    if crate::helpers::is_indirection_type(payload_ty) {
        return false;
    }
    match normalize_type_name(payload_ty).as_deref() {
        Some(
            "AtomicBool" | "AtomicPtr" | "AtomicI8" | "AtomicI16" | "AtomicI32" | "AtomicI64"
            | "AtomicIsize" | "AtomicU8" | "AtomicU16" | "AtomicU32" | "AtomicU64" | "AtomicUsize",
        ) => atomic_write_or_rmw_method(method),
        Some("RwLock") => lock_write_method(method) || matches!(method, "read" | "try_read"),
        Some("Mutex" | "SeqLock" | "WordLock") => lock_write_method(method),
        Some("UnsafeCell" | "Cell") => mutable_cell_write_method(method),
        Some("Notify" | "AtomicWaker") => wakeup_state_write_method(method),
        _ => false,
    }
}

fn atomic_write_or_rmw_method(method: &str) -> bool {
    matches!(
        method,
        "store"
            | "swap"
            | "fetch_add"
            | "fetch_sub"
            | "fetch_and"
            | "fetch_nand"
            | "fetch_or"
            | "fetch_xor"
            | "fetch_update"
            | "fetch_max"
            | "fetch_min"
            | "compare_exchange"
            | "compare_exchange_weak"
    )
}

fn lock_write_method(method: &str) -> bool {
    matches!(method, "lock" | "try_lock" | "write" | "try_write")
}

fn mutable_cell_write_method(method: &str) -> bool {
    matches!(
        method,
        "borrow_mut" | "get_mut" | "replace" | "take" | "set"
    )
}

fn wakeup_state_write_method(method: &str) -> bool {
    matches!(
        method,
        "notify_one" | "notify_waiters" | "wake" | "wake_by_ref" | "register"
    )
}
