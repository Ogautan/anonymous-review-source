//! Conservative storage binding for file-level findings. Module paths and explicit
//! imports bind statics; unresolved/glob aliases remain separate occurrences.
use crate::types::{CandidateKind, ColocationPattern, Finding, ParsedFile};
use quote::ToTokens;
use std::collections::HashMap;
use syn::{spanned::Spanned, visit::Visit};

type Key = (Option<String>, String);
pub(crate) type Position = (usize, usize);
type ScopedBindings<T> = HashMap<(String, String), Vec<(Position, Position, T)>>;
type ScopedModules = HashMap<String, Vec<(Position, Position, String)>>;
type ShadowRanges = HashMap<(String, String), Vec<(Position, Position)>>;

pub(crate) fn position(span: proc_macro2::Span) -> Position {
    (span.start().line, span.start().column)
}
fn range(span: proc_macro2::Span) -> (Position, Position) {
    (position(span), (span.end().line, span.end().column))
}
#[derive(Default)]
pub(crate) struct Index {
    statics: HashMap<Key, Vec<String>>,
    functions: HashMap<Key, Vec<String>>,
    constants: HashMap<Key, Vec<usize>>,
    macros: HashMap<Key, Vec<crate::rust_macros::ExpressionArguments>>,
    imports: HashMap<Key, Vec<String>>,
    modules: ScopedModules,
    implementations: HashMap<String, Vec<(usize, usize, String)>>,
    shadows: ShadowRanges,
    local_statics: ScopedBindings<String>,
    local_constants: ScopedBindings<usize>,
    local_functions: ScopedBindings<String>,
}

impl Index {
    pub(crate) fn new(files: &[ParsedFile]) -> Self {
        let mut index = Self::default();
        for file in files {
            index.items(
                file,
                &file.ast.items,
                &file.module_path,
                (0, 0),
                (usize::MAX, usize::MAX),
            );
            Shadows {
                file: &file.path,
                scope: ((0, 0), (usize::MAX, usize::MAX)),
                index: &mut index,
            }
            .visit_file(&file.ast);
        }
        // Different block-local declarations may share both a name and a
        // source line. Preserve old identities when unique; disambiguate only
        // actual collisions with the containing lexical block's position.
        let mut counts = HashMap::new();
        for (_, _, identity) in index.local_statics.values().flatten() {
            *counts.entry(identity.clone()).or_insert(0) += 1;
        }
        for (start, _, identity) in index.local_statics.values_mut().flatten() {
            if counts.get(identity).is_some_and(|count| *count > 1)
                && let Some((prefix, symbol)) = identity.rsplit_once("::")
            {
                *identity = format!("{prefix}::block_{}_{}::{symbol}", start.0, start.1);
            }
        }
        index
    }

    pub(crate) fn module_at(&self, file: &str, at: Position) -> Option<&str> {
        self.modules
            .get(file)?
            .iter()
            .rev()
            .find(|(start, end, _)| *start <= at && at <= *end)
            .map(|(_, _, module)| module.as_str())
    }

    pub(crate) fn resolve_static(
        &self,
        file: &ParsedFile,
        name: &str,
        at: Position,
    ) -> Option<String> {
        if !name.contains("::") {
            let key = (file.path.clone(), name.to_string());
            if self
                .shadows
                .get(&key)
                .is_some_and(|ranges| ranges.iter().any(|(start, end)| *start <= at && at <= *end))
            {
                return None;
            }
            if let Some(identity) = local_binding(&self.local_statics, file, name, at) {
                return Some(identity);
            }
        }
        self.resolve_named(file, name, at, &self.statics)
    }

    pub(crate) fn resolve_function(
        &self,
        file: &ParsedFile,
        name: &str,
        at: Position,
    ) -> Option<String> {
        if let Some(identity) = local_binding(&self.local_functions, file, name, at) {
            return Some(identity);
        }
        self.resolve_named(file, name, at, &self.functions)
    }

    pub(crate) fn resolve_macro(
        &self,
        file: &ParsedFile,
        name: &str,
        at: Position,
    ) -> Option<crate::rust_macros::ExpressionArguments> {
        self.resolve_named(file, name, at, &self.macros)
    }

    pub(crate) fn resolve_constant(
        &self,
        file: &ParsedFile,
        name: &str,
        at: Position,
    ) -> Option<usize> {
        if let Some(value) = local_binding(&self.local_constants, file, name, at) {
            return Some(value);
        }
        self.resolve_named(file, name, at, &self.constants)
    }

    fn resolve_named<T: Clone>(
        &self,
        file: &ParsedFile,
        name: &str,
        at: Position,
        declarations: &HashMap<Key, Vec<T>>,
    ) -> Option<T> {
        let module = self.module_at(&file.path, at)?;
        let mut path = qualify(module, name);
        let mut visited = std::collections::HashSet::new();
        while visited.insert(path.clone()) && visited.len() <= 32 {
            let key = (file.crate_name.clone(), path.clone());
            if let Some([identity]) = declarations.get(&key).map(Vec::as_slice) {
                return Some(identity.clone());
            }
            let parts = path.split("::").collect::<Vec<_>>();
            let replacement = (1..=parts.len()).rev().find_map(|len| {
                let [target] = self
                    .imports
                    .get(&(file.crate_name.clone(), parts[..len].join("::")))?
                    .as_slice()
                else {
                    return None;
                };
                Some(if len == parts.len() {
                    target.clone()
                } else {
                    format!("{target}::{}", parts[len..].join("::"))
                })
            });
            path = replacement?;
        }
        None
    }
}

fn local_binding<T: Clone>(
    bindings: &ScopedBindings<T>,
    file: &ParsedFile,
    name: &str,
    at: Position,
) -> Option<T> {
    bindings
        .get(&(file.path.clone(), name.into()))?
        .iter()
        .filter(|(start, end, _)| *start <= at && at <= *end)
        .min_by_key(|(start, end, _)| {
            (end.0.saturating_sub(start.0), end.1.saturating_sub(start.1))
        })
        .map(|(_, _, value)| value.clone())
}

pub(crate) fn bind_findings(
    files: &[ParsedFile],
    structs: &[crate::types::StructInfo],
    findings: &mut [Finding],
) {
    if !findings.iter().any(|f| {
        f.storage_identity.is_none()
            && matches!(
                f.candidate_kind,
                CandidateKind::StaticData | CandidateKind::IndexedWrites
            )
    }) {
        return;
    }
    let index = Index::new(files);
    for finding in findings {
        if finding.storage_identity.is_some()
            || finding.struct_name.is_some()
            || !matches!(
                finding.candidate_kind,
                CandidateKind::StaticData | CandidateKind::IndexedWrites
            )
            || finding
                .static_pattern
                .as_ref()
                .is_none_or(|p| p.colocation_pattern != ColocationPattern::ContiguousElements)
        {
            continue;
        }
        let [name] = finding.field_list.as_slice() else {
            continue;
        };
        let name = name.replace(' ', "");
        if let Some(field) = name.strip_prefix("self.") {
            if !field.contains('.')
                && let Some(implementations) = index.implementations.get(&finding.file)
                && let Some((_, _, ty)) = implementations
                    .iter()
                    .find(|(start, end, _)| *start <= finding.line && finding.line <= *end)
            {
                let matches = structs
                    .iter()
                    .filter(|si| {
                        si.crate_name == finding.crate_name
                            && qualify(&si.module_path, &si.name) == *ty
                    })
                    .collect::<Vec<_>>();
                if let [si] = matches.as_slice() {
                    crate::rules::bind_indexed_record_finding(finding, si, field);
                }
            }
            continue;
        }
        if name.contains(['.', '[', '(', '*', '&']) {
            continue;
        }
        if let Some(file) = files.iter().find(|file| file.path == finding.file) {
            finding.storage_identity = index.resolve_static(file, &name, (finding.line, 0));
        }
    }
}
fn qualify(module: &str, path: &str) -> String {
    let mut parts = module
        .split("::")
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect::<Vec<_>>();
    let mut path = path.split("::").peekable();
    match path.peek().copied() {
        Some("crate") | Some("") => {
            parts.clear();
            path.next();
        }
        Some("self") => {
            path.next();
        }
        _ => {}
    }
    while path.peek() == Some(&"super") {
        parts.pop();
        path.next();
    }
    parts.extend(path.map(str::to_string));
    parts.join("::")
}
impl Index {
    fn items(
        &mut self,
        file: &ParsedFile,
        items: &[syn::Item],
        module: &str,
        start: Position,
        end: Position,
    ) {
        self.modules
            .entry(file.path.clone())
            .or_default()
            .push((start, end, module.into()));
        for item in items {
            match item {
                syn::Item::Macro(item) => {
                    if item.mac.path.is_ident("macro_rules")
                        && let Some(name) = &item.ident
                        && let Some(summary) =
                            crate::rust_macros::ExpressionArguments::parse(item.mac.tokens.clone())
                    {
                        self.macros
                            .entry((file.crate_name.clone(), qualify(module, &name.to_string())))
                            .or_default()
                            .push(summary);
                    }
                }
                syn::Item::Const(item) => {
                    if let syn::Expr::Lit(syn::ExprLit {
                        lit: syn::Lit::Int(value),
                        ..
                    }) = item.expr.as_ref()
                        && let Ok(value) = value.base10_parse()
                    {
                        self.constants
                            .entry((
                                file.crate_name.clone(),
                                qualify(module, &item.ident.to_string()),
                            ))
                            .or_default()
                            .push(value);
                    }
                }
                syn::Item::Fn(item) => {
                    let name = qualify(module, &item.sig.ident.to_string());
                    self.functions
                        .entry((file.crate_name.clone(), name.clone()))
                        .or_default()
                        .push(format!(
                            "{}::{name}@{}",
                            file.path,
                            item.span().start().line
                        ));
                }
                syn::Item::Static(item) => {
                    let name = qualify(module, &item.ident.to_string());
                    self.statics
                        .entry((file.crate_name.clone(), name.clone()))
                        .or_default()
                        .push(format!(
                            "{}::{name}@{}",
                            file.path,
                            item.span().start().line
                        ));
                }
                syn::Item::Impl(item) => {
                    if let syn::Type::Path(path) = item.self_ty.as_ref()
                        && path.qself.is_none()
                        && path.path.segments.iter().all(|s| s.arguments.is_empty())
                    {
                        let ty = path.path.to_token_stream().to_string().replace(' ', "");
                        self.implementations
                            .entry(file.path.clone())
                            .or_default()
                            .push((
                                item.span().start().line,
                                item.span().end().line,
                                qualify(module, &ty),
                            ));
                    }
                }
                syn::Item::Use(item) => {
                    let mut imports = Vec::new();
                    use_paths(&item.tree, "", &mut imports);
                    for (alias, target) in imports {
                        // Rust 2018 unprefixed use paths start at the crate root.
                        let target =
                            if target.starts_with("self::") || target.starts_with("super::") {
                                qualify(module, &target)
                            } else {
                                qualify("", &target)
                            };
                        self.imports
                            .entry((file.crate_name.clone(), qualify(module, &alias)))
                            .or_default()
                            .push(target);
                    }
                }
                syn::Item::Mod(item) => {
                    if let Some((_, items)) = &item.content {
                        self.items(
                            file,
                            items,
                            &qualify(module, &item.ident.to_string()),
                            range(item.span()).0,
                            range(item.span()).1,
                        );
                    }
                }
                _ => {}
            }
        }
    }
}
fn use_paths(tree: &syn::UseTree, prefix: &str, out: &mut Vec<(String, String)>) {
    let join = |name: &str| {
        if prefix.is_empty() {
            name.to_string()
        } else {
            format!("{prefix}::{name}")
        }
    };
    match tree {
        syn::UseTree::Path(path) => use_paths(&path.tree, &join(&path.ident.to_string()), out),
        syn::UseTree::Name(name) => {
            out.push((name.ident.to_string(), join(&name.ident.to_string())))
        }
        syn::UseTree::Rename(name) => {
            out.push((name.rename.to_string(), join(&name.ident.to_string())))
        }
        syn::UseTree::Group(group) => {
            for item in &group.items {
                use_paths(item, prefix, out);
            }
        }
        syn::UseTree::Glob(_) => {}
    }
}
struct Shadows<'a> {
    file: &'a str,
    scope: (Position, Position),
    index: &'a mut Index,
}
impl<'ast> Visit<'ast> for Shadows<'_> {
    fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
        if self.scope.1 != (usize::MAX, usize::MAX)
            && let syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(value),
                ..
            }) = item.expr.as_ref()
            && let Ok(value) = value.base10_parse()
        {
            self.index
                .local_constants
                .entry((self.file.into(), item.ident.to_string()))
                .or_default()
                .push((self.scope.0, self.scope.1, value));
        }
    }
    fn visit_block(&mut self, block: &'ast syn::Block) {
        let old = self.scope;
        self.scope = range(block.span());
        syn::visit::visit_block(self, block);
        self.scope = old;
    }

    fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
        if self.scope.1 != (usize::MAX, usize::MAX) {
            let line = item.span().start().line;
            let module = self
                .index
                .module_at(self.file, position(item.span()))
                .unwrap_or("");
            let identity = format!(
                "{}::{}@{line}",
                self.file,
                qualify(module, &item.ident.to_string())
            );
            self.index
                .local_statics
                .entry((self.file.into(), item.ident.to_string()))
                .or_default()
                .push((self.scope.0, self.scope.1, identity));
        }
        // A declaration's initializer does not supply a concurrent access.
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        if self.scope.1 != (usize::MAX, usize::MAX) {
            let module = self
                .index
                .module_at(self.file, position(item.span()))
                .unwrap_or("");
            let name = format!(
                "block_{}_{}::{}",
                self.scope.0.0, self.scope.0.1, item.sig.ident
            );
            let identity = format!(
                "{}::{}@{}",
                self.file,
                qualify(module, &name),
                item.span().start().line
            );
            self.index
                .local_functions
                .entry((self.file.into(), item.sig.ident.to_string()))
                .or_default()
                .push((self.scope.0, self.scope.1, identity));
        }
        let old = self.scope;
        self.scope = range(item.span());
        syn::visit::visit_item_fn(self, item);
        self.scope = old;
    }
    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        let old = self.scope;
        self.scope = range(item.span());
        syn::visit::visit_impl_item_fn(self, item);
        self.scope = old;
    }
    fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
        self.index
            .shadows
            .entry((self.file.into(), pat.ident.to_string()))
            .or_default()
            .push(self.scope);
        syn::visit::visit_pat_ident(self, pat);
    }
}
