//! Source-proven auto-trait restrictions for shared API assumptions.
//! Unknown types and conditional positive implementations remain unresolved.

use crate::types::{ParsedFile, StructInfo, StructKey};
use std::collections::{HashMap, HashSet};
use syn::{GenericArgument, Item, PathArguments, Type, UseTree};

type Definitions = HashMap<StructKey, Option<Vec<Type>>>;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Restrictions {
    not_send: bool,
    not_sync: bool,
}

impl Restrictions {
    fn combine(self, other: Self) -> Self {
        Self {
            not_send: self.not_send || other.not_send,
            not_sync: self.not_sync || other.not_sync,
        }
    }
}

#[derive(Default)]
struct Scope {
    imports: HashMap<String, Vec<String>>,
    aliases: HashMap<String, Type>,
    local_names: HashSet<String>,
    cell_glob: bool,
    ambiguous_imports: HashSet<String>,
}

type Scopes = HashMap<(String, String), Scope>;

fn bind_import(scope: &mut Scope, name: String, path: Vec<String>) {
    if scope
        .imports
        .get(&name)
        .is_some_and(|existing| existing != &path)
    {
        scope.ambiguous_imports.insert(name.clone());
    }
    scope.imports.insert(name, path);
}

fn item_attributes(item: &Item) -> &[syn::Attribute] {
    match item {
        Item::Use(item) => &item.attrs,
        Item::Type(item) => &item.attrs,
        Item::Struct(item) => &item.attrs,
        Item::Enum(item) => &item.attrs,
        Item::Union(item) => &item.attrs,
        Item::Trait(item) => &item.attrs,
        Item::Mod(item) => &item.attrs,
        Item::Impl(item) => &item.attrs,
        _ => &[],
    }
}

fn conditional(attrs: &[syn::Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| attr.path().is_ident("cfg") || attr.path().is_ident("cfg_attr"))
}

fn collect_use(tree: &UseTree, prefix: Vec<String>, scope: &mut Scope) {
    match tree {
        UseTree::Path(path) => {
            let mut prefix = prefix;
            prefix.push(path.ident.to_string());
            collect_use(&path.tree, prefix, scope);
        }
        UseTree::Group(group) => {
            for tree in &group.items {
                collect_use(tree, prefix.clone(), scope);
            }
        }
        UseTree::Name(name) => {
            let mut path = prefix;
            if name.ident != "self" {
                path.push(name.ident.to_string());
            }
            if let Some(name) = path.last() {
                bind_import(scope, name.clone(), path);
            }
        }
        UseTree::Rename(rename) => {
            let mut path = prefix;
            if rename.ident != "self" {
                path.push(rename.ident.to_string());
            }
            bind_import(scope, rename.rename.to_string(), path);
        }
        UseTree::Glob(_) => {
            scope.cell_glob |= prefix == ["std", "cell"] || prefix == ["core", "cell"]
        }
    }
}

fn collect_scopes(
    items: &[Item],
    crate_name: &str,
    module: &str,
    scopes: &mut Scopes,
    definitions: &mut Definitions,
) {
    let scope = scopes
        .entry((crate_name.into(), module.into()))
        .or_default();
    for item in items {
        if crate::helpers::cfg_is_test_only(item_attributes(item)) {
            continue;
        }
        match item {
            Item::Use(item) if !conditional(&item.attrs) => {
                collect_use(&item.tree, Vec::new(), scope)
            }
            Item::Type(item) => {
                scope.local_names.insert(item.ident.to_string());
                let ty = if conditional(&item.attrs) {
                    syn::parse_quote!(_)
                } else {
                    (*item.ty).clone()
                };
                scope
                    .aliases
                    .entry(item.ident.to_string())
                    .and_modify(|ty| *ty = syn::parse_quote!(_))
                    .or_insert(ty);
            }
            Item::Struct(item) => {
                scope.local_names.insert(item.ident.to_string());
                let key = StructKey::new(crate_name, module, item.ident.to_string());
                let fields = item
                    .fields
                    .iter()
                    .filter(|field| {
                        !field.attrs.iter().any(|attr| {
                            attr.path().is_ident("cfg") || attr.path().is_ident("cfg_attr")
                        })
                    })
                    .map(|field| field.ty.clone())
                    .collect();
                definitions
                    .entry(key)
                    .and_modify(|fields| *fields = None)
                    .or_insert(Some(fields));
            }
            Item::Enum(item) => {
                scope.local_names.insert(item.ident.to_string());
            }
            Item::Union(item) => {
                scope.local_names.insert(item.ident.to_string());
            }
            Item::Trait(item) => {
                scope.local_names.insert(item.ident.to_string());
            }
            Item::Mod(item) => {
                scope.local_names.insert(item.ident.to_string());
            }
            _ => {}
        }
    }
    for item in items {
        if let Item::Mod(item) = item
            && !crate::helpers::cfg_is_test_only(&item.attrs)
            && let Some((_, children)) = &item.content
        {
            let child = if module.is_empty() {
                item.ident.to_string()
            } else {
                format!("{module}::{}", item.ident)
            };
            collect_scopes(children, crate_name, &child, scopes, definitions);
        }
    }
}

enum Binding {
    External(Vec<String>),
    Local(StructKey),
}

fn resolve(path: &syn::Path, crate_name: &str, module: &str, scopes: &Scopes) -> Option<Binding> {
    let mut parts = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    let first = parts.first()?.clone();
    let scope = scopes.get(&(crate_name.into(), module.into()));
    if scope.is_some_and(|scope| scope.ambiguous_imports.contains(&first)) {
        return None;
    }
    if path.leading_colon.is_none()
        && let Some(import) = scope.and_then(|scope| scope.imports.get(&first))
    {
        parts.splice(..1, import.clone());
    } else if parts.len() == 1 && !scope.is_some_and(|scope| scope.local_names.contains(&first)) {
        if matches!(first.as_str(), "Send" | "Sync") {
            return Some(Binding::External(vec![
                "core".into(),
                "marker".into(),
                first,
            ]));
        }
        if matches!(first.as_str(), "Box" | "Vec" | "Option" | "Result") {
            return Some(Binding::External(vec!["prelude".into(), first]));
        }
        if scope.is_some_and(|scope| scope.cell_glob)
            && matches!(
                first.as_str(),
                "Cell" | "RefCell" | "UnsafeCell" | "OnceCell" | "LazyCell"
            )
        {
            return Some(Binding::External(vec!["core".into(), "cell".into(), first]));
        }
    }
    if matches!(
        parts.first().map(String::as_str),
        Some("std" | "core" | "alloc" | "prelude")
    ) && (path.leading_colon.is_some()
        || !scope.is_some_and(|scope| scope.local_names.contains(&parts[0])))
    {
        return Some(Binding::External(parts));
    }
    let mut qualified = module
        .split("::")
        .filter(|part| !part.is_empty())
        .map(str::to_owned)
        .collect::<Vec<_>>();
    if parts
        .first()
        .is_some_and(|part| part == "crate" || part == crate_name)
    {
        qualified.clear();
        parts.remove(0);
    } else if parts.first().is_some_and(|part| part == "self") {
        parts.remove(0);
    }
    while parts.first().is_some_and(|part| part == "super") {
        qualified.pop();
        parts.remove(0);
    }
    let name = parts.pop()?;
    qualified.extend(parts);
    Some(Binding::Local(StructKey::new(
        crate_name.to_owned(),
        qualified.join("::"),
        name,
    )))
}

fn restrictions(
    ty: &Type,
    crate_name: &str,
    module: &str,
    scopes: &Scopes,
    facts: &HashMap<StructKey, Restrictions>,
    depth: usize,
) -> Restrictions {
    if depth > 32 {
        return Restrictions::default();
    }
    let recurse = |ty: &Type| restrictions(ty, crate_name, module, scopes, facts, depth + 1);
    match ty {
        Type::Ptr(_) => Restrictions {
            not_send: true,
            not_sync: true,
        },
        Type::Reference(reference) => {
            let inner = recurse(&reference.elem);
            Restrictions {
                not_send: if reference.mutability.is_some() {
                    inner.not_send
                } else {
                    inner.not_sync
                },
                not_sync: inner.not_sync,
            }
        }
        Type::Array(array) => recurse(&array.elem),
        Type::Slice(slice) => recurse(&slice.elem),
        Type::Paren(paren) => recurse(&paren.elem),
        Type::Group(group) => recurse(&group.elem),
        Type::Tuple(tuple) => tuple
            .elems
            .iter()
            .map(recurse)
            .fold(Restrictions::default(), Restrictions::combine),
        Type::Path(path) if path.qself.is_none() => {
            let Some(binding) = resolve(&path.path, crate_name, module, scopes) else {
                return Restrictions::default();
            };
            match binding {
                Binding::Local(key) => {
                    if let Some(alias) = scopes
                        .get(&(key.crate_name.clone(), key.module_path.clone()))
                        .and_then(|scope| scope.aliases.get(&key.name))
                    {
                        restrictions(
                            alias,
                            crate_name,
                            &key.module_path,
                            scopes,
                            facts,
                            depth + 1,
                        )
                    } else {
                        facts.get(&key).copied().unwrap_or_default()
                    }
                }
                Binding::External(parts) => {
                    let name = parts.join("::");
                    let inner = path_arguments(&path.path)
                        .map(recurse)
                        .fold(Restrictions::default(), Restrictions::combine);
                    match name.as_str() {
                        "std::cell::Cell"
                        | "core::cell::Cell"
                        | "std::cell::RefCell"
                        | "core::cell::RefCell"
                        | "std::cell::UnsafeCell"
                        | "core::cell::UnsafeCell"
                        | "std::cell::OnceCell"
                        | "core::cell::OnceCell"
                        | "std::cell::LazyCell"
                        | "core::cell::LazyCell" => Restrictions {
                            not_send: inner.not_send,
                            not_sync: true,
                        },
                        "std::rc::Rc" | "alloc::rc::Rc" | "std::rc::Weak" | "alloc::rc::Weak"
                        | "std::ptr::NonNull" | "core::ptr::NonNull" => Restrictions {
                            not_send: true,
                            not_sync: true,
                        },
                        "std::sync::Arc" | "alloc::sync::Arc" | "std::sync::Weak"
                        | "alloc::sync::Weak" => Restrictions {
                            not_send: inner.not_send || inner.not_sync,
                            not_sync: inner.not_send || inner.not_sync,
                        },
                        "std::sync::Mutex" => Restrictions {
                            not_send: inner.not_send,
                            not_sync: inner.not_send,
                        },
                        "std::sync::RwLock" => inner,
                        "prelude::Box"
                        | "std::boxed::Box"
                        | "alloc::boxed::Box"
                        | "prelude::Vec"
                        | "std::vec::Vec"
                        | "alloc::vec::Vec"
                        | "prelude::Option"
                        | "std::option::Option"
                        | "core::option::Option"
                        | "prelude::Result"
                        | "std::result::Result"
                        | "core::result::Result"
                        | "std::marker::PhantomData"
                        | "core::marker::PhantomData" => inner,
                        _ => Restrictions::default(),
                    }
                }
            }
        }
        _ => Restrictions::default(),
    }
}

fn path_arguments(path: &syn::Path) -> impl Iterator<Item = &Type> {
    path.segments
        .iter()
        .flat_map(|segment| match &segment.arguments {
            PathArguments::AngleBracketed(arguments) => Some(&arguments.args),
            _ => None,
        })
        .flatten()
        .filter_map(|argument| match argument {
            GenericArgument::Type(ty) => Some(ty),
            _ => None,
        })
}

fn collect_impls(
    items: &[Item],
    crate_name: &str,
    module: &str,
    scopes: &Scopes,
    overrides: &mut HashMap<(StructKey, String), bool>,
    projections: &mut HashMap<StructKey, HashSet<String>>,
) {
    for item in items {
        if crate::helpers::cfg_is_test_only(item_attributes(item)) {
            continue;
        }
        if let Item::Impl(item) = item
            && let Type::Path(ty) = item.self_ty.as_ref()
            && let Some(Binding::Local(key)) = resolve(&ty.path, crate_name, module, scopes)
        {
            for method in &item.items {
                if let syn::ImplItem::Fn(method) = method
                    && (matches!(method.vis, syn::Visibility::Public(_)) || item.trait_.is_some())
                    && matches!(&method.sig.output, syn::ReturnType::Type(_, ty) if matches!(ty.as_ref(), Type::Reference(reference) if reference.mutability.is_none()))
                {
                    let mut collector = SharedProjections::default();
                    syn::visit::Visit::visit_block(&mut collector, &method.block);
                    projections
                        .entry(key.clone())
                        .or_default()
                        .extend(collector.0);
                }
            }
        }
        if let Item::Impl(item) = item
            && !crate::helpers::cfg_is_test_only(&item.attrs)
            && let Some((negative, trait_path, _)) = &item.trait_
            && let Some(Binding::External(trait_name)) =
                resolve(trait_path, crate_name, module, scopes)
            && matches!(
                trait_name.join("::").as_str(),
                "std::marker::Sync"
                    | "core::marker::Sync"
                    | "std::marker::Send"
                    | "core::marker::Send"
            )
            && let Type::Path(ty) = item.self_ty.as_ref()
            && let Some(Binding::Local(key)) = resolve(&ty.path, crate_name, module, scopes)
        {
            // A possible positive impl blocks a universal negative conclusion.
            // Conditional negative impls cannot establish a universal failure.
            if negative.is_none()
                || !item
                    .attrs
                    .iter()
                    .any(|attr| attr.path().is_ident("cfg") || attr.path().is_ident("cfg_attr"))
            {
                overrides.insert(
                    (key, trait_name.last().unwrap().clone()),
                    negative.is_some(),
                );
            }
        }
        if let Item::Mod(item) = item
            && let Some((_, children)) = &item.content
        {
            let child = if module.is_empty() {
                item.ident.to_string()
            } else {
                format!("{module}::{}", item.ident)
            };
            collect_impls(children, crate_name, &child, scopes, overrides, projections);
        }
    }
}

#[derive(Default)]
struct SharedProjections(HashSet<String>);

impl<'ast> syn::visit::Visit<'ast> for SharedProjections {
    fn visit_expr_reference(&mut self, node: &'ast syn::ExprReference) {
        fn own_field(expression: &syn::Expr) -> Option<String> {
            match expression {
                syn::Expr::Field(field) => {
                    if matches!(field.base.as_ref(), syn::Expr::Path(path) if path.path.is_ident("self"))
                    {
                        match &field.member {
                            syn::Member::Named(name) => Some(name.to_string()),
                            syn::Member::Unnamed(index) => Some(index.index.to_string()),
                        }
                    } else {
                        own_field(&field.base)
                    }
                }
                syn::Expr::Paren(paren) => own_field(&paren.expr),
                _ => None,
            }
        }
        if node.mutability.is_none()
            && let Some(field) = own_field(&node.expr)
        {
            self.0.insert(field);
        }
        syn::visit::visit_expr_reference(self, node);
    }
}

pub(crate) fn annotate(files: &[ParsedFile], records: &mut [StructInfo]) {
    let mut scopes = Scopes::new();
    let mut definitions = Definitions::new();
    for file in files {
        collect_scopes(
            &file.ast.items,
            file.crate_name.as_deref().unwrap_or("unknown"),
            &file.module_path,
            &mut scopes,
            &mut definitions,
        );
    }
    let mut overrides = HashMap::new();
    let mut projections = HashMap::new();
    for file in files {
        collect_impls(
            &file.ast.items,
            file.crate_name.as_deref().unwrap_or("unknown"),
            &file.module_path,
            &scopes,
            &mut overrides,
            &mut projections,
        );
    }
    let mut facts = HashMap::new();
    for _ in 0..=records.len() {
        let mut changed = false;
        for record in records.iter() {
            let key = StructKey::from_struct(record);
            let Some(Some(fields)) = definitions.get(&key) else {
                continue;
            };
            let mut value = fields
                .iter()
                .map(|ty| restrictions(ty, &key.crate_name, &key.module_path, &scopes, &facts, 0))
                .fold(Restrictions::default(), Restrictions::combine);
            if let Some(negative) = overrides.get(&(key.clone(), "Send".into())) {
                value.not_send = *negative;
            }
            if let Some(negative) = overrides.get(&(key.clone(), "Sync".into())) {
                value.not_sync = *negative;
            }
            if facts.get(&key) != Some(&value) {
                facts.insert(key, value);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for record in records {
        record.known_not_sync = facts
            .get(&StructKey::from_struct(record))
            .is_some_and(|value| value.not_sync);
        record.shared_field_projections = projections
            .remove(&StructKey::from_struct(record))
            .unwrap_or_default()
            .into_iter()
            .collect();
        record.shared_field_projections.sort();
    }
}
