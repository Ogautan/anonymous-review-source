//! Rust module/API reachability.
//!
//! `pub` on an item is only externally meaningful when every containing
//! module is externally reachable (or the item is publicly re-exported).

use std::collections::{HashMap, HashSet, VecDeque};

use syn::visit::Visit;
use syn::{ItemMod, ItemUse, UseTree, Visibility};

use crate::types::{ItemVisibility, ParsedFile, StructInfo, StructKey};

pub type ModuleKey = (String, String);

#[derive(Debug)]
struct ModuleEdge {
    parent: ModuleKey,
    child: ModuleKey,
    externally_visible: bool,
}

#[derive(Debug)]
struct PublicUse {
    crate_name: String,
    module_path: String,
    path: Vec<String>,
    glob: bool,
}

pub fn apply_external_reachability(files: &[ParsedFile], structs: &mut [StructInfo]) {
    let graph = VisibilityGraph::collect(files);
    let reachable = graph.reachable_modules();
    let (reexported_types, reexported_modules) = graph.public_reexports(&reachable);

    for record in structs {
        let crate_name = record
            .crate_name
            .clone()
            .unwrap_or_else(|| "unknown".to_string());
        let module_key = (crate_name.clone(), record.module_path.clone());
        let struct_key = StructKey::from_struct(record);
        let naturally_reachable =
            reachable.contains(&module_key) && record.visibility.is_externally_exposed();
        let reexported = record.visibility.is_externally_exposed()
            && (reexported_types.contains(&struct_key) || reexported_modules.contains(&module_key));
        if !naturally_reachable && !reexported {
            // Preserve the distinction between an item that is private even
            // inside its crate and a `pub` item hidden behind a private module.
            // The latter is not an external API, but remains a valid
            // project-internal sharing capability.
            if record.visibility == ItemVisibility::Public {
                record.visibility = ItemVisibility::Restricted;
            }
            record.public_fields.clear();
        }
    }
}

pub fn externally_reachable_modules(files: &[ParsedFile]) -> HashSet<ModuleKey> {
    VisibilityGraph::collect(files).reachable_modules()
}

struct VisibilityGraph {
    crate_roots: HashSet<ModuleKey>,
    edges: Vec<ModuleEdge>,
    public_uses: Vec<PublicUse>,
}

impl VisibilityGraph {
    fn collect(files: &[ParsedFile]) -> Self {
        let mut graph = Self {
            crate_roots: HashSet::new(),
            edges: Vec::new(),
            public_uses: Vec::new(),
        };
        for file in files {
            let crate_name = file
                .crate_name
                .clone()
                .unwrap_or_else(|| "unknown".to_string());
            graph
                .crate_roots
                .insert((crate_name.clone(), String::new()));
            let mut collector = ModuleCollector {
                crate_name,
                module_path: file.module_path.clone(),
                edges: &mut graph.edges,
                public_uses: &mut graph.public_uses,
            };
            collector.visit_file(&file.ast);
        }
        graph
    }

    fn reachable_modules(&self) -> HashSet<ModuleKey> {
        let mut reachable = self.crate_roots.clone();
        let mut queue = self.crate_roots.iter().cloned().collect::<VecDeque<_>>();
        let mut outgoing: HashMap<&ModuleKey, Vec<&ModuleEdge>> = HashMap::new();
        for edge in &self.edges {
            outgoing.entry(&edge.parent).or_default().push(edge);
        }
        while let Some(module) = queue.pop_front() {
            for edge in outgoing.get(&module).into_iter().flatten() {
                if edge.externally_visible && reachable.insert(edge.child.clone()) {
                    queue.push_back(edge.child.clone());
                }
            }
        }
        reachable
    }

    fn public_reexports(
        &self,
        reachable: &HashSet<ModuleKey>,
    ) -> (HashSet<StructKey>, HashSet<ModuleKey>) {
        let mut types = HashSet::new();
        let mut modules = HashSet::new();
        for item_use in &self.public_uses {
            if !reachable.contains(&(item_use.crate_name.clone(), item_use.module_path.clone())) {
                continue;
            }
            let resolved = resolve_use_path(&item_use.module_path, &item_use.path);
            if item_use.glob {
                modules.insert((item_use.crate_name.clone(), resolved.join("::")));
            } else if let Some((name, module)) = resolved.split_last() {
                types.insert(StructKey::new(
                    item_use.crate_name.clone(),
                    module.join("::"),
                    name.clone(),
                ));
            }
        }
        (types, modules)
    }
}

struct ModuleCollector<'a> {
    crate_name: String,
    module_path: String,
    edges: &'a mut Vec<ModuleEdge>,
    public_uses: &'a mut Vec<PublicUse>,
}

impl<'ast> Visit<'ast> for ModuleCollector<'_> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        if cfg_is_test_only(&node.attrs) {
            return;
        }
        let child_path = join_module_path(&self.module_path, &node.ident.to_string());
        self.edges.push(ModuleEdge {
            parent: (self.crate_name.clone(), self.module_path.clone()),
            child: (self.crate_name.clone(), child_path.clone()),
            externally_visible: matches!(node.vis, Visibility::Public(_)),
        });

        let Some((_, items)) = &node.content else {
            return;
        };
        let previous = std::mem::replace(&mut self.module_path, child_path);
        for item in items {
            self.visit_item(item);
        }
        self.module_path = previous;
    }

    fn visit_item_use(&mut self, node: &'ast ItemUse) {
        if matches!(node.vis, Visibility::Public(_)) {
            let mut expanded = Vec::new();
            flatten_use_tree(&node.tree, Vec::new(), &mut expanded);
            self.public_uses
                .extend(expanded.into_iter().map(|(path, glob)| PublicUse {
                    crate_name: self.crate_name.clone(),
                    module_path: self.module_path.clone(),
                    path,
                    glob,
                }));
        }
    }
}

fn flatten_use_tree(
    tree: &UseTree,
    mut prefix: Vec<String>,
    output: &mut Vec<(Vec<String>, bool)>,
) {
    match tree {
        UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            flatten_use_tree(&path.tree, prefix, output);
        }
        UseTree::Name(name) => {
            prefix.push(name.ident.to_string());
            output.push((prefix, false));
        }
        UseTree::Rename(rename) => {
            prefix.push(rename.ident.to_string());
            output.push((prefix, false));
        }
        UseTree::Glob(_) => output.push((prefix, true)),
        UseTree::Group(group) => {
            for item in &group.items {
                flatten_use_tree(item, prefix.clone(), output);
            }
        }
    }
}

fn resolve_use_path(current_module: &str, path: &[String]) -> Vec<String> {
    let mut index = 0;
    let mut resolved = if path.first().is_some_and(|segment| segment == "self") {
        index = 1;
        split_module_path(current_module)
    } else if path.first().is_some_and(|segment| segment == "super") {
        let mut base = split_module_path(current_module);
        while path.get(index).is_some_and(|segment| segment == "super") {
            base.pop();
            index += 1;
        }
        base
    } else {
        if path.first().is_some_and(|segment| segment == "crate") {
            index = 1;
        }
        Vec::new()
    };
    resolved.extend(path[index..].iter().cloned());
    resolved
}

fn split_module_path(path: &str) -> Vec<String> {
    path.split("::")
        .filter(|segment| !segment.is_empty())
        .map(ToOwned::to_owned)
        .collect()
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
        if !attr.path().is_ident("cfg") {
            return false;
        }
        let compact = attr
            .meta
            .to_token_stream()
            .to_string()
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect::<String>();
        compact == "cfg(test)"
            || (compact.starts_with("cfg(all(")
                && compact
                    .trim_start_matches("cfg(all(")
                    .trim_end_matches("))")
                    .split(',')
                    .any(|term| term == "test"))
    })
}

use quote::ToTokens;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolves_relative_reexport_paths() {
        assert_eq!(
            resolve_use_path("api::nested", &["super".into(), "State".into()]),
            ["api", "State"]
        );
        assert_eq!(
            resolve_use_path("api", &["crate".into(), "internal".into(), "State".into()]),
            ["internal", "State"]
        );
    }
}
