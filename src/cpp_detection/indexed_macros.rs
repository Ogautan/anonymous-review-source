//! Source-backed effects of simple function-like synchronization macros.
//! Names do not establish effects; only a visible, unique replacement body
//! invoking a modelled primitive does. No general preprocessor emulation.

use super::*;

struct Effect {
    file: String,
    line: usize,
    definition_line: usize,
    primitive: String,
    parameter: usize,
    arity: usize,
    suffix: String,
}

pub(super) struct Target {
    pub(super) storage: String,
    pub(super) index: String,
    pub(super) evidence: String,
}

#[derive(Default)]
pub(super) struct Effects {
    definitions: HashMap<String, Effect>,
    includes: HashMap<String, Vec<(String, usize)>>,
    #[allow(clippy::type_complexity)]
    calls: HashMap<String, HashMap<usize, Vec<(String, Vec<String>)>>>,
}

fn unconditional(mut node: tree_sitter::Node<'_>) -> bool {
    while let Some(parent) = node.parent() {
        if matches!(
            parent.kind(),
            "preproc_if" | "preproc_ifdef" | "preproc_else" | "preproc_elif"
        ) {
            return false;
        }
        node = parent;
    }
    true
}

fn rmw_primitive(name: &str) -> bool {
    matches!(
        name,
        "pthread_mutex_lock"
            | "pthread_mutex_unlock"
            | "pthread_spin_lock"
            | "pthread_spin_unlock"
            | "mtx_lock"
            | "mtx_unlock"
            | "__sync_add_and_fetch"
            | "__sync_fetch_and_add"
            | "__sync_sub_and_fetch"
            | "__sync_fetch_and_sub"
            | "__atomic_fetch_add"
            | "__atomic_fetch_sub"
            | "__atomic_add_fetch"
            | "__atomic_sub_fetch"
            | "atomic_fetch_add"
            | "atomic_fetch_sub"
            | "atomic_fetch_add_explicit"
            | "atomic_fetch_sub_explicit"
    )
}

pub(super) fn collect(files: &[ParsedCppFile]) -> Effects {
    let mut result = Effects::default();
    let mut counts = HashMap::<String, usize>::new();
    let mut blocked = HashSet::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() == "preproc_include"
                && unconditional(node)
                && let Some(path) = node.child_by_field_name("path")
            {
                let path = node_text(path, &file.source);
                if let Some(relative) = path.strip_prefix('"').and_then(|p| p.strip_suffix('"'))
                    && let Some(parent) = Path::new(&file.path).parent()
                {
                    // No guessed include search paths or basename matching.
                    let target = parent.join(relative);
                    if let Some(target) = files.iter().find(|f| Path::new(&f.path) == target) {
                        result
                            .includes
                            .entry(file.path.clone())
                            .or_default()
                            .push((target.path.clone(), node.end_position().row + 1));
                    }
                }
            }
            if node.kind() == "preproc_call"
                && node_text(node, &file.source)
                    .trim_start()
                    .starts_with("#undef")
            {
                blocked.extend(
                    identifier_tokens(node_text(node, &file.source))
                        .skip(1)
                        .map(str::to_owned),
                );
            }
            if !matches!(node.kind(), "preproc_def" | "preproc_function_def") {
                return;
            }
            let Some(name) = node.child_by_field_name("name") else {
                return;
            };
            let name = node_text(name, &file.source).to_owned();
            *counts.entry(name.clone()).or_default() += 1;
            if node.kind() != "preproc_function_def" || !unconditional(node) {
                return;
            }
            let (Some(parameters), Some(value)) = (
                node.child_by_field_name("parameters"),
                node.child_by_field_name("value"),
            ) else {
                return;
            };
            let parameter_text = node_text(parameters, &file.source);
            if parameter_text.contains("...") {
                return;
            }
            let parameters = identifier_tokens(parameter_text).collect::<Vec<_>>();
            let body = node_text(value, &file.source)
                .trim()
                .trim_end_matches(';')
                .trim();
            let Some(open) = body.find('(') else { return };
            let callee = body[..open].trim();
            if !rmw_primitive(callee) || !body.ends_with(')') {
                return;
            }
            let calls = call_argument_lists(body, callee);
            let [args] = calls.as_slice() else { return };
            let Some(target) = args.first() else { return };
            let compact = target
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>();
            let compact = compact.trim_start_matches('&').trim_matches(['(', ')']);
            let (parameter, suffix) = compact.split_once("##").unwrap_or((compact, ""));
            if !suffix.is_empty() && !suffix.bytes().all(is_ident_continue) {
                return;
            }
            let Some(parameter) = parameters.iter().position(|p| *p == parameter) else {
                return;
            };
            result.definitions.insert(
                name,
                Effect {
                    file: file.path.clone(),
                    line: node.end_position().row + 1,
                    definition_line: node.start_position().row + 1,
                    primitive: callee.to_owned(),
                    parameter,
                    arity: parameters.len(),
                    suffix: suffix.to_owned(),
                },
            );
        });
    }
    result
        .definitions
        .retain(|name, _| counts.get(name) == Some(&1) && !blocked.contains(name));
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "call_expression" {
                return;
            }
            let (Some(callee), Some(arguments)) = (
                node.child_by_field_name("function"),
                node.child_by_field_name("arguments"),
            ) else {
                return;
            };
            if callee.kind() != "identifier" {
                return;
            }
            let name = node_text(callee, &file.source);
            if !result.definitions.contains_key(name) {
                return;
            }
            let arguments = arguments
                .named_children(&mut arguments.walk())
                .filter(|arg| arg.kind() != "comment")
                .map(|arg| node_text(arg, &file.source).to_owned())
                .collect();
            result
                .calls
                .entry(file.path.clone())
                .or_default()
                .entry(node.start_position().row + 1)
                .or_default()
                .push((name.to_owned(), arguments));
        });
    }
    result
}

impl Effects {
    pub(super) fn targets(&self, file: &ParsedCppFile, line: usize, _source: &str) -> Vec<Target> {
        let mut targets = Vec::new();
        let Some(calls) = self
            .calls
            .get(&file.path)
            .and_then(|lines| lines.get(&line))
        else {
            return targets;
        };
        for (name, arguments) in calls {
            let Some(effect) = self.definitions.get(name) else {
                continue;
            };
            let visible = (effect.file == file.path && effect.line < line)
                || self.includes.get(&file.path).is_some_and(|includes| {
                    includes
                        .iter()
                        .any(|(path, at)| *path == effect.file && *at < line)
                });
            if !visible {
                continue;
            }
            {
                if arguments.len() != effect.arity {
                    continue;
                }
                let argument = arguments[effect.parameter].trim();
                // Concatenation changes the final token. Only a member suffix
                // following the index can preserve the indexed storage name.
                if !effect.suffix.is_empty()
                    && !argument.rsplit_once(']').is_some_and(|(_, tail)| {
                        let tail = tail.trim();
                        tail.starts_with('.') && tail[1..].bytes().all(is_ident_continue)
                    })
                {
                    continue;
                }
                let target = format!("{argument}{}", effect.suffix);
                let Some((prefix, _)) = target.split_once('[') else {
                    continue;
                };
                // A member with the same spelling does not bind a global
                // array (e.g. batch->counters[index] versus counters[index]).
                if prefix.contains(['.', ':', '*'])
                    || prefix.contains("->")
                    || identifier_tokens(prefix).count() != 1
                {
                    continue;
                }
                // A pointee lock is not an embedded lock in the pointer array;
                // nested index arrays are only reads, not mutation targets.
                if target
                    .split_once(']')
                    .is_some_and(|(_, tail)| tail.trim_start().starts_with("->"))
                {
                    continue;
                }
                if let Some((symbol, index)) = indexed_accesses(&target).into_iter().next()
                    && identifier_tokens(&index).next().is_some()
                {
                    targets.push(Target {
                        evidence: format!(
                            "宏写证据: {name} 在 {}:{} 的定义调用 {}；实参绑定目标 {target}",
                            effect.file, effect.definition_line, effect.primitive
                        ),
                        storage: symbol,
                        index,
                    });
                }
            }
        }
        targets
    }
}
