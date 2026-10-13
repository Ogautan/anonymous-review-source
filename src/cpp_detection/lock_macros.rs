//! A bounded source view for scalar pthread mutex wrappers. It is used only
//! for locksets, never for ordinary access extraction or source identities.
//! Definitions and dominating include/conditional scopes bind the effects;
//! macro spelling alone cannot establish protection.
use super::*;

#[derive(Clone)]
enum Effect {
    Acquire(String),
    Release(String),
    Declare(String),
    StaticQualifier,
}

struct Definition {
    file: String,
    available: std::ops::Range<usize>,
    effect: Effect,
}

/// A declaration/include dominates only the remainder of its own source
/// preprocessor branch. Unlike picking a build configuration, this also works
/// when the branch condition is unknown but the use is inside that branch.
pub(super) fn branch_range(node: tree_sitter::Node<'_>) -> std::ops::Range<usize> {
    let start = node.end_byte();
    let mut end = usize::MAX;
    let mut child = node;
    while let Some(parent) = child.parent() {
        if matches!(
            parent.kind(),
            "preproc_if" | "preproc_ifdef" | "preproc_elif" | "preproc_else"
        ) {
            end = end.min(parent.end_byte());
            if let Some(other) = parent.child_by_field_name("alternative")
                && other != child
                && other.start_byte() > node.start_byte()
            {
                end = end.min(other.start_byte());
            }
        }
        child = parent;
    }
    start..end
}

fn unconditional(node: tree_sitter::Node<'_>) -> bool {
    let mut parent = node.parent();
    while let Some(scope) = parent {
        if matches!(
            scope.kind(),
            "preproc_if" | "preproc_ifdef" | "preproc_elif" | "preproc_else"
        ) {
            return false;
        }
        parent = scope.parent();
    }
    true
}

fn default_static(node: tree_sitter::Node<'_>, file: &ParsedCppFile, name: &str) -> bool {
    let Some(parent) = node.parent().filter(|p| p.kind() == "preproc_ifdef") else {
        return false;
    };
    parent.child_by_field_name("alternative").is_none()
        && node_text(parent, &file.source)
            .trim_start()
            .starts_with("#ifndef")
        && parent
            .child_by_field_name("name")
            .is_some_and(|n| node_text(n, &file.source) == name)
        && unconditional(parent)
}

pub(super) fn views(
    files: &[ParsedCppFile],
    commands: &[super::super::types::CppCompileCommand],
) -> HashMap<String, ParsedCppFile> {
    let operation = Regex::new(
        r"^pthread_mutex_(lock|unlock)\s*\(\s*&\s*([A-Za-z_]\w*)(?:\s*##\s*([A-Za-z_]\w*))?\s*\)$",
    )
    .unwrap();
    let declaration = Regex::new(r"^pthread_mutex_t\s+([A-Za-z_]\w*)(?:\s*##\s*([A-Za-z_]\w*))?\s*=\s*PTHREAD_MUTEX_INITIALIZER$").unwrap();
    let mut counts = HashMap::<String, usize>::new();
    let mut definitions = HashMap::new();
    let mut blocked = HashSet::new();
    let mut lock_related = HashSet::new();
    let mut macro_words = HashMap::<String, HashSet<String>>::new();
    for file in files {
        let Some(tree) = &file.tree else {
            continue;
        };
        walk_nodes(tree.root_node(), &mut |node| {
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
            let Some(value) = node.child_by_field_name("value") else {
                return;
            };
            let value = node_text(value, &file.source)
                .trim()
                .trim_end_matches(';')
                .trim();
            macro_words
                .entry(name.clone())
                .or_default()
                .extend(identifier_tokens(value).map(str::to_owned));
            if value.contains("pthread_mutex_lock") || value.contains("pthread_mutex_unlock") {
                lock_related.insert(name.clone());
            }
            let effect = if node.kind() == "preproc_def" {
                if value != "static" || !(unconditional(node) || default_static(node, file, &name))
                {
                    return;
                }
                Effect::StaticQualifier
            } else {
                if !unconditional(node) {
                    return;
                }
                let Some(parameters) = node.child_by_field_name("parameters") else {
                    return;
                };
                let parameters = node_text(parameters, &file.source)
                    .trim_matches(['(', ')'])
                    .trim();
                if parameters.is_empty() || !parameters.bytes().all(is_ident_continue) {
                    return;
                }
                if let Some(c) = operation.captures(value) {
                    if &c[2] != parameters {
                        return;
                    }
                    let suffix = c.get(3).map_or("", |s| s.as_str()).to_string();
                    if &c[1] == "lock" {
                        Effect::Acquire(suffix)
                    } else {
                        Effect::Release(suffix)
                    }
                } else if let Some(c) = declaration.captures(value) {
                    if &c[1] != parameters {
                        return;
                    }
                    Effect::Declare(c.get(2).map_or("", |s| s.as_str()).to_string())
                } else {
                    return;
                }
            };
            // The supported #ifndef NAME / #define NAME static default has
            // one project definition and no undef; it applies after the guard.
            let available =
                if matches!(effect, Effect::StaticQualifier) && default_static(node, file, &name) {
                    node.end_byte()..usize::MAX
                } else {
                    branch_range(node)
                };
            definitions.insert(
                name,
                Definition {
                    file: file.path.clone(),
                    available,
                    effect,
                },
            );
        });
    }
    // An unsupported wrapper around an unlock is still a possible release.
    // Never expand an acquire while silently ignoring that known effect.
    loop {
        let additions = macro_words
            .iter()
            .filter(|(name, words)| {
                !lock_related.contains(*name)
                    && words.iter().any(|word| lock_related.contains(word))
            })
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        if additions.is_empty() {
            break;
        }
        lock_related.extend(additions);
    }
    if [
        "pthread_mutex_lock",
        "pthread_mutex_unlock",
        "pthread_mutex_t",
        "PTHREAD_MUTEX_INITIALIZER",
        "static",
    ]
    .iter()
    .any(|name| counts.contains_key(*name))
    {
        return HashMap::new();
    }
    definitions.retain(|name, _| counts.get(name) == Some(&1) && !blocked.contains(name));
    let paths = files
        .iter()
        .map(|f| (Path::new(&f.path), f))
        .collect::<HashMap<_, _>>();
    let mut result = HashMap::new();
    for file in files {
        let Some(tree) = &file.tree else {
            continue;
        };
        let mut overrides = HashSet::new();
        let mut opaque_build = false;
        for command in commands.iter().filter(|c| c.file == file.path) {
            let mut arguments = command.arguments.iter();
            while let Some(arg) = arguments.next() {
                if arg.starts_with('@')
                    || arg.starts_with("-include")
                    || arg.starts_with("-imacros")
                    || arg.starts_with("/FI")
                {
                    opaque_build = true;
                }
                let value = if matches!(arg.as_str(), "-D" | "-U" | "/D" | "/U") {
                    arguments.next().map(String::as_str)
                } else {
                    ["-D", "-U", "/D", "/U"]
                        .iter()
                        .find_map(|prefix| arg.strip_prefix(prefix))
                };
                if let Some(value) = value {
                    overrides.insert(value.split(['=', '(']).next().unwrap_or(value).to_string());
                }
            }
        }
        if opaque_build
            || [
                "pthread_mutex_lock",
                "pthread_mutex_unlock",
                "pthread_mutex_t",
                "PTHREAD_MUTEX_INITIALIZER",
                "static",
            ]
            .iter()
            .any(|name| overrides.contains(*name))
        {
            continue;
        }
        let mut includes = Vec::new();
        walk_nodes(tree.root_node(), &mut |node| {
            if node.kind() != "preproc_include" {
                return;
            }
            let Some(path) = node.child_by_field_name("path") else {
                return;
            };
            let path = node_text(path, &file.source);
            let Some(path) = path.strip_prefix('"').and_then(|p| p.strip_suffix('"')) else {
                return;
            };
            let Some(parent) = Path::new(&file.path).parent() else {
                return;
            };
            let joined = parent.join(path);
            if let Some(included) = paths.get(joined.as_path()) {
                includes.push((included.path.as_str(), branch_range(node)));
            }
        });
        let visible = |definition: &Definition, at: usize| {
            if definition.file == file.path {
                definition.available.contains(&at)
            } else {
                definition.available.end == usize::MAX
                    && includes
                        .iter()
                        .any(|(p, range)| *p == definition.file && range.contains(&at))
            }
        };
        let mut edits = Vec::new();
        let mut opaque_calls = Vec::new();
        let mut macro_guards = HashSet::new();
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(node.kind(), "call_expression" | "function_declarator") {
                return;
            }
            let (Some(name), Some(arguments)) = (
                node.child_by_field_name(if node.kind() == "call_expression" {
                    "function"
                } else {
                    "declarator"
                }),
                node.child_by_field_name(if node.kind() == "call_expression" {
                    "arguments"
                } else {
                    "parameters"
                }),
            ) else {
                return;
            };
            if !matches!(name.kind(), "identifier" | "field_identifier") {
                return;
            }
            let spelling = node_text(name, &file.source);
            let Some(definition) = definitions
                .get(spelling)
                .filter(|d| !overrides.contains(spelling) && visible(d, node.start_byte()))
            else {
                if lock_related.contains(spelling) && node.kind() == "call_expression" {
                    opaque_calls.push((
                        node.start_byte(),
                        node.end_byte(),
                        node_text(node, &file.source)
                            .bytes()
                            .filter(|b| *b == b'\n')
                            .count(),
                    ));
                }
                return;
            };
            let arg = node_text(arguments, &file.source)
                .trim_matches(['(', ')'])
                .trim();
            if arg.is_empty()
                || !arg.bytes().all(is_ident_continue)
                || node.start_position().row != node.end_position().row
            {
                return;
            }
            let mut start = node.start_byte();
            let replacement = match &definition.effect {
                Effect::Acquire(suffix) => {
                    macro_guards.insert(format!("{arg}{suffix}"));
                    format!("pthread_mutex_lock(&{arg}{suffix})")
                }
                Effect::Release(suffix) => format!("pthread_mutex_unlock(&{arg}{suffix})"),
                Effect::Declare(suffix) => {
                    // Recognize a full declaration, not a macro call used in
                    // an expression or a member/function-pointer declarator.
                    let line_start = file.source[..start].rfind('\n').map_or(0, |i| i + 1);
                    let prefix = file.source[line_start..start].trim();
                    let qualifier = if prefix.is_empty() {
                        ""
                    } else if prefix == "static"
                        || (!overrides.contains(prefix)
                            && definitions.get(prefix).is_some_and(|d| {
                                matches!(d.effect, Effect::StaticQualifier) && visible(d, start)
                            }))
                    {
                        "static "
                    } else {
                        return;
                    };
                    macro_guards.insert(format!("{arg}{suffix}"));
                    start = line_start;
                    format!("{qualifier}pthread_mutex_t {arg}{suffix} = PTHREAD_MUTEX_INITIALIZER")
                }
                Effect::StaticQualifier => return,
            };
            edits.push((start, node.end_byte(), replacement));
        });
        // Opaque source-known mutex macros kill newly recovered must-held
        // facts at their call site. An unrelated logging macro elsewhere in
        // the file must not erase a proof in this function. These synthetic
        // releases exist only in the lock-analysis view, never in accesses.
        let mut guards = macro_guards.into_iter().collect::<Vec<_>>();
        guards.sort();
        if !guards.is_empty() {
            let kill = format!(
                "({})",
                guards
                    .iter()
                    .map(|g| format!("pthread_mutex_unlock(&{g})"))
                    .collect::<Vec<_>>()
                    .join(",")
            );
            for (start, end, newlines) in opaque_calls {
                edits.push((start, end, format!("{kill}{}", "\n".repeat(newlines))));
            }
        }
        edits.sort_by_key(|(start, _, _)| *start);
        edits.dedup_by_key(|(start, end, _)| (*start, *end));
        if edits.is_empty() || edits.windows(2).any(|pair| pair[0].1 > pair[1].0) {
            continue;
        }
        if let Some(view) = file.reparse_with_edits(&edits) {
            result.insert(file.path.clone(), view);
        }
    }
    result
}
