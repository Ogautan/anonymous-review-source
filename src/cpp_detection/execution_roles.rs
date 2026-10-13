//! Bounded member-call entry points for default same-object reportability.
//! Names are resolved within a bound record. Unresolved/overloaded/escaping
//! methods retain their own possible entry; they are never declared safe.
use super::super::types::{CppMethodRole, CppRecordKind};
use super::*;
use crate::cpp_detection::parser::CodeChildren;
use tree_sitter::Node;

#[derive(Default)]
pub(super) struct Builder {
    methods: Vec<Method>,
    declarations: HashMap<(usize, String), bool>, // true = definitely private
    escaped_names: HashSet<String>,
    // A resolved self-call opens only this owner's method graph. Its spelling
    // must not invent entry points in unrelated records with the same helper.
    escaped_methods: HashSet<(usize, String)>,
    open_records: HashSet<usize>,
    access_control_opaque: bool,
}

struct Method {
    owner: usize,
    name: String,
    function: String,
    file: String,
    line: usize,
    offset: usize,
    lifecycle: bool,
    opaque: bool,
    conditional: bool,
    calls: HashSet<String>,
    conditional_calls: HashSet<String>,
    call_guards: HashMap<String, HashSet<String>>,
    preserves_entry_locks: bool,
    accesses: Vec<(usize, String)>,
}

impl Builder {
    pub(super) fn collect_file(
        &mut self,
        file: &ParsedCppFile,
        index: &EvidenceIndex<'_>,
        syntax: &HashMap<usize, Vec<field_access::SyntaxAccess>>,
        locksets: &HashMap<usize, Vec<String>>,
    ) {
        let Some(tree) = &file.tree else { return };
        let mut lexical_bindings = collect_lexical_binding_ranges(file);
        let mut local_bindings = HashMap::new();
        let mut local_value_bindings = HashMap::new();
        let mut macro_bindings = HashSet::new();
        // The general object-binding helper deliberately skips function
        // declarators. Here a local callable/function-pointer declaration is
        // precisely a shadow that must prevent a member-call edge.
        walk_nodes(tree.root_node(), &mut |node| {
            if matches!(node.kind(), "preproc_def" | "preproc_function_def")
                && let Some(name) = node.child_by_field_name("name")
            {
                macro_bindings.insert(node_text(name, &file.source).to_owned());
                self.access_control_opaque |= matches!(
                    node_text(name, &file.source),
                    "private" | "protected" | "public"
                );
            }
            if !matches!(
                node.kind(),
                "declaration" | "parameter_declaration" | "optional_parameter_declaration"
            ) {
                return;
            }
            let mut parent = node.parent();
            let mut local = false;
            while let Some(p) = parent {
                if p.kind() == "function_definition" {
                    local = true;
                    break;
                }
                parent = p.parent();
            }
            if !local {
                return;
            }
            for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
                let mut current = declarator;
                loop {
                    if matches!(current.kind(), "identifier" | "field_identifier") {
                        let scope = field_access::binding_scope(node);
                        lexical_bindings
                            .entry(node_text(current, &file.source).into())
                            .or_default()
                            .push((node.start_byte(), scope.start_byte(), scope.end_byte()));
                        if !node.has_error() && !declarator.has_error() {
                            local_bindings
                                .entry(node_text(current, &file.source).to_owned())
                                .or_insert_with(Vec::new)
                                .push((node.start_byte(), scope.start_byte(), scope.end_byte()));
                            let plain = declarator
                                .child_by_field_name("declarator")
                                .filter(|_| declarator.kind() == "init_declarator")
                                .unwrap_or(declarator);
                            if plain.kind() == "identifier"
                                && node.child_by_field_name("type").is_some_and(|ty| {
                                    matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                                })
                            {
                                local_value_bindings
                                    .entry(node_text(current, &file.source).to_owned())
                                    .or_insert_with(Vec::new)
                                    .push((
                                        node.start_byte(),
                                        scope.start_byte(),
                                        scope.end_byte(),
                                    ));
                            }
                        }
                        break;
                    }
                    if let Some(inner) = current.child_by_field_name("declarator") {
                        current = inner;
                    } else if matches!(
                        current.kind(),
                        "parenthesized_declarator" | "reference_declarator"
                    ) && current.named_code_child_count() == 1
                    {
                        current = current.named_code_child(0).unwrap();
                    } else {
                        break;
                    }
                }
            }
        });
        local_bindings.retain(|name, _| !macro_bindings.contains(name));
        local_value_bindings.retain(|name, _| !macro_bindings.contains(name));
        walk_nodes(tree.root_node(), &mut |node| {
            if inside_decltype(node) {
                return;
            }
            if matches!(node.kind(), "identifier" | "qualified_identifier")
                && node.parent().is_some_and(|p| p.kind() == "argument_list")
                && !(node.kind() == "identifier"
                    && receiver_is_lexically_bound(node, node, &file.source, &local_bindings))
            {
                // Static member functions can escape without an explicit '&'.
                self.escaped_names
                    .extend(identifier_tokens(node_text(node, &file.source)).map(str::to_owned));
            }
            // Initializer-list callbacks are outside the compound body too.
            if node.kind() == "call_expression"
                && inside_lambda(node, tree.root_node())
                && let Some(callee) = node.child_by_field_name("function")
            {
                self.record_call_escape(callee, file, index);
            }
            // An explicit object call may come from a friend, a callback or
            // another receiver. It prevents closing that method's call graph.
            if node.kind() == "field_expression"
                && node.parent().is_some_and(|p| p.kind() == "call_expression")
                && node
                    .child_by_field_name("argument")
                    .is_some_and(|a| !is_self_receiver(a))
                && let Some(name) = node.child_by_field_name("field")
            {
                self.record_call_escape(name, file, index);
            }
            if node.kind() == "pointer_expression"
                && node_text(node, &file.source).trim_start().starts_with('&')
            {
                let mut argument = node.child_by_field_name("argument");
                while argument.is_some_and(|arg| arg.kind() == "parenthesized_expression") {
                    argument = argument.and_then(|arg| arg.named_code_child(0));
                }
                // The address of a lexically bound local/parameter cannot be
                // a same-spelled member function. Preserve qualified member
                // addresses and unresolved expressions conservatively.
                if !argument.is_some_and(|arg| {
                    arg.kind() == "identifier"
                        && receiver_is_lexically_bound(node, arg, &file.source, &local_bindings)
                }) {
                    self.escaped_names.extend(
                        identifier_tokens(node_text(node, &file.source)).map(str::to_owned),
                    );
                }
            }
            if matches!(node.kind(), "preproc_def" | "preproc_function_def") {
                self.escaped_names
                    .extend(identifier_tokens(node_text(node, &file.source)).map(str::to_owned));
            }
            if matches!(node.kind(), "class_specifier" | "struct_specifier") {
                self.collect_declarations(node, file, index);
            }
            if node.kind() != "function_definition" {
                return;
            }
            let (Some(owner), Some(name), Some(body)) = (
                field_access::function_owner(node, file, index),
                function_definition_name(node, file),
                node.child_by_field_name("body"),
            ) else {
                return;
            };
            let name = name.rsplit("::").next().unwrap_or(&name).to_owned();
            let signature = &file.source[node.start_byte()..body.start_byte()];
            let lifecycle = signature.split('(').next().is_some_and(|s| s.contains('~'))
                || is_record_constructor(&name, index.record(owner));
            // The presentation parser strips '~' and overload signatures.
            // Lifecycle bodies have distinct source identities; neither a
            // constructor overload nor a destructor is a runtime entry just
            // because its displayed name collides with another constructor.
            let function = name.clone();
            let name = if lifecycle {
                format!("{name}#lifecycle@{}:{}", file.path, node.start_byte())
            } else {
                name
            };
            let mut calls = HashSet::new();
            let mut conditional_calls = HashSet::new();
            let mut call_guards: HashMap<String, HashSet<String>> = HashMap::new();
            let mut lambdas = Vec::new();
            let mut conditional_exit = false;
            walk_nodes(body, &mut |child| {
                if inside_decltype(child) {
                    return;
                }
                if child.kind() == "lambda_expression" {
                    lambdas.push(child.byte_range());
                }
                if matches!(
                    child.kind(),
                    "return_statement" | "throw_statement" | "goto_statement"
                ) && conditionally_called(child, body)
                {
                    conditional_exit = true;
                }
                if child.kind() != "call_expression" {
                    return;
                }
                let Some(callee) = child.child_by_field_name("function") else {
                    return;
                };
                if callee.kind() == "identifier"
                    && receiver_is_lexically_bound(child, callee, &file.source, &lexical_bindings)
                {
                    return;
                }
                let name = match callee.kind() {
                    "identifier" => Some(node_text(callee, &file.source)),
                    "qualified_identifier" => {
                        let text = node_text(callee, &file.source);
                        text.rsplit_once("::").and_then(|(scope, name)| {
                            let record = index.record(owner);
                            (scope == record.name
                                || scope == record.qualified_name
                                || scope.trim_start_matches("::") == record.qualified_name)
                                .then_some(name)
                        })
                    }
                    "field_expression"
                        if callee
                            .child_by_field_name("argument")
                            .is_some_and(is_self_receiver) =>
                    {
                        callee
                            .child_by_field_name("field")
                            .map(|n| node_text(n, &file.source))
                    }
                    _ => None,
                };
                if let Some(name) = name {
                    if inside_lambda(child, body) {
                        // Even a synchronous callback is left open here; the
                        // dedicated callback frontend can refine concurrency.
                        self.escaped_methods.insert((owner, name.into()));
                    } else {
                        calls.insert(name.into());
                        if !lifecycle && conditionally_called(child, body) {
                            conditional_calls.insert(name.into());
                        }
                        let guards = locksets
                            .get(&(child.start_position().row + 1))
                            .into_iter()
                            .flatten()
                            // Caller locals/parameters do not identify the same
                            // guard in a different method's lexical scope.
                            .filter(|guard| {
                                identifier_tokens(guard).collect::<Vec<_>>() == [guard.as_str()]
                                    && !macro_bindings.contains(guard.as_str())
                                    && !local_bindings.get(guard.as_str()).is_some_and(|ranges| {
                                        ranges.iter().any(|(declaration, begin, end)| {
                                            *declaration <= child.start_byte()
                                                && *begin <= child.start_byte()
                                                && child.start_byte() < *end
                                        })
                                    })
                            })
                            .cloned()
                            .collect::<HashSet<_>>();
                        call_guards
                            .entry(name.into())
                            .and_modify(|held| held.retain(|guard| guards.contains(guard)))
                            .or_insert(guards);
                    }
                } else {
                    // A templated/indirect/otherwise unresolved callee must
                    // not make a potentially referenced helper unreachable.
                    self.record_call_escape(callee, file, index);
                }
            });
            if conditional_exit && !lifecycle {
                // Calls after a guarded return are control-dependent too,
                // even though they are siblings rather than children of if.
                conditional_calls.extend(calls.iter().cloned());
            }
            let mut accesses = Vec::new();
            for line in body.start_position().row + 1..=body.end_position().row + 1 {
                let Some(items) = syntax.get(&line) else {
                    continue;
                };
                for access in items {
                    if access.record != owner
                        || access.start_byte < body.start_byte()
                        || access.start_byte >= body.end_byte()
                        || access.contiguous_element
                        || access.receiver.as_deref().is_some_and(|r| r != "this")
                        || lambdas.iter().any(|r| r.contains(&access.start_byte))
                        // Same-line accesses to another object cannot inherit
                        // this object's lifecycle or callable entry point.
                        || items.iter().any(|other| other.record == owner
                            && other.field == access.field
                            && other.receiver.as_deref().is_some_and(|r| r != "this"))
                    {
                        continue;
                    }
                    let key = (line, access.field.clone());
                    if !accesses.contains(&key) {
                        accesses.push(key);
                    }
                }
            }
            self.methods.push(Method {
                owner,
                name,
                function,
                file: file.path.clone(),
                line: node.start_position().row + 1,
                offset: node.start_byte(),
                lifecycle,
                opaque: body.has_error()
                    || !lambdas.is_empty()
                    || receiver_may_escape(
                        body,
                        &file.source,
                        &local_bindings,
                        &local_value_bindings,
                    )
                    || signature.contains("virtual")
                    || signature.contains("override")
                    || index.record(owner).has_base_classes
                    || (lifecycle
                        && (!lambdas.is_empty()
                            || signature.contains("this")
                            || signature.contains('[')
                            || receiver_may_escape(
                                body,
                                &file.source,
                                &local_bindings,
                                &local_value_bindings,
                            ))),
                calls,
                conditional: !lifecycle && conditional_exit,
                conditional_calls,
                call_guards,
                preserves_entry_locks: preserves_entry_locks(node, body, file, index, owner)
                    && !identifier_tokens(node_text(node, &file.source))
                        .any(|token| macro_bindings.contains(token)),
                accesses,
            });
        });
    }

    // A call expression does not grant access to every same-spelled private
    // method in the project. Only its lexical class (including enclosing
    // classes) can directly call those private methods. Friend-bearing records
    // are already open; unresolved qualified/template calls and parse recovery
    // retain the global fallback. Actual method-address escapes remain global.
    fn record_call_escape(
        &mut self,
        callee: Node<'_>,
        file: &ParsedCppFile,
        index: &EvidenceIndex<'_>,
    ) {
        let mut owners = HashSet::new();
        let mut unresolved = !matches!(
            callee.kind(),
            "identifier" | "field_identifier" | "field_expression"
        );
        let mut current = Some(callee);
        while let Some(node) = current {
            unresolved |= node.kind() == "ERROR" || node.is_missing();
            if node.kind() == "function_definition" {
                if let Some(owner) = field_access::function_owner(node, file, index) {
                    owners.insert(owner);
                    // An out-of-line nested method has no lexical class AST
                    // ancestors here, but retains access to its enclosing
                    // classes' private members.
                    let mut scope = index.record(owner).qualified_name.as_str();
                    while let Some((parent, _)) = scope.rsplit_once("::") {
                        let name = parent.rsplit("::").next().unwrap_or(parent);
                        owners.extend(
                            index
                                .record_indices_for_name(name)
                                .into_iter()
                                .flatten()
                                .copied()
                                .filter(|&candidate| {
                                    index.record(candidate).qualified_name == parent
                                }),
                        );
                        scope = parent;
                    }
                } else if node.child_by_field_name("declarator").is_some_and(|decl| {
                    node_text(decl, &file.source)
                        .split('(')
                        .next()
                        .is_some_and(|name| name.contains("::"))
                }) {
                    unresolved = true;
                }
            }
            if matches!(node.kind(), "class_specifier" | "struct_specifier") {
                let candidates = node
                    .child_by_field_name("name")
                    .and_then(|name| index.record_indices_for_name(node_text(name, &file.source)))
                    .into_iter()
                    .flatten()
                    .copied()
                    .filter(|&i| {
                        index.record(i).file == file.path
                            && index.record(i).line == node.start_position().row + 1
                    })
                    .collect::<Vec<_>>();
                if candidates.len() == 1 {
                    owners.insert(candidates[0]);
                } else if candidates.len() > 1 || node.has_error() {
                    unresolved = true;
                }
            }
            current = node.parent();
        }
        let names = identifier_tokens(node_text(callee, &file.source));
        for name in names {
            if unresolved {
                self.escaped_names.insert(name.into());
            } else {
                self.escaped_methods
                    .extend(owners.iter().map(|&owner| (owner, name.into())));
            }
        }
    }

    fn collect_declarations(
        &mut self,
        node: Node<'_>,
        file: &ParsedCppFile,
        index: &EvidenceIndex<'_>,
    ) {
        let Some(body) = node.child_by_field_name("body") else {
            return;
        };
        let Some(name) = node.child_by_field_name("name") else {
            return;
        };
        let Some(candidates) = index.record_indices_for_name(node_text(name, &file.source)) else {
            return;
        };
        let mut matches = candidates.iter().copied().filter(|&i| {
            let record = index.record(i);
            record.file == file.path && record.line == node.start_position().row + 1
        });
        let Some(owner) = matches.next() else { return };
        if matches.next().is_some() {
            return;
        }
        let record = index.record(owner);
        if body.has_error()
            || node_text(body, &file.source)
                .split_whitespace()
                .any(|word| word == "friend")
        {
            self.open_records.insert(owner);
        }
        let mut private = record.kind == CppRecordKind::Class;
        for child in body.named_code_children(&mut body.walk()) {
            if child.kind() == "access_specifier" {
                private = node_text(child, &file.source) == "private";
                continue;
            }
            if !matches!(
                child.kind(),
                "field_declaration" | "declaration" | "function_definition"
            ) {
                continue;
            }
            let Some(name) = function_definition_name(child, file) else {
                continue;
            };
            let text = node_text(child, &file.source);
            let closed = private
                && !child.has_error()
                && !text.contains("virtual")
                && !text.contains("override")
                && !text.contains("friend");
            self.declarations
                .entry((owner, name))
                .and_modify(|p| *p &= closed)
                .or_insert(closed);
        }
    }

    pub(super) fn finish(self, records: &[CppStructInfo], evidence: &mut [CppEvidenceSet]) {
        // Visibility-rewriting macros invalidate lexical C++ access rights.
        // The source frontend does not expand them; retain unresolved roles.
        if self.access_control_opaque {
            return;
        }
        let mut by_owner: HashMap<usize, Vec<&Method>> = HashMap::new();
        for method in &self.methods {
            by_owner.entry(method.owner).or_default().push(method);
        }
        for (owner, methods) in by_owner {
            // Bounded computation: excessive/recursive expansion must remain
            // unresolved rather than silently lose paths or access roles.
            if methods.len() > 256 || self.open_records.contains(&owner) {
                continue;
            }
            let mut names: HashMap<&str, Vec<usize>> = HashMap::new();
            for (i, m) in methods.iter().enumerate() {
                names.entry(&m.name).or_default().push(i);
            }
            let mut entries = vec![HashSet::new(); methods.len()];
            for (i, m) in methods.iter().enumerate() {
                let unresolved = m.opaque
                    || names[m.name.as_str()].len() != 1
                    || (!m.lifecycle
                        && (self.escaped_names.contains(&m.name)
                            || self.escaped_methods.contains(&(owner, m.name.clone()))));
                let private = self.declarations.get(&(owner, m.name.clone())) == Some(&true);
                // A built-in scalar leaf cannot release a caller's lock or
                // invoke user code. Only closed private entry points inherit a
                // must-held lock, and every observed call must hold it.
                if !unresolved && private && m.preserves_entry_locks {
                    let mut inherited: Option<HashSet<String>> = None;
                    for caller in &methods {
                        if let Some(guards) = caller.call_guards.get(&m.name) {
                            // A bare external/static name in another file may
                            // denote a different mutex. Cross-file inheritance
                            // requires an inline member of this same receiver.
                            let guards = guards
                                .iter()
                                .filter(|guard| {
                                    caller.file == m.file
                                        || records[owner].fields.iter().any(|field| {
                                            field.name == **guard
                                                && field.is_hot_sync
                                                && !field.is_indirect
                                                && !field.is_static
                                        })
                                })
                                .cloned()
                                .collect::<HashSet<_>>();
                            match &mut inherited {
                                Some(held) => held.retain(|guard| guards.contains(guard)),
                                None => inherited = Some(guards),
                            }
                        }
                    }
                    if let Some(guards) = inherited {
                        for item in &mut evidence[owner].items {
                            if item.file == m.file
                                && item.function_name.as_deref() == Some(m.function.as_str())
                                && m.accesses.iter().any(|(line, field)| {
                                    item.line == *line && item.field_name.as_ref() == Some(field)
                                })
                            {
                                item.guard_ids.extend(guards.iter().cloned());
                                item.guard_ids.sort();
                                item.guard_ids.dedup();
                            }
                        }
                    }
                }
                if unresolved || (!m.lifecycle && !private) {
                    entries[i].insert(format!(
                        "{}::{}@{}:{}:{}",
                        records[owner].qualified_name, m.function, m.file, m.line, m.offset
                    ));
                }
            }
            let mut complete = false;
            for _ in 0..32 {
                let mut changed = false;
                for (caller, m) in methods.iter().enumerate() {
                    // Branching is not publication. A private helper reached
                    // only during construction/destruction has no runtime
                    // entry merely because it can return early. Once runtime
                    // reachable, retain independent branch roles as before.
                    if m.conditional && !entries[caller].is_empty() {
                        changed |= entries[caller].insert(format!(
                            "{}::{}@{}:{}:{}",
                            records[owner].qualified_name, m.function, m.file, m.line, m.offset
                        ));
                    }
                    for callee in &m.calls {
                        for &target in names.get(callee.as_str()).into_iter().flatten() {
                            let inherited = entries[caller].clone();
                            let before = entries[target].len();
                            if !inherited.is_empty() && m.conditional_calls.contains(callee) {
                                let target_method = methods[target];
                                entries[target].insert(format!(
                                    "{}::{}@{}:{}:{}",
                                    records[owner].qualified_name,
                                    target_method.function,
                                    target_method.file,
                                    target_method.line,
                                    target_method.offset
                                ));
                            }
                            entries[target].extend(inherited);
                            changed |= before != entries[target].len();
                        }
                    }
                }
                if !changed {
                    complete = true;
                    break;
                }
            }
            if !complete {
                continue;
            }
            for (i, method) in methods.iter().enumerate() {
                if method.opaque || names[method.name.as_str()].len() != 1 {
                    continue;
                }
                let mut roots = entries[i].iter().cloned().collect::<Vec<_>>();
                roots.sort();
                // Even a completely evicted helper may contribute fields to
                // a retained caller's runtime role. Preserve its entry map
                // for completeness checks, never as an access witness.
                for omitted in &mut evidence[owner].omitted_access_roles {
                    if omitted.file == method.file
                        && omitted.function == method.function
                        && method
                            .accesses
                            .iter()
                            .any(|(_, field)| *field == omitted.field)
                    {
                        omitted.runtime_entries = roots.clone();
                    }
                }
                for (line, field) in &method.accesses {
                    if !evidence[owner].items.iter().any(|item| {
                        item.file == method.file
                            && item.line == *line
                            && item.field_name.as_deref() == Some(field)
                            && item.function_name.as_deref() == Some(method.function.as_str())
                    }) {
                        continue;
                    }
                    evidence[owner].method_roles.push(CppMethodRole {
                        file: method.file.clone(),
                        function: method.function.clone(),
                        line: *line,
                        field: field.clone(),
                        entries: roots.clone(),
                    });
                }
            }
        }
    }
}

// A closed leaf consisting only of built-in scalar operations cannot release
// an entry lock, publish the receiver, or invoke a user conversion/destructor.
// Unknown nodes/types/calls remain outside this proof. Parameters are excluded:
// evaluating a caller argument could itself release the lock before entry.
fn preserves_entry_locks(
    node: Node<'_>,
    body: Node<'_>,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    owner: usize,
) -> bool {
    let Some(declarator) = node.child_by_field_name("declarator") else {
        return false;
    };
    if declarator.kind() != "function_declarator"
        || declarator
            .child_by_field_name("parameters")
            .is_none_or(|parameters| parameters.named_code_child_count() != 0)
        || node
            .child_by_field_name("type")
            .is_none_or(|ty| !matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
    {
        return false;
    }
    let scalar_field = |name: &str| {
        index.record(owner).fields.iter().any(|field| {
            field.name == name
                && !field.is_static
                && !field.is_array
                && !field.is_indirect
                && !field.ty_str.is_empty()
                && field.ty_str.split_whitespace().all(|token| {
                    matches!(
                        token,
                        "bool"
                            | "char"
                            | "int"
                            | "short"
                            | "long"
                            | "float"
                            | "double"
                            | "signed"
                            | "unsigned"
                            | "const"
                    )
                })
        })
    };
    let mut locals = Vec::new();
    let mut safe = true;
    walk_nodes(body, &mut |child| {
        if child.kind() != "declaration" {
            return;
        }
        if child
            .child_by_field_name("type")
            .is_none_or(|ty| !matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
        {
            safe = false;
        }
        for declaration in child.children_by_field_name("declarator", &mut child.walk()) {
            let name = if declaration.kind() == "init_declarator" {
                declaration.child_by_field_name("declarator")
            } else {
                Some(declaration)
            };
            if let Some(name) = name.filter(|name| name.kind() == "identifier") {
                let scope = field_access::binding_scope(child);
                locals.push((
                    node_text(name, &file.source),
                    child.start_byte(),
                    scope.byte_range(),
                ));
            } else {
                safe = false;
            }
        }
    });
    walk_nodes(body, &mut |child| {
        if !child.is_named() {
            return;
        }
        safe &= match child.kind() {
            "identifier" => {
                let name = node_text(child, &file.source);
                locals.iter().any(|(local, declaration, scope)| {
                    *local == name
                        && *declaration <= child.start_byte()
                        && scope.contains(&child.start_byte())
                }) || scalar_field(name)
            }
            "field_identifier" => scalar_field(node_text(child, &file.source)),
            "this" => child.parent().is_some_and(|parent| {
                parent.kind() == "field_expression"
                    && parent.child_by_field_name("argument") == Some(child)
            }),
            "field_expression" => child
                .child_by_field_name("argument")
                .is_some_and(|argument| argument.kind() == "this"),
            "compound_statement"
            | "expression_statement"
            | "return_statement"
            | "if_statement"
            | "else_clause"
            | "condition_clause"
            | "while_statement"
            | "do_statement"
            | "for_statement"
            | "break_statement"
            | "continue_statement"
            | "declaration"
            | "init_declarator"
            | "primitive_type"
            | "sized_type_specifier"
            | "type_qualifier"
            | "assignment_expression"
            | "binary_expression"
            | "unary_expression"
            | "update_expression"
            | "conditional_expression"
            | "parenthesized_expression"
            | "number_literal"
            | "char_literal"
            | "true"
            | "false"
            | "comment" => true,
            _ => false,
        };
    });
    safe
}

fn inside_lambda(mut node: Node<'_>, body: Node<'_>) -> bool {
    while let Some(parent) = node.parent() {
        if parent == body {
            return false;
        }
        if parent.kind() == "lambda_expression" {
            return true;
        }
        node = parent;
    }
    false
}

// decltype's operand supplies a type; it neither invokes a helper nor
// publishes a member-function address or the receiver at runtime.
fn inside_decltype(mut node: Node<'_>) -> bool {
    loop {
        if node.kind() == "decltype" {
            return true;
        }
        let Some(parent) = node.parent() else {
            return false;
        };
        node = parent;
    }
}

// Parentheses and dereferencing the built-in `this` pointer do not change
// receiver identity. Do not peel casts, aliases, calls or overloaded operators.
fn is_self_receiver(mut node: Node<'_>) -> bool {
    let mut dereferenced = false;
    loop {
        match node.kind() {
            "this" => return true,
            "parenthesized_expression" if node.named_code_child_count() == 1 => {
                node = node.named_code_child(0).unwrap();
            }
            "pointer_expression"
                if !dereferenced
                    && node
                        .child_by_field_name("operator")
                        .is_some_and(|op| op.kind() == "*") =>
            {
                let Some(argument) = node.child_by_field_name("argument") else {
                    return false;
                };
                dereferenced = true;
                node = argument;
            }
            _ => return false,
        }
    }
}

// A constructor/destructor can publish its receiver before completing. A this
// value used outside a direct member receiver invalidates the closed phase;
// this deliberately leaves unknown escape/registration contracts unresolved.
fn receiver_may_escape(
    body: Node<'_>,
    source: &str,
    locals: &HashMap<String, Vec<(usize, usize, usize)>>,
    local_values: &HashMap<String, Vec<(usize, usize, usize)>>,
) -> bool {
    let mut escapes = false;
    walk_nodes(body, &mut |node| {
        if inside_decltype(node) {
            return;
        }
        if node.kind() == "this" {
            let mut receiver = node;
            while let Some(parent) = receiver.parent() {
                if !is_self_receiver(parent) {
                    break;
                }
                receiver = parent;
            }
            let bound_member = receiver.parent().is_some_and(|parent| {
                parent.kind() == "field_expression"
                    && parent.child_by_field_name("argument") == Some(receiver)
            });
            escapes |= !bound_member;
        }
        if node.kind() == "pointer_expression"
            && node_text(node, source).trim_start().starts_with('&')
        {
            let mut argument = node.child_by_field_name("argument");
            while argument.is_some_and(|arg| arg.kind() == "parenthesized_expression") {
                argument = argument.and_then(|arg| arg.named_code_child(0));
            }
            // Taking an independent primitive local's address publishes no
            // receiver storage. Pointer/reference/record aliases remain open.
            escapes |= !argument.is_some_and(|arg| {
                if arg.kind() != "identifier" {
                    return false;
                }
                let name = node_text(arg, source);
                let position = node.start_byte();
                let nearest = locals
                    .get(name)
                    .into_iter()
                    .flatten()
                    .filter(|(decl, begin, end)| {
                        *decl <= position && *begin <= position && position < *end
                    })
                    .max_by_key(|(decl, _, _)| *decl);
                nearest.is_some_and(|binding| {
                    local_values
                        .get(name)
                        .is_some_and(|values| values.contains(binding))
                })
            });
        }
    });
    escapes
}

// Distinct branches/iterations of a runtime entry can be selected by distinct
// invocations. A may-call union cannot certify that both helpers are one
// coupled access role; retain their original unresolved roles in that case.
fn conditionally_called(mut node: Node<'_>, body: Node<'_>) -> bool {
    while let Some(parent) = node.parent() {
        if parent == body {
            return false;
        }
        if parent.kind() == "binary_expression"
            && parent
                .child_by_field_name("operator")
                .is_some_and(|operator| matches!(operator.kind(), "&&" | "||" | "and" | "or"))
        {
            return true;
        }
        if matches!(
            parent.kind(),
            "if_statement"
                | "switch_statement"
                | "conditional_expression"
                | "for_statement"
                | "for_range_loop"
                | "while_statement"
                | "do_statement"
                | "try_statement"
                | "catch_clause"
        ) {
            return true;
        }
        node = parent;
    }
    false
}
