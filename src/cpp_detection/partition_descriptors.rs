//! Positional contracts for immutable scalar descriptors on concrete call paths.
use super::*;
use tree_sitter::Node;

pub(super) struct DeclarationAnnotations(HashSet<String>);

impl DeclarationAnnotations {
    pub(super) fn collect(files: &[ParsedCppFile]) -> Self {
        let mut definitions = HashMap::<String, Vec<String>>::new();
        let mut invalid = HashSet::new();
        for file in files {
            let Some(tree) = &file.tree else { continue };
            walk_nodes(tree.root_node(), &mut |node| {
                if node.kind() == "preproc_def"
                    && let Some(name) = node.child_by_field_name("name")
                {
                    let value = node
                        .child_by_field_name("value")
                        .map(|n| node_text(n, &file.source))
                        .unwrap_or("");
                    definitions
                        .entry(node_text(name, &file.source).to_owned())
                        .or_default()
                        .push(value.replace("\\\n", " ").replace("\\\r\n", " "));
                }
                if node.kind() == "preproc_function_def"
                    && let Some(name) = node.child_by_field_name("name")
                {
                    invalid.insert(node_text(name, &file.source).to_owned());
                }
                if node.kind() == "preproc_call"
                    && identifier_tokens(node_text(node, &file.source)).next() == Some("undef")
                {
                    invalid.extend(
                        identifier_tokens(node_text(node, &file.source))
                            .skip(1)
                            .map(ToOwned::to_owned),
                    );
                }
            });
        }
        // Annotation payloads do not participate in constructor initialization.
        // Other attributes (including layout/calling convention attributes) are
        // intentionally not inferred from their spelling.
        let annotation =
            Regex::new(r#"__attribute__\s*\(\(\s*annotate\s*\(\s*"[^"\\]*"\s*\)\s*\)\)"#).unwrap();
        let mut known = HashSet::new();
        for _ in 0..32 {
            let mut added = Vec::new();
            for (name, alternatives) in &definitions {
                if known.contains(name) || invalid.contains(name) {
                    continue;
                }
                if alternatives.iter().all(|value| {
                    let value = annotation.replace_all(value, " ");
                    value.split_whitespace().all(|token| {
                        matches!(
                            token,
                            "inline"
                                | "__inline__"
                                | "__inline"
                                | "__forceinline__"
                                | "__host__"
                                | "__device__"
                                | "constexpr"
                        ) || known.contains(token)
                    })
                }) {
                    added.push(name.clone());
                }
            }
            if added.is_empty() {
                break;
            }
            known.extend(added);
        }
        Self(known)
    }

    pub(super) fn api_fields(&self, file: &ParsedCppFile) -> HashMap<String, HashSet<String>> {
        let mut source = file.source.as_bytes().to_vec();
        let mut offset = 0;
        let mut changed = false;
        for line in file.source.split_inclusive('\n') {
            if self.0.contains(line.trim()) {
                for byte in &mut source[offset..offset + line.len()] {
                    if !matches!(*byte, b'\n' | b'\r') {
                        *byte = b' ';
                    }
                }
                changed = true;
            }
            offset += line.len();
        }
        if !changed {
            return api_fields(file);
        }
        let source = String::from_utf8(source).expect("only ASCII annotation lines replaced");
        let mut parser = tree_sitter::Parser::new();
        if parser
            .set_language(&tree_sitter_cpp::LANGUAGE.into())
            .is_err()
        {
            return api_fields(file);
        }
        let tree = parser.parse(&source, None);
        api_fields(&ParsedCppFile {
            path: file.path.clone(),
            source,
            tree,
            is_c: file.is_c,
            allow_internal_linkage_proof: file.allow_internal_linkage_proof,
        })
    }
}

/// Caller-selectable immutable coordinates are conditional API inputs, not
/// runtime identities. Bind them to their declared record and constructor.
pub(super) fn api_fields(file: &ParsedCppFile) -> HashMap<String, HashSet<String>> {
    let Some(tree) = &file.tree else {
        return HashMap::new();
    };
    let mut records = HashMap::new();
    let mut counts = HashMap::<String, usize>::new();
    walk_nodes(tree.root_node(), &mut |record| {
        if !matches!(record.kind(), "struct_specifier" | "class_specifier") {
            return;
        }
        let (Some(name), Some(body)) = (
            record.child_by_field_name("name"),
            record.child_by_field_name("body"),
        ) else {
            return;
        };
        let name = node_text(name, &file.source).to_owned();
        *counts.entry(name.clone()).or_default() += 1;
        if children(record)
            .iter()
            .any(|n| n.kind() == "base_class_clause")
        {
            return;
        }
        let mut fields = HashSet::new();
        let mut aggregate_fields = HashSet::new();
        let mut constructors = Vec::new();
        let mut public = record.kind() == "struct_specifier";
        let mut aggregate = public;
        for member in children(body) {
            if member.has_error() {
                aggregate = false;
            }
            if member.kind() == "access_specifier" {
                public = node_text(member, &file.source) == "public";
                continue;
            }
            if member.kind() == "field_declaration" {
                if !public {
                    aggregate = false;
                }
                let Some(ty) = member.child_by_field_name("type") else {
                    continue;
                };
                if !matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                    || !identifier_tokens(node_text(member, &file.source)).any(|n| n == "const")
                    || identifier_tokens(node_text(member, &file.source)).any(|n| n == "static")
                {
                    continue;
                }
                for field in member.children_by_field_name("declarator", &mut member.walk()) {
                    if field.kind() == "field_identifier" {
                        let field = node_text(field, &file.source).to_owned();
                        fields.insert(field.clone());
                        if public {
                            aggregate_fields.insert(field);
                        }
                    }
                }
            }
            if matches!(
                member.kind(),
                "function_definition" | "declaration" | "field_declaration"
            ) && let Some(declarator) = member.child_by_field_name("declarator")
                && declarator
                    .child_by_field_name("declarator")
                    .is_some_and(|n| node_text(n, &file.source) == name)
            {
                aggregate = false;
                if public && member.kind() == "function_definition" && !member.has_error() {
                    constructors.push(member);
                }
            }
        }
        let mut selectable = if aggregate {
            aggregate_fields
        } else {
            HashSet::new()
        };
        for constructor in constructors {
            let Some(body) = constructor.child_by_field_name("body") else {
                continue;
            };
            // An empty body cannot rewrite or escape the constructed object.
            if !children(body).is_empty() {
                continue;
            }
            let Some(parameters) = constructor
                .child_by_field_name("declarator")
                .and_then(|d| d.child_by_field_name("parameters"))
            else {
                continue;
            };
            let parameters = children(parameters)
                .into_iter()
                .filter_map(|p| {
                    let ty = p.child_by_field_name("type")?;
                    let value = p.child_by_field_name("declarator")?;
                    (matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                        && value.kind() == "identifier")
                        .then(|| node_text(value, &file.source))
                })
                .collect::<HashSet<_>>();
            let Some(initializers) = children(constructor)
                .into_iter()
                .find(|n| n.kind() == "field_initializer_list")
            else {
                continue;
            };
            for initializer in children(initializers) {
                let (Some(field), Some(values)) =
                    (initializer.named_child(0), initializer.named_child(1))
                else {
                    continue;
                };
                let field = node_text(field, &file.source);
                let values = children(values);
                if let [value] = values.as_slice()
                    && value.kind() == "identifier"
                    && fields.contains(field)
                    && parameters.contains(node_text(*value, &file.source))
                {
                    selectable.insert(field.to_owned());
                }
            }
        }
        if !selectable.is_empty() {
            records.insert(name, selectable);
        }
    });
    records.retain(|name, _| counts.get(name) == Some(&1));
    records
}

struct Contract {
    arity: usize,
    fields: Vec<(String, usize)>,
}

fn children(node: Node<'_>) -> Vec<Node<'_>> {
    node.named_children(&mut node.walk())
        .filter(|n| n.kind() != "comment")
        .collect()
}

fn direct_call<'a>(node: Node<'a>, source: &'a str) -> Option<(&'a str, Vec<Node<'a>>)> {
    if node.kind() != "call_expression" {
        return None;
    }
    let callee = node.child_by_field_name("function")?;
    if callee.kind() != "identifier" {
        return None;
    }
    Some((
        node_text(callee, source),
        children(node.child_by_field_name("arguments")?),
    ))
}

fn contract(node: Node<'_>, source: &str) -> Option<(String, Contract)> {
    if !matches!(node.kind(), "struct_specifier" | "class_specifier")
        || node.has_error()
        || node.parent()?.kind() != "translation_unit"
    {
        return None;
    }
    let name = node_text(node.child_by_field_name("name")?, source);
    let body = node.child_by_field_name("body")?;
    let mut fields = HashSet::new();
    let mut constructors = Vec::new();
    for member in children(body) {
        match member.kind() {
            "field_declaration" => {
                let ty = member.child_by_field_name("type")?;
                if !matches!(ty.kind(), "primitive_type" | "sized_type_specifier")
                    || !identifier_tokens(node_text(member, source)).any(|n| n == "const")
                {
                    return None;
                }
                let mut cursor = member.walk();
                for field in member.children_by_field_name("declarator", &mut cursor) {
                    if field.kind() != "field_identifier" {
                        return None;
                    }
                    fields.insert(node_text(field, source).to_owned());
                }
            }
            "function_definition" => constructors.push(member),
            "access_specifier" => {}
            _ => return None,
        }
    }
    let [constructor] = constructors.as_slice() else {
        return None;
    };
    if !children(constructor.child_by_field_name("body")?).is_empty() {
        return None;
    }
    let declarator = constructor.child_by_field_name("declarator")?;
    if node_text(declarator.child_by_field_name("declarator")?, source) != name {
        return None;
    }
    let parameters = children(declarator.child_by_field_name("parameters")?)
        .into_iter()
        .map(|p| {
            let ty = p.child_by_field_name("type")?;
            let parameter = p.child_by_field_name("declarator")?;
            (p.kind() == "parameter_declaration"
                && parameter.kind() == "identifier"
                && matches!(ty.kind(), "primitive_type" | "sized_type_specifier"))
            .then(|| node_text(parameter, source).to_owned())
        })
        .collect::<Option<Vec<_>>>()?;
    let list = children(*constructor)
        .into_iter()
        .find(|n| n.kind() == "field_initializer_list")?;
    let mut mapped = Vec::new();
    for initializer in children(list) {
        let field = node_text(initializer.named_child(0)?, source);
        if !fields.contains(field) {
            return None;
        }
        let values = children(initializer.named_child(1)?);
        let [value] = values.as_slice() else {
            return None;
        };
        if let Some(position) = parameters
            .iter()
            .position(|p| p == node_text(*value, source))
        {
            mapped.push((field.to_owned(), position));
        } else if !matches!(
            value.kind(),
            "number_literal" | "true" | "false" | "char_literal"
        ) {
            return None;
        }
    }
    (!mapped.is_empty()).then(|| {
        (
            name.to_owned(),
            Contract {
                arity: parameters.len(),
                fields: mapped,
            },
        )
    })
}

pub(super) fn propagate(file: &ParsedCppFile, origins: &mut IndexPartitionOrigins) {
    let Some(tree) = &file.tree else { return };
    let mut contracts = HashMap::new();
    let mut functions = HashMap::new();
    let mut declarations = HashMap::<String, usize>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if let Some((name, contract)) = contract(node, &file.source) {
            contracts.insert(name, contract);
        }
        if node.kind() == "function_declarator"
            && let Some(name) = node.child_by_field_name("declarator")
        {
            *declarations
                .entry(node_text(name, &file.source).to_owned())
                .or_default() += 1;
        }
        if node.kind() == "function_definition"
            && !node.has_error()
            && node
                .parent()
                .is_some_and(|p| p.kind() == "translation_unit")
            && let Some(name) = index_method_name(node, &file.source)
        {
            functions.insert(name, node);
        }
    });
    functions.retain(|name, _| declarations.get(name) == Some(&1));
    contracts.retain(|name, _| declarations.get(name) == Some(&1));
    let mut hidden = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "identifier" {
            return;
        }
        let name = node_text(node, &file.source);
        if !functions.contains_key(name) {
            return;
        }
        let direct = node.parent().is_some_and(|parent| {
            (parent.kind() == "function_declarator"
                && parent.child_by_field_name("declarator") == Some(node))
                || (parent.kind() == "call_expression"
                    && parent.child_by_field_name("function") == Some(node))
        });
        if !direct {
            hidden.insert(name.to_owned());
        }
    });
    for line in file
        .source
        .lines()
        .filter(|line| line.trim_start().starts_with('#'))
    {
        for name in identifier_tokens(line) {
            hidden.insert(name.to_owned());
        }
    }
    functions.retain(|name, _| !hidden.contains(name));
    contracts.retain(|name, _| !hidden.contains(name));

    let mut factories = HashMap::new();
    for (name, function) in &functions {
        let Some(ty) = function.child_by_field_name("type") else {
            continue;
        };
        let record = node_text(ty, &file.source);
        let Some(contract) = contracts.get(record) else {
            continue;
        };
        let Some(params) = function
            .child_by_field_name("declarator")
            .and_then(|d| d.child_by_field_name("parameters"))
        else {
            continue;
        };
        if !children(params).is_empty() {
            continue;
        }
        let Some(body) = function.child_by_field_name("body") else {
            continue;
        };
        let statements = children(body);
        let [statement] = statements.as_slice() else {
            continue;
        };
        if statement.kind() != "return_statement" {
            continue;
        }
        let Some(value) = statement.named_child(0) else {
            continue;
        };
        let Some((constructor, args)) = direct_call(value, &file.source) else {
            continue;
        };
        if constructor != record || args.len() != contract.arity {
            continue;
        }
        let fields = contract
            .fields
            .iter()
            .filter(|(_, position)| {
                if direct_call(args[*position], &file.source)
                    .is_some_and(|(callee, _)| functions.contains_key(callee))
                {
                    return false;
                }
                origins.supports_runtime_identity(
                    node_text(args[*position], &file.source),
                    args[*position].start_position().row + 1,
                )
            })
            .map(|(field, _)| field.clone())
            .collect::<Vec<_>>();
        if !fields.is_empty() {
            factories.insert(name.as_str(), (record, fields));
        }
    }
    let mut additions = Vec::new();
    walk_nodes(tree.root_node(), &mut |declaration| {
        if declaration.kind() != "declaration"
            || declaration.has_error()
            || declaration
                .parent()
                .is_none_or(|p| p.kind() != "compound_statement")
        {
            return;
        }
        let Some(init) = declaration
            .child_by_field_name("declarator")
            .filter(|n| n.kind() == "init_declarator")
        else {
            return;
        };
        let Some(variable) = init
            .child_by_field_name("declarator")
            .filter(|n| n.kind() == "identifier")
        else {
            return;
        };
        let Some(value) = init.child_by_field_name("value") else {
            return;
        };
        let Some((factory, args)) = direct_call(value, &file.source) else {
            return;
        };
        if !args.is_empty() {
            return;
        }
        let Some((record, fields)) = factories.get(factory) else {
            return;
        };
        // No intervening action can replace the descriptor or hide an alias.
        let Some(next) = declaration
            .next_named_sibling()
            .filter(|n| n.kind() == "expression_statement")
        else {
            return;
        };
        let Some(call) = next.named_child(0) else {
            return;
        };
        let Some((callee, args)) = direct_call(call, &file.source) else {
            return;
        };
        let Some(function) = functions.get(callee) else {
            return;
        };
        let Some(params) = function
            .child_by_field_name("declarator")
            .and_then(|d| d.child_by_field_name("parameters"))
        else {
            return;
        };
        let params = children(params);
        if params.len() != args.len() {
            return;
        }
        let Some(body) = function.child_by_field_name("body") else {
            return;
        };
        for (parameter, argument) in params.iter().zip(args) {
            if argument.kind() != "identifier"
                || node_text(argument, &file.source) != node_text(variable, &file.source)
            {
                continue;
            }
            if parameter
                .child_by_field_name("type")
                .is_none_or(|t| node_text(t, &file.source) != *record)
            {
                continue;
            }
            let Some(declarator) = parameter.child_by_field_name("declarator") else {
                continue;
            };
            if !matches!(declarator.kind(), "identifier" | "reference_declarator") {
                continue;
            }
            let Some(name) = declarator_variable_name(declarator, &file.source) else {
                continue;
            };
            for field in fields {
                additions.push((
                    body.start_position().row + 1,
                    body.end_position().row + 1,
                    format!("{name}.{field}"),
                ));
            }
        }
    });
    for (begin, end, member) in additions {
        if let Some((_, _, parameters)) = origins
            .regions
            .iter_mut()
            .find(|(b, e, _)| *b == begin && *e == end)
        {
            parameters.insert(member);
        }
    }
}
