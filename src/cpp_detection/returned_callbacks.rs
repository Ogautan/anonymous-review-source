//! Conditional index inputs of externally returned closures.
use super::*;

fn integer_type(text: &str) -> bool {
    let compact = text.split_whitespace().collect::<String>();
    matches!(
        compact.trim_start_matches("std::"),
        "int"
            | "unsigned"
            | "unsignedint"
            | "signed"
            | "signedint"
            | "short"
            | "unsignedshort"
            | "long"
            | "unsignedlong"
            | "longlong"
            | "unsignedlonglong"
            | "size_t"
            | "ptrdiff_t"
            | "int8_t"
            | "uint8_t"
            | "int16_t"
            | "uint16_t"
            | "int32_t"
            | "uint32_t"
            | "int64_t"
            | "uint64_t"
    )
}

fn scope_prefix(node: tree_sitter::Node<'_>, source: &str) -> String {
    let mut names = Vec::new();
    let mut parent = node.parent();
    while let Some(scope) = parent {
        if matches!(
            scope.kind(),
            "namespace_definition" | "class_specifier" | "struct_specifier"
        ) && let Some(name) = scope.child_by_field_name("name")
        {
            names.push(node_text(name, source));
        }
        parent = scope.parent();
    }
    names.reverse();
    names.join("::")
}

fn qualified(prefix: &str, name: &str) -> String {
    if prefix.is_empty() {
        name.to_owned()
    } else {
        format!("{prefix}::{name}")
    }
}

pub(super) struct IntegerAliases {
    known: HashSet<String>,
    declared: HashSet<String>,
}

impl IntegerAliases {
    fn supports(&self, ty: &str, prefix: &str) -> bool {
        if integer_type(ty) {
            return true;
        }
        if let Some(absolute) = ty.strip_prefix("::") {
            return self.known.contains(absolute);
        }
        let mut scope = prefix;
        loop {
            let name = qualified(scope, ty);
            if self.declared.contains(&name) {
                return self.known.contains(&name);
            }
            if scope.is_empty() {
                return false;
            }
            scope = scope
                .rsplit_once("::")
                .map(|(parent, _)| parent)
                .unwrap_or("");
        }
    }
}

pub(super) fn integer_aliases(files: &[ParsedCppFile]) -> IntegerAliases {
    let mut definitions = HashMap::<String, Vec<(String, String)>>::new();
    let mut invalid = HashSet::new();
    for file in files {
        let Some(tree) = &file.tree else { continue };
        walk_nodes(tree.root_node(), &mut |node| {
            if !matches!(
                node.kind(),
                "alias_declaration" | "struct_specifier" | "class_specifier" | "enum_specifier"
            ) {
                return;
            }
            let prefix = scope_prefix(node, &file.source);
            if node.kind() == "alias_declaration" {
                let (Some(name), Some(ty)) = (
                    node.child_by_field_name("name"),
                    node.child_by_field_name("type"),
                ) else {
                    return;
                };
                let name = qualified(&prefix, node_text(name, &file.source));
                let mut parent = node.parent();
                let mut local = false;
                while let Some(scope) = parent {
                    local |= matches!(scope.kind(), "function_definition" | "lambda_expression");
                    parent = scope.parent();
                }
                if local || node.has_error() {
                    invalid.insert(name);
                    return;
                }
                definitions
                    .entry(name)
                    .or_default()
                    .push((prefix, node_text(ty, &file.source).to_owned()));
                return;
            }
            if matches!(
                node.kind(),
                "struct_specifier" | "class_specifier" | "enum_specifier"
            ) && let Some(name) = node.child_by_field_name("name")
            {
                invalid.insert(qualified(&prefix, node_text(name, &file.source)));
            }
        });
    }
    let mut aliases = IntegerAliases {
        known: HashSet::new(),
        declared: definitions.keys().chain(invalid.iter()).cloned().collect(),
    };
    for _ in 0..16 {
        let additions = definitions
            .iter()
            .filter(|(name, values)| {
                !aliases.known.contains(*name)
                    && !invalid.contains(*name)
                    && values
                        .iter()
                        .all(|(prefix, ty)| aliases.supports(ty, prefix))
            })
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        if additions.is_empty() {
            break;
        }
        aliases.known.extend(additions);
    }
    aliases
}

pub(super) fn seed(
    file: &ParsedCppFile,
    aliases: &IntegerAliases,
    index: &EvidenceIndex<'_>,
    origins: &mut IndexPartitionOrigins,
) {
    let Some(tree) = &file.tree else { return };
    walk_nodes(tree.root_node(), &mut |lambda| {
        if lambda.kind() != "lambda_expression"
            || lambda.has_error()
            || lambda
                .parent()
                .is_none_or(|p| p.kind() != "return_statement")
        {
            return;
        }
        let Some(body) = lambda.child_by_field_name("body") else {
            return;
        };
        let mut ancestor = lambda.parent();
        while ancestor
            .is_some_and(|n| !matches!(n.kind(), "function_definition" | "lambda_expression"))
        {
            ancestor = ancestor.and_then(|n| n.parent());
        }
        let Some(factory) = ancestor.filter(|n| n.kind() == "function_definition") else {
            return;
        };
        if let Some(owner) = field_access::function_owner(factory, file, index) {
            let Some(name) = index_method_name(factory, &file.source) else {
                return;
            };
            if !index.records[owner].visibility.is_externally_exposed()
                || !index.records[owner].public_methods.contains(&name)
            {
                return;
            }
        } else {
            let Some(factory_body) = factory.child_by_field_name("body") else {
                return;
            };
            if identifier_tokens(&file.source[factory.start_byte()..factory_body.start_byte()])
                .any(|n| n == "static")
            {
                return;
            }
            let mut parent = factory.parent();
            while let Some(node) = parent {
                if matches!(
                    node.kind(),
                    "class_specifier"
                        | "struct_specifier"
                        | "function_definition"
                        | "lambda_expression"
                ) || (node.kind() == "namespace_definition"
                    && node.child_by_field_name("name").is_none())
                {
                    return;
                }
                parent = node.parent();
            }
        }
        let mut inputs = Vec::new();
        walk_nodes(lambda, &mut |parameter| {
            if parameter.kind() != "parameter_declaration"
                || parameter.end_byte() > body.start_byte()
            {
                return;
            }
            let (Some(ty), Some(name)) = (
                parameter.child_by_field_name("type"),
                parameter.child_by_field_name("declarator"),
            ) else {
                return;
            };
            if name.kind() == "identifier"
                && aliases.supports(
                    node_text(ty, &file.source),
                    &scope_prefix(parameter, &file.source),
                )
            {
                inputs.push(node_text(name, &file.source).to_owned());
            }
        });
        if let Some((_, _, parameters)) = origins.regions.iter_mut().find(|(start, end, _)| {
            *start == body.start_position().row + 1 && *end == body.end_position().row + 1
        }) {
            parameters.extend(inputs);
        }
    });
}
