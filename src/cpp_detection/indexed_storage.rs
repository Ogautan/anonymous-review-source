//! A write below an indirect element does not write the outer contiguous slot.
//! Bind each use lexically; unknown types, overloaded operators and ambiguous
//! uses must not supply a negative proof for another access on the same line.
use crate::cpp_detection::parser::CodeChildren;
use std::collections::{HashMap, HashSet};

use super::super::parser::{ParsedCppFile, node_text, walk_nodes};
use super::{declarator_variable_name, field_access};
use tree_sitter::Node;

/// A record member cannot borrow contiguity from a same-spelled pointer or
/// container in another record. This only vetoes direct indexed mutations;
/// bound call summaries and aliases have separate storage provenance.
pub(super) fn unproved_member_accesses(
    file: &ParsedCppFile,
    index: &super::EvidenceIndex<'_>,
) -> HashSet<(usize, String)> {
    let Some(tree) = &file.tree else {
        return HashSet::new();
    };
    let variables = super::collect_variable_types(file, index);
    let bindings = field_access::collect(file, index, &variables, &[]);
    let mut uses = HashMap::<(usize, String), bool>::new();
    super::walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "subscript_expression" {
            return;
        }
        let Some(receiver) = node.child_by_field_name("argument") else {
            return;
        };
        let name = match receiver.kind() {
            "identifier" => Some(receiver),
            "field_expression" => receiver.child_by_field_name("field"),
            _ => None,
        };
        let Some(name) = name else { return };
        let name = node_text(name, &file.source);
        let line = receiver.start_position().row + 1;
        let matching = bindings
            .get(&line)
            .into_iter()
            .flatten()
            .filter(|access| access.start_byte == receiver.start_byte() && access.field == name)
            .collect::<Vec<_>>();
        let unproved = !node.has_error()
            && !matching.is_empty()
            && matching.iter().all(|access| {
                index
                    .record(access.record)
                    .fields
                    .iter()
                    .find(|field| field.name == name)
                    .is_some_and(|field| {
                        // Layout resolves visible aliases before evidence collection.
                        // Native pointers and arrays, and recognized containers, retain
                        // their own may-layout proof regardless of an unrelated namesake.
                        !field.is_array
                            && !outer_pointer(&field.ty_str)
                            && !super::is_contiguous_index_type(&field.ty_str)
                    })
            });
        // Candidate keys currently use a line and spelling. An unresolved or
        // genuinely contiguous use on that line must keep the shared key.
        uses.entry((line, name.to_owned()))
            .and_modify(|all| *all &= unproved)
            .or_insert(unproved);
    });
    uses.into_iter()
        .filter_map(|(key, unproved)| unproved.then_some(key))
        .collect()
}

fn outer_pointer(ty: &str) -> bool {
    let mut depth = 0usize;
    for ch in ty.chars() {
        match ch {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            '*' if depth == 0 => return true,
            _ => {}
        }
    }
    false
}

#[derive(Clone)]
enum Shape {
    Unknown,
    Indexed { indirect: bool, element: Box<Shape> },
}

impl Shape {
    fn indexed(self, indirect: bool) -> Self {
        Self::Indexed {
            indirect,
            element: Box::new(self),
        }
    }

    fn element(&self) -> Option<(&Self, bool)> {
        match self {
            Self::Indexed { indirect, element } => Some((element, *indirect)),
            Self::Unknown => None,
        }
    }
}

fn type_shape(text: &str, depth: usize) -> Shape {
    if depth > 16 {
        return Shape::Unknown;
    }
    let compact = text
        .split_whitespace()
        .filter(|t| !matches!(*t, "const" | "volatile"))
        .collect::<String>();
    if let Some(inner) = compact.strip_suffix('*') {
        return type_shape(inner, depth + 1).indexed(true);
    }
    // References to a container keep the referent's indexing semantics.
    if let Some(inner) = compact.strip_suffix('&') {
        return type_shape(inner, depth + 1);
    }
    let Some(argument) = field_access::first_template_argument(&compact) else {
        return Shape::Unknown;
    };
    let outer = compact
        .split('<')
        .next()
        .unwrap_or("")
        .trim_start_matches("::");
    match outer {
        "std::vector" | "std::span" => type_shape(argument, depth + 1).indexed(true),
        "std::array" => type_shape(argument, depth + 1).indexed(false),
        _ => Shape::Unknown,
    }
}

fn declared_shape(mut node: Node<'_>, mut shape: Shape) -> Shape {
    loop {
        shape = match node.kind() {
            "pointer_declarator" => shape.indexed(true),
            "array_declarator" => shape.indexed(false),
            "reference_declarator" | "parenthesized_declarator" | "init_declarator" => shape,
            "identifier" => return shape,
            _ => return Shape::Unknown,
        };
        let Some(inner) = node
            .child_by_field_name("declarator")
            .or_else(|| node.named_code_child(0))
        else {
            return Shape::Unknown;
        };
        node = inner;
    }
}

struct Binding {
    start: usize,
    end: usize,
    shape: Shape,
}

/// Keys for which *every* source-spelled indexed use on that line crosses a
/// proven indirection after selecting the first element. This is deliberately
/// not a symbol-wide exclusion: `rows[i] = other` still writes a vector header.
pub(super) fn pointee_only_accesses(file: &ParsedCppFile) -> HashSet<(usize, String)> {
    let Some(tree) = &file.tree else {
        return HashSet::new();
    };
    let mut macro_names = HashSet::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if matches!(node.kind(), "preproc_def" | "preproc_function_def")
            && let Some(name) = node.child_by_field_name("name")
        {
            macro_names.insert(node_text(name, &file.source));
        }
    });
    let mut bindings = HashMap::<String, Vec<Binding>>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(
            node.kind(),
            "declaration" | "parameter_declaration" | "optional_parameter_declaration"
        ) {
            return;
        }
        let scope = field_access::binding_scope(node);
        // Member and namespace lookup need a receiver-qualified binding. Do
        // not borrow a same-spelled declaration through an unsupported scope.
        let supported = matches!(
            scope.kind(),
            "translation_unit"
                | "compound_statement"
                | "function_definition"
                | "lambda_expression"
                | "for_statement"
                | "for_range_loop"
                | "if_statement"
                | "catch_clause"
        );
        let ty = node
            .child_by_field_name("type")
            .map(|n| node_text(n, &file.source));
        for decl in node.children_by_field_name("declarator", &mut node.walk()) {
            let Some(name) = declarator_variable_name(decl, &file.source) else {
                continue;
            };
            let mut conditional = false;
            let mut ancestor = node.parent();
            while let Some(parent) = ancestor {
                conditional |= parent.kind().starts_with("preproc_");
                ancestor = parent.parent();
            }
            let macro_bound = macro_names.contains(name.as_str())
                || ty.is_some_and(|ty| {
                    super::identifier_tokens(ty).any(|token| macro_names.contains(token))
                });
            let shape = if supported && !node.has_error() && !conditional && !macro_bound {
                declared_shape(decl, ty.map(|t| type_shape(t, 0)).unwrap_or(Shape::Unknown))
            } else {
                Shape::Unknown
            };
            bindings.entry(name).or_default().push(Binding {
                start: decl.start_byte(),
                end: scope.end_byte(),
                shape,
            });
        }
    });
    let mut uses = HashMap::<(usize, String), bool>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "subscript_expression" {
            return;
        }
        let Some(receiver) = node.child_by_field_name("argument") else {
            return;
        };
        let name = match receiver.kind() {
            "identifier" => node_text(receiver, &file.source),
            "field_expression" => {
                let Some(field) = receiver.child_by_field_name("field") else {
                    return;
                };
                node_text(field, &file.source)
            }
            _ => return,
        };
        let binding = (receiver.kind() == "identifier")
            .then(|| {
                bindings
                    .get(name)?
                    .iter()
                    .filter(|b| b.start < receiver.start_byte() && receiver.end_byte() < b.end)
                    .max_by_key(|b| b.start)
            })
            .flatten();
        let indirect = !node.has_error()
            && binding.is_some_and(|b| {
                // Do not resolve implicit member/namespace lookup using a
                // global declaration outside the receiver's scope.
                let mut ancestor = receiver.parent();
                while let Some(parent) = ancestor {
                    if matches!(
                        parent.kind(),
                        "class_specifier" | "struct_specifier" | "namespace_definition"
                    ) && b.start < parent.start_byte()
                    {
                        return false;
                    }
                    if parent.kind() == "function_definition"
                        && parent
                            .child_by_field_name("declarator")
                            .is_some_and(|d| node_text(d, &file.source).contains("::"))
                        && b.start < parent.start_byte()
                    {
                        return false;
                    }
                    ancestor = parent.parent();
                }
                b.shape
                    .element()
                    .is_some_and(|(element, _)| crosses_indirection(node, element, &file.source))
            });
        uses.entry((receiver.start_position().row + 1, name.to_owned()))
            .and_modify(|all| *all &= indirect)
            .or_insert(indirect);
    });
    uses.into_iter()
        .filter_map(|(key, indirect)| indirect.then_some(key))
        .collect()
}

fn crosses_indirection(mut node: Node<'_>, mut shape: &Shape, source: &str) -> bool {
    while let Some(parent) = node.parent() {
        match parent.kind() {
            "parenthesized_expression" => {}
            "subscript_expression" if parent.child_by_field_name("argument") == Some(node) => {
                let Some((element, indirect)) = shape.element() else {
                    return false;
                };
                if indirect {
                    return true;
                }
                shape = element;
            }
            "pointer_expression" if node_text(parent, source).trim_start().starts_with('*') => {
                return shape.element().is_some_and(|(_, indirect)| indirect);
            }
            "field_expression"
                if parent.child_by_field_name("argument") == Some(node)
                    && parent
                        .child_by_field_name("operator")
                        .is_some_and(|op| node_text(op, source) == "->") =>
            {
                return shape.element().is_some_and(|(_, indirect)| indirect);
            }
            _ => return false,
        }
        node = parent;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpp_detection::{parser::parse_cpp_files, types::CppFile};

    #[test]
    fn uncertain_lookup_and_inline_operators_do_not_prove_pointee_only_writes() {
        for source in [
            "std::vector<std::map<int,int>> rows; void f(int i) { rows[i][0]++; }",
            "std::vector<std::string> rows; void f(int i) { rows[i][0]++; }",
            "std::vector<std::array<int,8>> rows; void f(int i) { rows[i][0]++; }",
            "std::vector<std::vector<int>> rows; void f(int i) { rows[i][0]++; rows[i].clear(); }",
            "std::vector<std::vector<int>> rows; void f(int i, Opaque &rows) { rows[i][0]++; }",
            "std::vector<std::vector<int>> rows; struct S { int rows[8][8]; void f(int i) { rows[i][0]++; } };",
            "std::vector<std::vector<int>> rows; void S::f(int i) { rows[i][0]++; }",
            "std::vector<std::vector<int>> rows; namespace N { void f(int i) { rows[i][0]++; } }",
            "#if OPTION\nstd::vector<std::vector<int>> rows;\n#else\nint rows[8][8];\n#endif\nvoid f(int i) { rows[i][0]++; }",
            "#define rows real_rows\nstd::vector<std::vector<int>> rows; void f(int i) { rows[i][0]++; }",
        ] {
            let files = parse_cpp_files(vec![CppFile {
                path: "storage.cpp".into(),
                source: source.into(),
            }]);
            assert!(pointee_only_accesses(&files[0]).is_empty(), "{source}");
        }
    }
}
