//! Bind indexed method summaries to their actual receiver. A method name is
//! not a storage identity: an atomic_ref::fetch_add must not borrow a table's
//! same-named indexed write. Unknown receiver types yield no positive evidence.
use super::*;
use tree_sitter::Node;

pub(super) type Calls = HashMap<(usize, String, Option<usize>), Vec<Vec<String>>>;

pub(super) struct BoundCall {
    pub begin: usize,
    pub line: usize,
    pub name: String,
    pub owner: Option<usize>,
    pub arguments: Vec<String>,
}

struct Binding {
    begin: usize,
    end: usize,
    owner: Option<usize>,
}

fn type_owner(text: &str, file: &ParsedCppFile, index: &EvidenceIndex<'_>) -> Option<usize> {
    let name = field_access::without_template_arguments(text);
    let name = name
        .split_whitespace()
        .filter(|word| !matches!(*word, "const" | "volatile" | "struct" | "class"))
        .collect::<String>();
    let short = name.rsplit("::").next()?;
    let owner = index.unambiguous_record_index(short, &file.path)?;
    if name.contains("::")
        && index.records[owner].qualified_name.trim_start_matches("::")
            != name.trim_start_matches("::")
    {
        return None;
    }
    Some(owner)
}

fn enclosing_owner(
    node: Node<'_>,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
) -> Option<usize> {
    let mut ancestor = node.parent();
    while let Some(parent) = ancestor {
        if parent.kind() == "function_definition" {
            return field_access::function_owner(parent, file, index);
        }
        ancestor = parent.parent();
    }
    None
}

fn receiver_owner(
    node: Node<'_>,
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    bindings: &HashMap<String, Vec<Binding>>,
    owner: Option<usize>,
) -> Option<usize> {
    match node.kind() {
        "this" => owner,
        "identifier" => {
            let name = node_text(node, &file.source);
            if let Some(binding) = bindings.get(name).and_then(|entries| {
                entries
                    .iter()
                    .filter(|b| b.begin < node.start_byte() && node.end_byte() <= b.end)
                    .max_by_key(|b| b.begin)
            }) {
                // An unknown local still shadows a known member.
                return binding.owner;
            }
            let owner = owner?;
            let field = index.records[owner]
                .fields
                .iter()
                .find(|f| f.name == name)?;
            field_access::type_record_in_scope(&field.ty_str, file, index, Some(owner))
        }
        "field_expression" => {
            let parent = receiver_owner(
                node.child_by_field_name("argument")?,
                file,
                index,
                bindings,
                owner,
            )?;
            let name = node_text(node.child_by_field_name("field")?, &file.source);
            let field = index.records[parent]
                .fields
                .iter()
                .find(|f| f.name == name)?;
            field_access::type_record_in_scope(&field.ty_str, file, index, Some(parent))
        }
        "parenthesized_expression" | "pointer_expression" => {
            receiver_owner(node.named_child(0)?, file, index, bindings, owner)
        }
        _ => None,
    }
}

pub(super) fn collect(file: &ParsedCppFile, index: &EvidenceIndex<'_>) -> Calls {
    let mut calls = Calls::new();
    for call in collect_spans(file, index) {
        calls
            .entry((call.line, call.name, call.owner))
            .or_default()
            .push(call.arguments);
    }
    calls
}

pub(super) fn collect_spans(file: &ParsedCppFile, index: &EvidenceIndex<'_>) -> Vec<BoundCall> {
    let mut calls = Vec::new();
    let Some(tree) = &file.tree else { return calls };
    let mut bindings = HashMap::<String, Vec<Binding>>::new();
    walk_nodes(tree.root_node(), &mut |node| {
        if !matches!(node.kind(), "declaration" | "parameter_declaration") {
            return;
        }
        let scope = field_access::binding_scope(node);
        for declarator in node.children_by_field_name("declarator", &mut node.walk()) {
            let Some(name) = declarator
                .child_by_field_name("declarator")
                .filter(|_| declarator.kind() == "function_declarator")
                .map(|n| node_text(n, &file.source).to_owned())
                .or_else(|| declarator_variable_name(declarator, &file.source))
            else {
                continue;
            };
            let owner = if !node.has_error()
                && (declarator.kind() != "function_declarator"
                    || value_initialized_receiver(declarator, file))
            {
                node.child_by_field_name("type")
                    .and_then(|ty| type_owner(node_text(ty, &file.source), file, index))
            } else {
                None
            };
            bindings.entry(name).or_default().push(Binding {
                begin: declarator.start_byte(),
                end: scope.end_byte(),
                owner,
            });
        }
    });
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "call_expression" || node.has_error() {
            return;
        }
        let Some(function) = node.child_by_field_name("function") else {
            return;
        };
        let (name, owner) = match function.kind() {
            "identifier" => (
                node_text(function, &file.source),
                enclosing_owner(node, file, index),
            ),
            "field_expression" => {
                let (Some(receiver), Some(method)) = (
                    function.child_by_field_name("argument"),
                    function.child_by_field_name("field"),
                ) else {
                    return;
                };
                if method.kind() != "field_identifier" {
                    return;
                }
                let owner = receiver_owner(
                    receiver,
                    file,
                    index,
                    &bindings,
                    enclosing_owner(node, file, index),
                );
                let Some(owner) = owner else { return };
                (node_text(method, &file.source), Some(owner))
            }
            "qualified_identifier" => {
                let (Some(scope), Some(name)) = (
                    function.child_by_field_name("scope"),
                    function.child_by_field_name("name"),
                ) else {
                    return;
                };
                let Some(owner) = type_owner(node_text(scope, &file.source), file, index) else {
                    return;
                };
                (node_text(name, &file.source), Some(owner))
            }
            _ => return,
        };
        let Some(arguments) = node.child_by_field_name("arguments") else {
            return;
        };
        let args = arguments
            .named_children(&mut arguments.walk())
            .filter(|arg| arg.kind() != "comment")
            .map(|arg| node_text(arg, &file.source).to_owned())
            .collect();
        calls.push(BoundCall {
            begin: node.start_byte(),
            line: node.start_position().row + 1,
            name: name.to_owned(),
            owner,
            arguments: args,
        });
    });
    calls
}
