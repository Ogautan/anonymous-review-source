//! Read-only AST interface diagnostics: cargo run --example cpp_interface_probe -- FILE...
use std::{env, fs};
use tree_sitter::Node;

fn visit(node: Node<'_>, source: &str) {
    if matches!(node.kind(), "class_specifier" | "struct_specifier")
        && let (Some(name), Some(body)) = (
            node.child_by_field_name("name"),
            node.child_by_field_name("body"),
        )
    {
        println!(
            "type {} line {}",
            &source[name.byte_range()],
            node.start_position().row + 1
        );
        for member in body.named_children(&mut body.walk()) {
            if member.kind() == "access_specifier" || member.has_error() || member.kind() == "ERROR"
            {
                let text = source[member.byte_range()]
                    .chars()
                    .take(180)
                    .collect::<String>()
                    .replace('\n', " ");
                println!(
                    "  {} line {} error={} {}",
                    member.kind(),
                    member.start_position().row + 1,
                    member.has_error(),
                    text
                );
            }
        }
    }
    for child in node.named_children(&mut node.walk()) {
        visit(child, source);
    }
}

fn main() {
    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(&tree_sitter_cpp::LANGUAGE.into())
        .unwrap();
    for path in env::args().skip(1) {
        let source = fs::read_to_string(&path).expect("read source");
        println!("file {path}");
        let tree = parser.parse(&source, None).expect("parse source");
        visit(tree.root_node(), &source);
    }
}
