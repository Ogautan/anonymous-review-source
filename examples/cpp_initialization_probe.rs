//! Read-only allocation-range diagnostics: cargo run --example cpp_initialization_probe -- FILE...
use false_sharing_detector::cpp_detection::{
    initialization::collect_initialization_facts, parser::parse_cpp_files, types::CppFile,
};
use std::{env, fs};
fn main() {
    let files = parse_cpp_files(
        env::args()
            .skip(1)
            .map(|path| CppFile {
                source: fs::read_to_string(&path).expect("read source"),
                path,
            })
            .collect(),
    );
    let ranges = collect_initialization_facts(&files);
    for file in &files {
        println!("file {}", file.path);
        if let Some(tree) = &file.tree {
            let mut count = 0;
            false_sharing_detector::cpp_detection::parser::walk_nodes(tree.root_node(), &mut |n| {
                if (n.is_error() || n.is_missing()) && count < 20 {
                    count += 1;
                    println!(
                        "syntax {}:{} {} {:?}",
                        n.start_position().row + 1,
                        n.start_position().column + 1,
                        n.kind(),
                        file.source[n.byte_range()]
                            .chars()
                            .take(80)
                            .collect::<String>()
                    );
                }
                if n.kind() == "init_declarator" && file.source[n.byte_range()].contains("calloc(")
                {
                    println!(
                        "allocation AST={} parent={:?}",
                        n.to_sexp(),
                        n.parent().and_then(|p| p.parent()).map(|p| (
                            p.kind(),
                            p.has_error(),
                            p.start_position().row + 1
                        ))
                    );
                }
            });
        }
        for range in &ranges[&file.path] {
            let line = |pos: usize| file.source[..pos].bytes().filter(|b| *b == b'\n').count() + 1;
            println!(
                "{} declaration={} begin={} end={} next={:?}",
                range.receiver,
                line(range.declaration),
                line(range.begin),
                line(range.end),
                file.source[range.end..]
                    .chars()
                    .take(100)
                    .collect::<String>()
            );
        }
    }
}
