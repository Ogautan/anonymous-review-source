//! A thread constructor's callback does not execute the assignment receiving
//! the new handle. Re-evaluate that assignment with only its callback masked,
//! preserving any genuinely parallel enclosing callable or loop.
use super::*;

pub(super) fn serial_indexed_assignments(
    file: &ParsedCppFile,
    index: &EvidenceIndex<'_>,
    private: &HashSet<(usize, String)>,
) -> HashSet<(usize, String)> {
    let mut excluded = HashSet::new();
    let Some(tree) = &file.tree else {
        return excluded;
    };
    walk_nodes(tree.root_node(), &mut |node| {
        if node.kind() != "assignment_expression" || node.has_error() {
            return;
        }
        let (Some(left), Some(right)) = (
            node.child_by_field_name("left"),
            node.child_by_field_name("right"),
        ) else {
            return;
        };
        if right.kind() != "call_expression" {
            return;
        }
        let Some(function) = right.child_by_field_name("function") else {
            return;
        };
        if !matches!(
            node_text(function, &file.source).trim_start_matches("::"),
            "std::thread" | "std::jthread"
        ) {
            return;
        }
        let Some(callback) = right
            .child_by_field_name("arguments")
            .and_then(|args| args.named_child(0))
        else {
            return;
        };
        if callback.kind() != "lambda_expression" {
            return;
        }
        let targets = indexed_accesses(node_text(left, &file.source));
        let [(symbol, expression)] = targets.as_slice() else {
            return;
        };
        let line = left.start_position().row + 1;
        let source_line = file.source.lines().nth(line - 1).unwrap_or("");
        // The line-based consumer cannot separate two same-spelled targets.
        // Retain both in that ambiguous case rather than hiding a worker write.
        if indexed_accesses(source_line)
            .iter()
            .filter(|(s, _)| s == symbol)
            .count()
            != 1
        {
            return;
        }
        let mut masked = file.source.as_bytes().to_vec();
        for b in &mut masked[callback.byte_range()] {
            if *b != b'\n' {
                *b = b' ';
            }
        }
        // A syntactic placeholder preserves the surrounding AST and every
        // newline, including multi-line lambda capture lists.
        masked[callback.start_byte()] = b'0';
        let mut parsed =
            super::super::parser::parse_cpp_files(vec![super::super::types::CppFile {
                path: file.path.clone(),
                source: String::from_utf8(masked).expect("masked UTF-8 source"),
            }]);
        let masked = &mut parsed[0];
        masked.is_c = file.is_c;
        masked.allow_internal_linkage_proof = file.allow_internal_linkage_proof;
        if concurrent_context_lines(masked).contains(&line) {
            return;
        }
        let functions = collect_function_regions(masked);
        let mut origins = collect_index_partition_origins(masked, &functions);
        remove_private_api_partition_seeds(masked, index, private, &mut origins);
        if !origins.supports_parallel_argument(expression, line) {
            excluded.insert((line, symbol.clone()));
        }
    });
    excluded
}
