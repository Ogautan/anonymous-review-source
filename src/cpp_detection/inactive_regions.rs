//! Exclude proved inactive literal preprocessor branches from both AST and
//! text evidence. This is deliberately not a macro/configuration preprocessor.

use std::ops::Range;

use tree_sitter::{Node, Tree};

use super::{node_text, walk_nodes};

pub(super) fn mask_literal_inactive_branches(source: &str, tree: &Tree) -> Option<String> {
    let mut ranges = Vec::<Range<usize>>::new();
    walk_nodes(tree.root_node(), &mut |root| {
        if !matches!(root.kind(), "preproc_if" | "preproc_ifdef") || root.has_error() {
            return;
        }
        // Recovery can swallow an #else/#endif and unrelated following code.
        // A missing closing token is not a safe deletion boundary.
        let Some(end) = root.children(&mut root.walk()).find(|child| {
            child.kind() == "#endif" && !child.is_missing() && node_text(*child, source) == "#endif"
        }) else {
            return;
        };
        let mut branch = Some(root);
        let mut earlier_always_taken = false;
        while let Some(current) = branch {
            let next = current.child_by_field_name("alternative");
            let condition = current.child_by_field_name("condition");
            let truth = condition.and_then(|condition| literal_truth(condition, source));
            let begin = if current.kind() == "preproc_else" {
                current.child(0).map(|token| token.end_byte())
            } else {
                condition
                    .map(|condition| condition.end_byte())
                    // #ifdef/#ifndef have a name rather than a condition.
                    .or_else(|| {
                        current
                            .child_by_field_name("name")
                            .map(|name| name.end_byte())
                    })
            };
            if (earlier_always_taken || truth == Some(false))
                && let Some(begin) = begin
            {
                let finish = next.map_or(end.start_byte(), |next| next.start_byte());
                if begin <= finish {
                    ranges.push(begin..finish);
                }
            }
            // Even after an unknown earlier arm, an unconditional true arm
            // rules out every later arm: either the earlier arm or this one
            // wins. It does not make this arm unconditionally reachable.
            earlier_always_taken |= truth == Some(true);
            branch = next;
        }
    });
    if ranges.is_empty() {
        return None;
    }
    ranges.sort_unstable_by_key(|range| (range.start, range.end));
    let mut merged = Vec::<Range<usize>>::new();
    for range in ranges {
        if let Some(last) = merged.last_mut()
            && range.start <= last.end
        {
            last.end = last.end.max(range.end);
        } else {
            merged.push(range);
        }
    }
    let mut masked = source.as_bytes().to_vec();
    let mut changed = false;
    for range in merged {
        for byte in &mut masked[range] {
            if !matches!(*byte, b'\n' | b'\r' | b' ' | b'\t') {
                *byte = b' ';
                changed = true;
            }
        }
    }
    changed
        .then(|| String::from_utf8(masked).expect("whole inactive byte regions replaced by ASCII"))
}

fn literal_truth(mut node: Node<'_>, source: &str) -> Option<bool> {
    if node.has_error() || node.is_missing() {
        return None;
    }
    while node.kind() == "parenthesized_expression" {
        node = node.named_child(0)?;
    }
    if node.kind() != "number_literal" {
        return None;
    }
    match node_text(node, source) {
        "0" => Some(false),
        "1" => Some(true),
        _ => None,
    }
}
