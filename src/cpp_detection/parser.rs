use std::sync::Arc;
use tree_sitter::{Node, Parser, Tree, TreeCursor};

use super::types::CppFile;

#[path = "inactive_regions.rs"]
mod inactive_regions;

#[path = "source_text.rs"]
pub(super) mod source_text;

#[derive(Clone)]
pub struct ParsedCppFile {
    pub path: String,
    /// Active original syntax, shared by temporary analysis views.
    pub syntax_source: Arc<str>,
    /// Comment-free evidence text. Byte and line offsets match the syntax
    /// input; the tree retains comments from the original active source.
    pub source: String,
    pub tree: Option<Tree>,
    /// Source-language semantics, independently of the shared C/C++ grammar.
    /// The project analyzer refines the extension default using build variants.
    pub is_c: bool,
    /// Evidence collectors clear this when preprocessing can override linkage
    /// keywords. Temporary source views must preserve the conservative flag.
    pub allow_internal_linkage_proof: bool,
}

impl ParsedCppFile {
    /// Explicit source transformations must edit both views. In particular,
    /// reparsing a macro/annotation view must not drop unrelated comments and
    /// change recovery of a conditional class elsewhere in the same file.
    pub(super) fn reparse_with_edits(&self, edits: &[(usize, usize, String)]) -> Option<Self> {
        if edits.windows(2).any(|pair| pair[0].1 > pair[1].0) {
            return None;
        }
        let mut syntax = self.syntax_source.to_string();
        let mut evidence = self.source.clone();
        for (start, end, replacement) in edits.iter().rev() {
            if start > end
                || *end > evidence.len()
                || *end > syntax.len()
                || ![*start, *end].iter().all(|&offset| {
                    syntax.is_char_boundary(offset) && evidence.is_char_boundary(offset)
                })
            {
                return None;
            }
            syntax.replace_range(*start..*end, replacement);
            evidence.replace_range(*start..*end, replacement);
        }
        self.reparse_views(syntax, evidence)
    }

    pub(super) fn reparse_masked_ranges(&self, ranges: &[std::ops::Range<usize>]) -> Option<Self> {
        self.reparse_views(
            source_text::mask_ranges(&self.syntax_source, ranges)
                .unwrap_or_else(|| self.syntax_source.to_string()),
            source_text::mask_ranges(&self.source, ranges).unwrap_or_else(|| self.source.clone()),
        )
    }

    fn reparse_views(&self, syntax: String, evidence: String) -> Option<Self> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_cpp::LANGUAGE.into())
            .ok()?;
        let tree = parser.parse(&syntax, None)?;
        Some(Self {
            path: self.path.clone(),
            syntax_source: syntax.into(),
            source: evidence,
            tree: Some(tree),
            is_c: self.is_c,
            allow_internal_linkage_proof: self.allow_internal_linkage_proof,
        })
    }
}

pub fn parse_cpp_files(files: Vec<CppFile>) -> Vec<ParsedCppFile> {
    let worker_count = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1)
        .min(4)
        .min(files.len());
    if worker_count <= 1 || files.len() < 32 {
        return parse_cpp_batch(files.into_iter().enumerate().collect())
            .into_iter()
            .map(|(_, file)| file)
            .collect();
    }

    let mut batches: Vec<Vec<(usize, CppFile)>> = (0..worker_count).map(|_| Vec::new()).collect();
    for (idx, file) in files.into_iter().enumerate() {
        batches[idx % worker_count].push((idx, file));
    }
    let handles: Vec<_> = batches
        .into_iter()
        .map(|batch| std::thread::spawn(move || parse_cpp_batch(batch)))
        .collect();
    let mut parsed: Vec<(usize, ParsedCppFile)> = handles
        .into_iter()
        .flat_map(|handle| handle.join().expect("C++ parser worker panicked"))
        .collect();
    parsed.sort_unstable_by_key(|(idx, _)| *idx);
    parsed.into_iter().map(|(_, file)| file).collect()
}

fn parse_cpp_batch(files: Vec<(usize, CppFile)>) -> Vec<(usize, ParsedCppFile)> {
    let mut parser = Parser::new();
    if parser
        .set_language(&tree_sitter_cpp::LANGUAGE.into())
        .is_err()
    {
        return files
            .into_iter()
            .map(|(idx, file)| {
                (
                    idx,
                    ParsedCppFile {
                        is_c: file.path.ends_with(".c"),
                        allow_internal_linkage_proof: true,
                        path: file.path,
                        source: source_text::mask_comments(&file.source),
                        syntax_source: file.source.into(),
                        tree: None,
                    },
                )
            })
            .collect();
    }

    files
        .into_iter()
        .map(|(idx, file)| {
            // Preserve original syntax for the parser's error recovery. Facts
            // use a separate comment-free view at exactly the same offsets.
            let mut syntax_source = file.source;
            let mut evidence_source = source_text::mask_comments(&syntax_source);
            let mut tree = parser.parse(&syntax_source, None);
            let ranges = tree
                .as_ref()
                .map(|tree| inactive_regions::literal_inactive_ranges(&evidence_source, tree))
                .unwrap_or_default();
            if let Some(source) = source_text::mask_ranges(&syntax_source, &ranges) {
                // Both views exclude exactly the same proved inactive branches.
                // Active comments remain available to syntax recovery only.
                syntax_source = source;
                evidence_source =
                    source_text::mask_ranges(&evidence_source, &ranges).unwrap_or(evidence_source);
                tree = parser.parse(&syntax_source, None);
            }
            (
                idx,
                ParsedCppFile {
                    is_c: file.path.ends_with(".c"),
                    allow_internal_linkage_proof: true,
                    path: file.path,
                    syntax_source: syntax_source.into(),
                    source: evidence_source,
                    tree,
                },
            )
        })
        .collect()
}

pub fn apply_source_dialects(
    files: &mut [ParsedCppFile],
    commands: &[super::types::CppCompileCommand],
) {
    for file in files {
        let variants = commands
            .iter()
            .filter(|command| command.file == file.path)
            .collect::<Vec<_>>();
        if !variants.is_empty() {
            // A C++ or unresolved build variant precludes C-only exclusion.
            file.is_c = variants.iter().all(|command| command_uses_c(command));
        }
    }
}

fn command_uses_c(command: &super::types::CppCompileCommand) -> bool {
    let mut explicit = None;
    let mut source_languages = Vec::new();
    let mut msvc_override = None;
    let mut arguments = command.arguments.iter();
    while let Some(argument) = arguments.next() {
        if argument.starts_with('@') || argument == "--" {
            return false;
        }
        if !argument.starts_with('-') {
            let path = std::path::Path::new(&command.directory).join(argument);
            let path = std::fs::canonicalize(&path).unwrap_or(path);
            if path == std::path::Path::new(&command.file) {
                // -x applies to subsequent inputs, not to an earlier file.
                source_languages.push(explicit);
            }
        }
        let language = if argument == "-x" {
            arguments.next().map(String::as_str)
        } else {
            argument.strip_prefix("-x").filter(|s| !s.is_empty())
        };
        if let Some(language) = language {
            explicit = (language != "none").then_some(language == "c");
        }
        if argument == "/TC" {
            msvc_override = Some(true);
        }
        if argument == "/TP" || argument.starts_with("/Tp") || argument.starts_with("/Tc") {
            msvc_override = Some(false);
        }
    }
    if let Some(is_c) = msvc_override {
        return is_c;
    }
    let cpp_standard = command.arguments.iter().any(|argument| {
        argument.starts_with("-std=c++")
            || argument.starts_with("-std=gnu++")
            || argument.starts_with("/std:c++")
    });
    let compiler = std::path::Path::new(&command.compiler)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("");
    let compiler = if matches!(compiler, "ccache" | "sccache" | "distcc") {
        command
            .arguments
            .get(1)
            .and_then(|arg| std::path::Path::new(arg).file_name())
            .and_then(|n| n.to_str())
            .unwrap_or("")
    } else {
        compiler
    };
    let c_driver = matches!(
        compiler,
        "cc" | "gcc"
            | "clang"
            | "clang-cl"
            | "clang-cl.exe"
            | "cl"
            | "cl.exe"
            | "icc"
            | "icx"
            | "tcc"
    ) || ["gcc-", "clang-"].iter().any(|prefix| {
        compiler.strip_prefix(prefix).is_some_and(|version| {
            !version.is_empty() && version.bytes().all(|c| c.is_ascii_digit() || c == b'.')
        })
    });
    let default_c = c_driver && command.file.ends_with(".c") && !cpp_standard;
    if source_languages.is_empty() {
        source_languages.push(explicit);
    }
    source_languages
        .into_iter()
        .all(|language| language.unwrap_or(default_c))
}

pub fn node_text<'a>(node: Node<'_>, source: &'a str) -> &'a str {
    node.utf8_text(source.as_bytes()).unwrap_or("")
}

/// Semantic traversal of an original-source tree. Comments participate in
/// syntax recovery, but never occupy argument/statement positions in facts.
pub(super) trait CodeChildren<'tree> {
    fn next_named_code_sibling(&self) -> Option<Node<'tree>>;
    fn named_code_child(&self, index: u32) -> Option<Node<'tree>>;
    fn named_code_child_count(&self) -> usize;
    fn named_code_children<'cursor>(
        &self,
        cursor: &'cursor mut TreeCursor<'tree>,
    ) -> impl Iterator<Item = Node<'tree>> + 'cursor;
    fn code_child(&self, index: u32) -> Option<Node<'tree>>;
    fn code_child_count(&self) -> usize;
    fn code_children<'cursor>(
        &self,
        cursor: &'cursor mut TreeCursor<'tree>,
    ) -> impl Iterator<Item = Node<'tree>> + 'cursor;
}

impl<'tree> CodeChildren<'tree> for Node<'tree> {
    fn next_named_code_sibling(&self) -> Option<Node<'tree>> {
        let mut sibling = self.next_named_sibling();
        while sibling.is_some_and(|node| node.kind() == "comment") {
            sibling = sibling.and_then(|node| node.next_named_sibling());
        }
        sibling
    }

    fn named_code_child(&self, index: u32) -> Option<Node<'tree>> {
        self.named_code_children(&mut self.walk())
            .nth(index as usize)
    }

    fn named_code_child_count(&self) -> usize {
        self.named_code_children(&mut self.walk()).count()
    }

    fn named_code_children<'cursor>(
        &self,
        cursor: &'cursor mut TreeCursor<'tree>,
    ) -> impl Iterator<Item = Node<'tree>> + 'cursor {
        self.named_children(cursor)
            .filter(|node| node.kind() != "comment")
    }

    fn code_child(&self, index: u32) -> Option<Node<'tree>> {
        self.code_children(&mut self.walk()).nth(index as usize)
    }

    fn code_child_count(&self) -> usize {
        self.code_children(&mut self.walk()).count()
    }

    fn code_children<'cursor>(
        &self,
        cursor: &'cursor mut TreeCursor<'tree>,
    ) -> impl Iterator<Item = Node<'tree>> + 'cursor {
        self.children(cursor)
            .filter(|node| node.kind() != "comment")
    }
}

pub fn walk_nodes<'tree, F>(node: Node<'tree>, f: &mut F)
where
    F: FnMut(Node<'tree>),
{
    // Generated C++ can produce very deeply nested syntax trees. An explicit
    // stack preserves the previous pre-order traversal without risking a
    // process stack overflow during whole-repository analysis.
    let mut pending = vec![node];
    while let Some(current) = pending.pop() {
        f(current);
        let mut cursor = current.walk();
        let children: Vec<_> = current.code_children(&mut cursor).collect();
        pending.extend(children.into_iter().rev());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpp_detection::layout::collect_cpp_structs;

    #[test]
    fn temporary_source_edits_preserve_unrelated_conditional_class_recovery() {
        let original = r###"#include <atomic>
#include <cstdint>
namespace grpc_core {
class RefCount {
 public:
  using Value = intptr_t;

  // `init` is the initial refcount stored in this object.
  //
  // `trace` is a string to be logged with trace events; if null, no
  // trace logging will be done.  Tracing is a no-op in non-debug builds.
  explicit RefCount(
      Value init = 1,
      const char*
#ifndef NDEBUG
          // Leave unnamed if NDEBUG to avoid unused parameter warning
          trace
#endif
      = nullptr)
      :
#ifndef NDEBUG
        trace_(trace),
#endif
        value_(init) {
  }

private:
 const char* trace_;
 std::atomic<Value> value_{0};
};
}

LOCK_WORD(global_lock);
"###;
        let mut file = parse_cpp_files(vec![CppFile {
            path: "recovery.hpp".into(),
            source: original.into(),
        }])
        .remove(0);
        file.allow_internal_linkage_proof = false;
        let start = original.find("LOCK_WORD").unwrap();
        let end = start + "LOCK_WORD(global_lock);".len();
        let edits = [(start, end, "pthread_mutex_t global_lock;".to_string())];
        let expanded = file.reparse_with_edits(&edits).unwrap();
        let range = start..end;
        let masked = file
            .reparse_masked_ranges(std::slice::from_ref(&range))
            .unwrap();
        for view in [expanded, masked] {
            assert!(view.syntax_source.contains("Leave unnamed"));
            assert!(!view.source.contains("Leave unnamed"));
            assert_eq!(view.syntax_source.len(), view.source.len());
            assert!(!view.allow_internal_linkage_proof);
            let records = collect_cpp_structs(&[view], "fixture", 64);
            assert!(
                records
                    .iter()
                    .any(|r| r.qualified_name == "grpc_core::RefCount")
            );
        }
    }
}
