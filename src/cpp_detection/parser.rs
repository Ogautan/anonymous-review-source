use tree_sitter::{Node, Parser, Tree};

use super::types::CppFile;

#[path = "inactive_regions.rs"]
mod inactive_regions;

#[derive(Clone)]
pub struct ParsedCppFile {
    pub path: String,
    pub source: String,
    pub tree: Option<Tree>,
    /// Source-language semantics, independently of the shared C/C++ grammar.
    /// The project analyzer refines the extension default using build variants.
    pub is_c: bool,
    /// Evidence collectors clear this when preprocessing can override linkage
    /// keywords. Temporary source views must preserve the conservative flag.
    pub allow_internal_linkage_proof: bool,
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
                        source: file.source,
                        tree: None,
                    },
                )
            })
            .collect();
    }

    files
        .into_iter()
        .map(|(idx, mut file)| {
            let mut tree = parser.parse(&file.source, None);
            if let Some(source) = tree.as_ref().and_then(|tree| {
                inactive_regions::mask_literal_inactive_branches(&file.source, tree)
            }) {
                // Every consumer, including text fallback, must use the same
                // reachable source view. Masking preserves byte/line offsets.
                file.source = source;
                tree = parser.parse(&file.source, None);
            }
            (
                idx,
                ParsedCppFile {
                    is_c: file.path.ends_with(".c"),
                    allow_internal_linkage_proof: true,
                    path: file.path,
                    source: file.source,
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
        let children: Vec<_> = current.children(&mut cursor).collect();
        pending.extend(children.into_iter().rev());
    }
}
