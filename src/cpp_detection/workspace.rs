use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use walkdir::WalkDir;

use crate::helpers::path_to_string;
use crate::types::AnalysisDiagnostic;

use super::compile_database::{find_compile_database, load_compile_database};
use super::types::{CppFile, CppProject};

const CPP_EXTENSIONS: &[&str] = &[
    "c", "cc", "cpp", "cxx", "h", "hh", "hpp", "hxx", "ipp", "inl",
];

pub fn discover_cpp_project(root: &Path) -> CppProject {
    let root = root.to_path_buf();
    let project_root = if root.is_file() {
        root.parent()
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf()
    } else {
        root.clone()
    };

    let compile_database = find_compile_database(&project_root);
    let has_compile_commands = compile_database.is_some();
    let has_cmake = find_upwards(&project_root, "CMakeLists.txt").is_some();
    let mut diagnostics = Vec::new();
    if !root.exists() {
        diagnostics.push(AnalysisDiagnostic::fatal(
            "input",
            Some(root.to_string_lossy()),
            "analysis path does not exist",
        ));
    }
    let (compile_commands, discovered_files) = if let Some(database) = compile_database {
        match load_compile_database(&database, &root) {
            Ok(commands) => {
                let mut compiled_files = commands
                    .iter()
                    .map(|command| PathBuf::from(&command.file))
                    .collect::<Vec<_>>();
                // Headers are not compilation units and usually do not occur
                // in the database, but they contain most record declarations.
                compiled_files.extend(collect_cpp_files(&root).into_iter().filter(|path| {
                    matches!(
                        path.extension().and_then(|extension| extension.to_str()),
                        Some("h" | "hh" | "hpp" | "hxx" | "ipp" | "inl")
                    )
                }));
                (commands, deduplicate_paths(compiled_files))
            }
            Err(error) => {
                diagnostics.push(AnalysisDiagnostic::warning(
                    "compile_commands",
                    Some(database.to_string_lossy()),
                    error,
                ));
                (Vec::new(), collect_cpp_files(&root))
            }
        }
    } else {
        (Vec::new(), collect_cpp_files(&root))
    };
    let files = discovered_files
        .into_iter()
        .filter_map(|path| match fs::read_to_string(&path) {
            Ok(source) => Some(CppFile {
                path: path_to_string(&path),
                source,
            }),
            Err(error) => {
                diagnostics.push(AnalysisDiagnostic::warning(
                    "read",
                    Some(path.to_string_lossy()),
                    format!("failed to read C/C++ source as UTF-8: {error}"),
                ));
                None
            }
        })
        .collect::<Vec<_>>();
    if files.is_empty() && diagnostics.iter().all(|diagnostic| !diagnostic.fatal) {
        diagnostics.push(AnalysisDiagnostic::fatal(
            "discovery",
            Some(root.to_string_lossy()),
            "no analyzable C/C++ source files were found",
        ));
    }

    CppProject {
        name: project_name(&project_root),
        files,
        has_compile_commands,
        has_cmake,
        compile_commands,
        diagnostics,
    }
}

fn deduplicate_paths(paths: Vec<PathBuf>) -> Vec<PathBuf> {
    let mut paths = paths
        .into_iter()
        // Prefer the real declaration path over whichever symlink happened to
        // be visited first. Besides making discovery deterministic, this keeps
        // diagnostics and dataset/source locations anchored at the canonical
        // production header.
        .map(|path| fs::canonicalize(&path).unwrap_or(path))
        .collect::<Vec<_>>();
    paths.sort();
    paths.dedup();
    paths
}

pub fn looks_like_cpp_project(root: &Path) -> bool {
    if root.join("compile_commands.json").is_file()
        || root.join("build/compile_commands.json").is_file()
        || root.join("CMakeLists.txt").is_file()
    {
        return true;
    }

    if root.is_file() {
        return is_cpp_source(root);
    }

    WalkDir::new(root)
        .max_depth(5)
        .into_iter()
        .filter_entry(should_descend)
        .filter_map(Result::ok)
        .any(|entry| {
            entry.path().is_file()
                && is_cpp_source(entry.path())
                && is_production_source(entry.path())
        })
}

pub fn collect_cpp_files(root: &Path) -> Vec<PathBuf> {
    if root.is_file() {
        return if is_cpp_source(root) {
            vec![root.to_path_buf()]
        } else {
            Vec::new()
        };
    }

    let mut seen = HashSet::new();
    let mut files = Vec::new();
    let canonical_root = fs::canonicalize(root).unwrap_or_else(|_| root.to_path_buf());

    for entry in WalkDir::new(root)
        .into_iter()
        .filter_entry(should_descend)
        .filter_map(Result::ok)
    {
        let path = entry.path();
        if !path.is_file()
            || !is_cpp_source(path)
            || !is_production_source(path)
            || is_generated_cpp_artifact(path)
        {
            continue;
        }
        let canonical = fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
        // Do not let a source-tree symlink expand the requested analysis
        // scope. In-tree aliases use their real path; external aliases remain
        // represented by the requested in-tree path.
        let selected = if canonical.starts_with(&canonical_root) {
            canonical
        } else {
            path.to_path_buf()
        };
        if seen.insert(path_to_string(&selected)) {
            files.push(selected);
        }
    }

    files.sort();
    files
}

fn is_cpp_source(path: &Path) -> bool {
    path.extension()
        .and_then(|ext| ext.to_str())
        .map(|ext| {
            CPP_EXTENSIONS
                .iter()
                .any(|candidate| ext.eq_ignore_ascii_case(candidate))
        })
        .unwrap_or(false)
}

fn is_production_source(path: &Path) -> bool {
    !path
        .components()
        .any(|component| is_ignored_directory_name(&component.as_os_str().to_string_lossy()))
}

fn is_generated_cpp_artifact(path: &Path) -> bool {
    let name = path
        .file_name()
        .map(|value| value.to_string_lossy())
        .unwrap_or_default();
    name.contains(".cubin.") || name.contains("_kernel.sm") || name.contains(".generated.")
}

fn should_descend(entry: &walkdir::DirEntry) -> bool {
    !entry.file_type().is_dir() || !is_ignored_directory_name(&entry.file_name().to_string_lossy())
}

fn is_ignored_directory_name(name: &str) -> bool {
    matches!(
        name,
        ".git"
            | ".hg"
            | ".svn"
            | ".cache"
            | ".venv"
            | "target"
            | "build"
            | "_build"
            | "out"
            | "dist"
            | "install"
            | "cmake-build-debug"
            | "cmake-build-release"
            | "CMakeFiles"
            | "bazel-bin"
            | "bazel-out"
            | "buck-out"
            | "third_party"
            | "third-party"
            | "vendor"
            | "external"
            | "contrib"
            | "deps"
            | "_deps"
            | "node_modules"
            | "generated"
            | "autogen"
            | "test"
            | "tests"
            | "gtest"
            | "googletest"
            | "benchmark"
            | "benchmarks"
            | "example"
            | "examples"
    )
}

fn find_upwards(start: &Path, name: &str) -> Option<PathBuf> {
    let mut current = Some(start);
    while let Some(path) = current {
        let candidate = path.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
        current = path.parent();
    }
    None
}

fn project_name(root: &Path) -> String {
    root.file_name()
        .map(|name| name.to_string_lossy().to_string())
        .unwrap_or_else(|| "cpp_project".to_string())
}
