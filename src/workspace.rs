use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

/// Describes a discovered crate within a workspace or standalone project.
#[derive(Debug, Clone)]
pub struct CrateInfo {
    pub name: String,
    pub root: PathBuf,
}

/// Discovers crates from the given root path.
///
/// Strategies (tried in order):
/// 1. If root/Cargo.toml has `[workspace]` → parse members globs
/// 2. If root/Cargo.toml exists but no workspace → single crate
/// 3. Otherwise → treat root as a plain directory
pub fn discover_crates(root: &Path) -> Vec<CrateInfo> {
    let cargo_toml = root.join("Cargo.toml");
    if !cargo_toml.is_file() {
        return vec![CrateInfo {
            name: root
                .file_name()
                .map(|n| n.to_string_lossy().to_string())
                .unwrap_or_else(|| "unknown".into()),
            root: root.to_path_buf(),
        }];
    }

    let content = match fs::read_to_string(&cargo_toml) {
        Ok(c) => c,
        Err(_) => {
            return vec![CrateInfo {
                name: "unknown".into(),
                root: root.to_path_buf(),
            }];
        }
    };

    let toml_value: toml::Value = match content.parse() {
        Ok(v) => v,
        Err(_) => {
            return vec![CrateInfo {
                name: "unknown".into(),
                root: root.to_path_buf(),
            }];
        }
    };

    if let Some(workspace) = toml_value.get("workspace")
        && let Some(members) = workspace.get("members").and_then(|m| m.as_array())
    {
        let mut crates = Vec::new();
        let excluded_roots = workspace
            .get("exclude")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|value| value.as_str())
            .flat_map(|pattern| {
                let pattern = root.join(pattern).to_string_lossy().to_string();
                glob::glob(&pattern)
                    .into_iter()
                    .flatten()
                    .filter_map(Result::ok)
            })
            .map(|path| canonical_path(&path))
            .collect::<std::collections::HashSet<_>>();
        if toml_value.get("package").is_some() {
            let name = toml_value
                .get("package")
                .and_then(|p| p.get("name"))
                .and_then(|n| n.as_str())
                .map(|s| s.to_string())
                .unwrap_or_else(|| dir_name(root));
            crates.push(CrateInfo {
                name,
                root: root.to_path_buf(),
            });
        }
        for member in members {
            if let Some(pattern) = member.as_str() {
                let full_pattern = root.join(pattern);
                let pattern_str = full_pattern.to_string_lossy().to_string();

                match glob::glob(&pattern_str) {
                    Ok(paths) => {
                        for entry in paths.flatten() {
                            if entry.join("Cargo.toml").is_file()
                                && !excluded_roots.contains(&canonical_path(&entry))
                            {
                                let name =
                                    read_crate_name(&entry).unwrap_or_else(|| dir_name(&entry));
                                crates.push(CrateInfo { name, root: entry });
                            }
                        }
                    }
                    Err(_) => {
                        let direct = root.join(pattern);
                        if direct.join("Cargo.toml").is_file() {
                            let name =
                                read_crate_name(&direct).unwrap_or_else(|| dir_name(&direct));
                            crates.push(CrateInfo { name, root: direct });
                        }
                    }
                }
            }
        }
        if !crates.is_empty() {
            // A Cargo manifest may be both a package and a workspace root.
            // The root package was inserted above; return it together with
            // discovered members instead of falling through to a single-crate
            // result that would silently drop the workspace membership.
            let mut seen_roots = std::collections::HashSet::new();
            crates.retain(|crate_info| seen_roots.insert(crate_info.root.clone()));
            crates.sort_by(|left, right| left.root.cmp(&right.root));
            return crates;
        }
    }

    let name = toml_value
        .get("package")
        .and_then(|p| p.get("name"))
        .and_then(|n| n.as_str())
        .map(|s| s.to_string())
        .unwrap_or_else(|| dir_name(root));

    vec![CrateInfo {
        name,
        root: root.to_path_buf(),
    }]
}

/// Collects all `.rs` files under a crate root.
pub fn collect_rs_files(crate_root: &Path) -> Vec<PathBuf> {
    if crate_root.join("Cargo.toml").is_file() {
        let mut files = Vec::new();
        let src = crate_root.join("src");
        if src.is_dir() {
            files.extend(collect_rs_files_under(&src));
        }
        let build = crate_root.join("build.rs");
        if build.is_file() {
            files.push(build);
        }
        files.sort();
        return files;
    }

    collect_rs_files_under(crate_root)
}

pub fn canonical_path(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

pub fn module_path_for_rs_file(crate_root: &Path, file: &Path) -> String {
    let crate_root = canonical_path(crate_root);
    let file = canonical_path(file);
    let src_root = crate_root.join("src");
    let Ok(relative) = file.strip_prefix(&src_root) else {
        return String::new();
    };

    let mut parts: Vec<String> = Vec::new();
    for component in relative.components() {
        let name = component.as_os_str().to_string_lossy();
        parts.push(name.to_string());
    }

    let Some(last) = parts.last_mut() else {
        return String::new();
    };
    if !last.ends_with(".rs") {
        return String::new();
    }
    last.truncate(last.len() - ".rs".len());

    if parts.len() == 1 && matches!(parts[0].as_str(), "lib" | "main" | "mod") {
        return String::new();
    }
    if matches!(parts.last().map(String::as_str), Some("mod")) {
        parts.pop();
    }
    if matches!(parts.first().map(String::as_str), Some("lib" | "main")) {
        parts.remove(0);
    }

    parts.join("::")
}

fn collect_rs_files_under(root: &Path) -> Vec<PathBuf> {
    let mut files = WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|e| {
            e.path().is_file() && e.path().extension().and_then(|x| x.to_str()) == Some("rs")
        })
        .filter(|e| is_production_source(e.path()))
        .map(|e| e.into_path())
        .collect::<Vec<_>>();
    files.sort();
    files
}

fn is_production_source(path: &Path) -> bool {
    !path.components().any(|component| {
        let name = component.as_os_str().to_string_lossy();
        matches!(
            name.as_ref(),
            ".git"
                | "target"
                | "bench"
                | "benches"
                | "benchmark"
                | "benchmarks"
                | "example"
                | "examples"
                | "test"
                | "tests"
                | "fuzz"
        )
    })
}

fn read_crate_name(crate_root: &Path) -> Option<String> {
    let content = fs::read_to_string(crate_root.join("Cargo.toml")).ok()?;
    let v: toml::Value = content.parse().ok()?;
    v.get("package")?
        .get("name")?
        .as_str()
        .map(|s| s.to_string())
}

fn dir_name(path: &Path) -> String {
    path.file_name()
        .map(|n| n.to_string_lossy().to_string())
        .unwrap_or_else(|| "unknown".into())
}
