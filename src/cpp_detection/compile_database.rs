use std::fs;
use std::path::{Path, PathBuf};

use serde::Deserialize;
use sha2::{Digest, Sha256};

use super::types::CppCompileCommand;

#[derive(Debug, Deserialize)]
struct RawCompileCommand {
    directory: PathBuf,
    file: PathBuf,
    #[serde(default)]
    arguments: Vec<String>,
    #[serde(default)]
    command: String,
}

pub fn find_compile_database(project_root: &Path) -> Option<PathBuf> {
    let direct = project_root.join("compile_commands.json");
    if direct.is_file() {
        return Some(direct);
    }
    let build = project_root.join("build/compile_commands.json");
    if build.is_file() {
        return Some(build);
    }
    find_upwards(project_root, "compile_commands.json")
}

pub fn load_compile_database(
    database: &Path,
    requested_root: &Path,
) -> Result<Vec<CppCompileCommand>, String> {
    let source = fs::read_to_string(database)
        .map_err(|error| format!("failed to read compilation database: {error}"))?;
    let raw: Vec<RawCompileCommand> = serde_json::from_str(&source)
        .map_err(|error| format!("failed to parse compilation database: {error}"))?;
    let requested =
        fs::canonicalize(requested_root).unwrap_or_else(|_| requested_root.to_path_buf());
    let mut commands = Vec::new();
    for entry in raw {
        let file = resolve_path(&entry.directory, &entry.file);
        let canonical_file = fs::canonicalize(&file).unwrap_or(file);
        let in_scope = if requested.is_file() {
            canonical_file == requested
        } else {
            canonical_file.starts_with(&requested)
        };
        if !in_scope || !canonical_file.is_file() || !is_cpp_source(&canonical_file) {
            continue;
        }
        let arguments = if entry.arguments.is_empty() {
            split_command_line(&entry.command)
        } else {
            entry.arguments
        };
        if arguments.is_empty() {
            continue;
        }
        let directory = fs::canonicalize(&entry.directory).unwrap_or(entry.directory);
        let semantic_arguments =
            normalize_semantic_arguments(&arguments, &directory, &canonical_file);
        let compiler = arguments.first().cloned().unwrap_or_default();
        let command_hash =
            command_hash(&compiler, &directory, &canonical_file, &semantic_arguments);
        commands.push(CppCompileCommand {
            directory: directory.to_string_lossy().into_owned(),
            file: canonical_file.to_string_lossy().into_owned(),
            compiler,
            arguments,
            semantic_arguments,
            variant_id: command_hash[..16].to_string(),
            command_hash,
        });
    }
    commands.sort_by(|left, right| {
        left.file
            .cmp(&right.file)
            .then_with(|| left.command_hash.cmp(&right.command_hash))
    });
    commands
        .dedup_by(|left, right| left.file == right.file && left.command_hash == right.command_hash);
    if commands.is_empty() {
        return Err("compilation database contains no valid in-scope C/C++ commands".to_string());
    }
    Ok(commands)
}

fn normalize_semantic_arguments(
    arguments: &[String],
    directory: &Path,
    source_file: &Path,
) -> Vec<String> {
    let mut normalized = Vec::new();
    let mut index = 1usize;
    while index < arguments.len() {
        let argument = &arguments[index];
        if argument == "-c" || argument == "-S" || argument == "-pipe" {
            index += 1;
            continue;
        }
        if matches!(argument.as_str(), "-o" | "-MF" | "-MT" | "-MQ") {
            index += 2;
            continue;
        }
        if argument.starts_with("-o") && argument.len() > 2
            || argument.starts_with("-MF") && argument.len() > 3
            || argument.starts_with("-MT") && argument.len() > 3
            || argument.starts_with("-MQ") && argument.len() > 3
            || matches!(argument.as_str(), "-MD" | "-MMD" | "-MP" | "-MG")
            || argument.starts_with("-fdiagnostics-color")
        {
            index += 1;
            continue;
        }
        if matches!(
            argument.as_str(),
            "-I" | "-isystem" | "-iquote" | "-include"
        ) {
            if let Some(path) = arguments.get(index + 1) {
                normalized.push(argument.clone());
                normalized.push(normalize_argument_path(directory, path));
            }
            index += 2;
            continue;
        }
        if let Some((prefix, path)) = ["-I", "-isystem", "-iquote", "-include"]
            .iter()
            .find_map(|prefix| argument.strip_prefix(prefix).map(|path| (*prefix, path)))
            .filter(|(_, path)| !path.is_empty())
        {
            normalized.push(format!(
                "{prefix}{}",
                normalize_argument_path(directory, path)
            ));
            index += 1;
            continue;
        }
        let argument_path = Path::new(argument);
        if argument_path == source_file || resolve_path(directory, argument_path) == source_file {
            index += 1;
            continue;
        }
        normalized.push(argument.clone());
        index += 1;
    }
    normalized
}

fn normalize_argument_path(directory: &Path, path: &str) -> String {
    let path = Path::new(path);
    let resolved = resolve_path(directory, path);
    fs::canonicalize(&resolved)
        .unwrap_or(resolved)
        .to_string_lossy()
        .into_owned()
}

fn command_hash(
    compiler: &str,
    directory: &Path,
    file: &Path,
    semantic_arguments: &[String],
) -> String {
    let mut hasher = Sha256::new();
    for value in [
        compiler,
        &directory.to_string_lossy(),
        &file.to_string_lossy(),
    ] {
        hasher.update(value.as_bytes());
        hasher.update([0]);
    }
    for argument in semantic_arguments {
        hasher.update(argument.as_bytes());
        hasher.update([0]);
    }
    hex::encode(hasher.finalize())
}

fn resolve_path(directory: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        directory.join(path)
    }
}

fn is_cpp_source(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|extension| extension.to_str()),
        Some("c" | "cc" | "cpp" | "cxx")
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

fn split_command_line(command: &str) -> Vec<String> {
    let mut arguments = Vec::new();
    let mut current = String::new();
    let mut quote = None;
    let mut escaped = false;
    for character in command.chars() {
        if escaped {
            current.push(character);
            escaped = false;
            continue;
        }
        if character == '\\' && quote != Some('\'') {
            escaped = true;
            continue;
        }
        if matches!(character, '\'' | '"') {
            if quote == Some(character) {
                quote = None;
            } else if quote.is_none() {
                quote = Some(character);
            } else {
                current.push(character);
            }
            continue;
        }
        if character.is_whitespace() && quote.is_none() {
            if !current.is_empty() {
                arguments.push(std::mem::take(&mut current));
            }
        } else {
            current.push(character);
        }
    }
    if escaped {
        current.push('\\');
    }
    if !current.is_empty() {
        arguments.push(current);
    }
    arguments
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn command_split_preserves_quoted_arguments() {
        assert_eq!(
            split_command_line("clang++ -I'include dir' -DNAME=\"a b\" -c source.cpp"),
            vec!["clang++", "-Iinclude dir", "-DNAME=a b", "-c", "source.cpp",]
        );
    }

    #[test]
    fn database_preserves_build_variants_and_normalizes_include_paths() {
        let root = tempdir().expect("create project");
        fs::create_dir(root.path().join("include")).expect("create include directory");
        fs::write(root.path().join("candidate.cpp"), "int main() {}").expect("write source");
        let database = serde_json::json!([
            {
                "directory": root.path(),
                "file": "candidate.cpp",
                "arguments": ["clang++", "-I", "include", "-DVARIANT=1", "-c", "candidate.cpp", "-o", "one.o"]
            },
            {
                "directory": root.path(),
                "file": "candidate.cpp",
                "command": "clang++ -Iinclude -DVARIANT=2 -c candidate.cpp -o two.o"
            }
        ]);
        let database_path = root.path().join("compile_commands.json");
        fs::write(
            &database_path,
            serde_json::to_vec(&database).expect("serialize database"),
        )
        .expect("write database");

        let commands =
            load_compile_database(&database_path, root.path()).expect("load compile database");
        assert_eq!(commands.len(), 2);
        assert_ne!(commands[0].variant_id, commands[1].variant_id);
        assert!(commands.iter().all(|command| {
            command.semantic_arguments.iter().any(|argument| {
                argument.trim_start_matches("-I").starts_with('/') && argument.ends_with("/include")
            })
        }));
        assert!(commands.iter().all(|command| {
            !command
                .semantic_arguments
                .iter()
                .any(|argument| argument == "-c" || argument == "-o" || argument.ends_with(".o"))
        }));
    }
}
