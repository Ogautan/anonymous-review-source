use std::collections::HashMap;
use std::path::Path;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::Deserialize;

use crate::types::StructKey;

pub type RustcLayoutMap = HashMap<StructKey, RustcTypeLayout>;

#[derive(Debug, Clone)]
pub struct RustcTypeLayout {
    pub type_name: String,
    pub total_size: usize,
    pub alignment: usize,
    pub fields: Vec<RustcFieldLayout>,
}

#[derive(Debug, Clone)]
pub struct RustcFieldLayout {
    pub name: String,
    pub offset: usize,
    pub size: usize,
    pub alignment: Option<usize>,
}

pub fn collect_rustc_layouts(root: &Path) -> Result<RustcLayoutMap, String> {
    if !root.join("Cargo.toml").is_file() {
        return Ok(RustcLayoutMap::new());
    }

    let toolchain = installed_nightly_toolchain().unwrap_or_else(|| "nightly".to_string());
    let metadata = cargo_metadata(root, &toolchain)?;
    // `cargo rustc -- -Zprint-type-sizes` emits layouts only when rustc is
    // actually invoked. A previously cached artifact can therefore make a
    // second analysis silently return no layouts. Give this collection pass a
    // unique metadata salt so Cargo rebuilds the workspace target while still
    // reusing compiled dependencies.
    let rebuild_nonce = rustc_rebuild_nonce();
    let workspace_members: std::collections::HashSet<&str> = metadata
        .workspace_members
        .iter()
        .map(String::as_str)
        .collect();
    let mut layouts = RustcLayoutMap::new();
    let mut target_failures = Vec::new();

    for package in metadata
        .packages
        .iter()
        .filter(|package| workspace_members.contains(package.id.as_str()))
    {
        for target in &package.targets {
            let Some(target_arg) = rustc_target_arg(target) else {
                continue;
            };
            let output = match run_cargo_rustc(
                &toolchain,
                &package.manifest_path,
                target_arg,
                &rebuild_nonce,
            ) {
                Ok(output) => output,
                Err(error) => {
                    target_failures.push(format!("{}: {error}", target.name));
                    continue;
                }
            };
            for layout in parse_print_type_sizes(&output) {
                let Some(key) = rustc_struct_key(&package.name, &layout.type_name) else {
                    continue;
                };
                layouts.entry(key).or_insert(layout);
            }
        }
    }

    if !target_failures.is_empty() {
        return Err(format!(
            "rustc exact-layout collection failed for {} target(s): {}",
            target_failures.len(),
            target_failures.join("; ")
        ));
    }
    if layouts.is_empty() {
        return Err(format!(
            "cargo +{toolchain} rustc produced no usable, non-generic struct layouts"
        ));
    }

    Ok(layouts)
}

fn cargo_metadata(root: &Path, toolchain: &str) -> Result<CargoMetadata, String> {
    let output = Command::new("cargo")
        .arg(format!("+{toolchain}"))
        .arg("metadata")
        .arg("--no-deps")
        .arg("--format-version")
        .arg("1")
        .current_dir(root)
        .output()
        .map_err(|err| format!("failed to run cargo metadata: {err}"))?;

    if !output.status.success() {
        return Err(format!(
            "cargo metadata failed: {}",
            stderr_or_status(&output.stderr, output.status)
        ));
    }

    serde_json::from_slice(&output.stdout).map_err(|err| format!("parse cargo metadata: {err}"))
}

fn run_cargo_rustc(
    toolchain: &str,
    manifest_path: &str,
    target_arg: CargoTargetArg<'_>,
    rebuild_nonce: &str,
) -> Result<String, String> {
    let mut command = Command::new("cargo");
    command
        .arg(format!("+{toolchain}"))
        .arg("rustc")
        .arg("--manifest-path")
        .arg(manifest_path);
    match target_arg {
        CargoTargetArg::Lib => {
            command.arg("--lib");
        }
        CargoTargetArg::Bin(name) => {
            command.arg("--bin").arg(name);
        }
    }
    command
        .arg("--")
        .arg("-Zprint-type-sizes")
        .arg(format!("-Cmetadata={rebuild_nonce}"));

    let output = command
        .output()
        .map_err(|err| format!("failed to run cargo +{toolchain} rustc: {err}"))?;
    if !output.status.success() {
        return Err(format!(
            "cargo +{toolchain} rustc failed: {}",
            stderr_or_status(&output.stderr, output.status)
        ));
    }

    let mut text = String::new();
    text.push_str(&String::from_utf8_lossy(&output.stdout));
    text.push_str(&String::from_utf8_lossy(&output.stderr));
    Ok(text)
}

fn rustc_rebuild_nonce() -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    format!("fsd{}t{nanos}", std::process::id())
}

fn installed_nightly_toolchain() -> Option<String> {
    let output = Command::new("rustup")
        .arg("toolchain")
        .arg("list")
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }

    let text = String::from_utf8_lossy(&output.stdout);
    text.lines()
        .filter_map(installed_toolchain_name)
        .filter(|name| name.starts_with("nightly"))
        // Prefer the newest dated nightly. Old nightlies may not understand
        // the edition or language features used by the analyzed crate.
        .max_by_key(|name| {
            if let Some(date) = name.strip_prefix("nightly-") {
                (2u8, date.to_string())
            } else {
                (1u8, String::new())
            }
        })
        .map(str::to_string)
}

fn installed_toolchain_name(line: &str) -> Option<&str> {
    line.split_whitespace().next()
}

pub fn parse_print_type_sizes(output: &str) -> Vec<RustcTypeLayout> {
    let mut layouts = Vec::new();
    let mut current: Option<PendingTypeLayout> = None;

    for line in output.lines() {
        if let Some(header) = parse_type_header(line) {
            if let Some(layout) = current.take().and_then(PendingTypeLayout::finish) {
                layouts.push(layout);
            }
            current = Some(PendingTypeLayout {
                type_name: header.type_name,
                total_size: header.total_size,
                alignment: header.alignment,
                offset: 0,
                fields: Vec::new(),
            });
            continue;
        }

        let Some(pending) = current.as_mut() else {
            continue;
        };
        if let Some(size) = parse_padding_line(line) {
            pending.offset = pending.offset.saturating_add(size);
            continue;
        }
        if parse_end_padding_line(line).is_some() {
            continue;
        }
        if let Some(field) = parse_field_line(line, pending.offset) {
            pending.offset = pending.offset.saturating_add(field.size);
            pending.fields.push(field);
        }
    }

    if let Some(layout) = current.and_then(PendingTypeLayout::finish) {
        layouts.push(layout);
    }

    layouts
}

fn parse_type_header(line: &str) -> Option<TypeHeader> {
    let line = line.trim_start();
    let rest = line.strip_prefix("print-type-size type: `")?;
    let (type_name, rest) = rest.split_once("`: ")?;
    let (size_text, rest) = rest.split_once(" bytes, alignment: ")?;
    let (alignment_text, _) = rest.split_once(" bytes")?;
    Some(TypeHeader {
        type_name: type_name.to_string(),
        total_size: size_text.parse().ok()?,
        alignment: alignment_text.parse().ok()?,
    })
}

fn parse_field_line(line: &str, offset: usize) -> Option<RustcFieldLayout> {
    let line = line.trim_start();
    let rest = line.strip_prefix("print-type-size     field `.")?;
    let (name, rest) = rest.split_once("`: ")?;
    let (size_text, rest) = rest.split_once(" bytes")?;
    let alignment = rest
        .strip_prefix(", alignment: ")
        .and_then(|rest| rest.split_once(" bytes"))
        .and_then(|(alignment_text, _)| alignment_text.parse().ok());
    Some(RustcFieldLayout {
        name: name.to_string(),
        offset,
        size: size_text.parse().ok()?,
        alignment,
    })
}

fn parse_padding_line(line: &str) -> Option<usize> {
    let line = line.trim_start();
    let rest = line.strip_prefix("print-type-size     padding: ")?;
    let (size_text, _) = rest.split_once(" bytes")?;
    size_text.parse().ok()
}

fn parse_end_padding_line(line: &str) -> Option<usize> {
    let line = line.trim_start();
    let rest = line.strip_prefix("print-type-size     end padding: ")?;
    let (size_text, _) = rest.split_once(" bytes")?;
    size_text.parse().ok()
}

fn rustc_struct_key(package_name: &str, type_name: &str) -> Option<StructKey> {
    if type_name.starts_with('{')
        || type_name.starts_with('[')
        || type_name.starts_with('&')
        || type_name.contains('<')
    {
        return None;
    }
    let mut segments = type_name.split("::").collect::<Vec<_>>();
    let name = segments.pop()?.trim();
    if name.is_empty() || !name.chars().all(|ch| ch == '_' || ch.is_alphanumeric()) {
        return None;
    }
    let normalized_package = package_name.replace('-', "_");
    if segments
        .first()
        .is_some_and(|segment| *segment == package_name || *segment == normalized_package)
    {
        segments.remove(0);
    }
    Some(StructKey::new(package_name, segments.join("::"), name))
}

fn rustc_target_arg(target: &CargoTarget) -> Option<CargoTargetArg<'_>> {
    if target.kind.iter().any(|kind| kind == "lib") {
        return Some(CargoTargetArg::Lib);
    }
    if target.kind.iter().any(|kind| kind == "bin") {
        return Some(CargoTargetArg::Bin(&target.name));
    }
    None
}

fn stderr_or_status(stderr: &[u8], status: std::process::ExitStatus) -> String {
    let text = String::from_utf8_lossy(stderr);
    let first_line = text
        .lines()
        .find(|line| !line.trim().is_empty())
        .map(str::trim)
        .unwrap_or("");
    if first_line.is_empty() {
        status.to_string()
    } else {
        first_line.to_string()
    }
}

#[derive(Debug)]
struct TypeHeader {
    type_name: String,
    total_size: usize,
    alignment: usize,
}

#[derive(Debug)]
struct PendingTypeLayout {
    type_name: String,
    total_size: usize,
    alignment: usize,
    offset: usize,
    fields: Vec<RustcFieldLayout>,
}

impl PendingTypeLayout {
    fn finish(self) -> Option<RustcTypeLayout> {
        if self.fields.is_empty() {
            return None;
        }
        Some(RustcTypeLayout {
            type_name: self.type_name,
            total_size: self.total_size,
            alignment: self.alignment,
            fields: self.fields,
        })
    }
}

#[derive(Debug, Deserialize)]
struct CargoMetadata {
    packages: Vec<CargoPackage>,
    workspace_members: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct CargoPackage {
    name: String,
    id: String,
    targets: Vec<CargoTarget>,
    manifest_path: String,
}

#[derive(Debug, Deserialize)]
struct CargoTarget {
    kind: Vec<String>,
    name: String,
}

enum CargoTargetArg<'a> {
    Lib,
    Bin(&'a str),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_reordered_fields() {
        let output = r#"
print-type-size type: `Reordered`: 16 bytes, alignment: 8 bytes
print-type-size     field `.b`: 8 bytes
print-type-size     field `.c`: 2 bytes
print-type-size     field `.a`: 1 bytes
print-type-size     end padding: 5 bytes
"#;

        let layouts = parse_print_type_sizes(output);
        let layout = layouts
            .iter()
            .find(|layout| layout.type_name == "Reordered")
            .unwrap();
        let fields: Vec<_> = layout
            .fields
            .iter()
            .map(|field| (field.name.as_str(), field.offset, field.size))
            .collect();

        assert_eq!(layout.total_size, 16);
        assert_eq!(layout.alignment, 8);
        assert_eq!(fields, vec![("b", 0, 8), ("c", 8, 2), ("a", 10, 1)]);
    }

    #[test]
    fn parses_internal_padding_for_repr_c() {
        let output = r#"
print-type-size type: `CLayout`: 12 bytes, alignment: 4 bytes
print-type-size     field `.a`: 1 bytes
print-type-size     padding: 3 bytes
print-type-size     field `.b`: 4 bytes, alignment: 4 bytes
print-type-size     field `.c`: 2 bytes
print-type-size     end padding: 2 bytes
"#;

        let layout = parse_print_type_sizes(output).remove(0);
        let fields: Vec<_> = layout
            .fields
            .iter()
            .map(|field| {
                (
                    field.name.as_str(),
                    field.offset,
                    field.size,
                    field.alignment,
                )
            })
            .collect();

        assert_eq!(
            fields,
            vec![("a", 0, 1, None), ("b", 4, 4, Some(4)), ("c", 8, 2, None)]
        );
    }

    #[test]
    fn parses_cross_cache_line_offsets() {
        let output = r#"
print-type-size type: `Wide`: 80 bytes, alignment: 8 bytes
print-type-size     field `.prefix`: 60 bytes
print-type-size     padding: 4 bytes
print-type-size     field `.tail`: 8 bytes
print-type-size     end padding: 8 bytes
"#;

        let layout = parse_print_type_sizes(output).remove(0);
        let tail = layout
            .fields
            .iter()
            .find(|field| field.name == "tail")
            .unwrap();

        assert_eq!(tail.offset, 64);
        assert_eq!(tail.size, 8);
    }

    #[test]
    fn selects_installed_nightly_names() {
        assert_eq!(
            installed_toolchain_name("nightly-2026-01-30-x86_64-unknown-linux-gnu").unwrap(),
            "nightly-2026-01-30-x86_64-unknown-linux-gnu"
        );
        assert_eq!(
            installed_toolchain_name("stable-x86_64-unknown-linux-gnu (active, default)").unwrap(),
            "stable-x86_64-unknown-linux-gnu"
        );
    }

    #[test]
    fn rustc_type_identity_preserves_module_path() {
        assert_eq!(
            rustc_struct_key("demo-crate", "demo_crate::first::State")
                .unwrap()
                .qualified_name(),
            "first::State"
        );
        assert_eq!(
            rustc_struct_key("demo-crate", "demo_crate::second::State")
                .unwrap()
                .qualified_name(),
            "second::State"
        );
        assert!(rustc_struct_key("demo-crate", "demo_crate::State<u64>").is_none());
    }
}
