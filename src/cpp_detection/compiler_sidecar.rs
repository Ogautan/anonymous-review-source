use std::collections::HashMap;
use std::io::{Read, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use super::types::{
    CppAccessKind, CppCompileCommand, CppEvidenceItem, CppEvidenceKind, CppEvidenceSet,
    CppStructInfo,
};

pub const CPP_SIDECAR_SCHEMA_VERSION: &str = "false-sharing-cpp-semantic-sidecar/v1";
const SIDECAR_TIMEOUT: Duration = Duration::from_secs(60);
const MAX_SIDECAR_OUTPUT_BYTES: u64 = 64 * 1024 * 1024;

#[derive(Debug, Serialize)]
struct SidecarRequest<'a> {
    schema_version: &'static str,
    project_root: String,
    cache_line_size: usize,
    compile_commands: &'a [CppCompileCommand],
    candidate_accesses: Vec<SidecarCandidateAccess>,
}

#[derive(Debug, Serialize)]
struct SidecarCandidateAccess {
    record_name: String,
    field_name: String,
    file: String,
    line: usize,
    source_access_kind: String,
    function_name: Option<String>,
    in_concurrent_context: bool,
    through_shared_indirection: bool,
    through_raw_pointer: bool,
    through_thread_local: bool,
    through_nonescaping_local: bool,
    guard_ids: Vec<String>,
    initialization_phase: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CompilerSemanticFacts {
    pub schema_version: String,
    #[serde(default)]
    pub records: Vec<CompilerRecordLayout>,
    #[serde(default)]
    pub accesses: Vec<CompilerAccessFact>,
    #[serde(default)]
    pub diagnostics: Vec<String>,
    #[serde(default)]
    pub coverage: CompilerSemanticCoverage,
}

#[derive(Debug, Clone, Default, Deserialize)]
pub struct CompilerSemanticCoverage {
    #[serde(default)]
    pub command_mode: String,
    #[serde(default)]
    pub commands_selected: usize,
    #[serde(default)]
    pub translation_units_attempted: usize,
    #[serde(default)]
    pub translation_units_clean: usize,
    #[serde(default)]
    pub candidate_accesses: usize,
    #[serde(default)]
    pub confirmed_accesses: usize,
    #[serde(default)]
    pub functions: usize,
    #[serde(default)]
    pub call_edges: usize,
    #[serde(default)]
    pub cfg_files: usize,
    #[serde(default)]
    pub cfg_blocks: usize,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct CompilerRecordLayout {
    pub name: String,
    #[serde(default)]
    pub canonical_type: Option<String>,
    #[serde(default)]
    pub file: Option<String>,
    #[serde(default)]
    pub build_variant: Option<String>,
    /// Only layouts produced from the project's real compilation database may
    /// replace the source may-layout. Candidate-directed inferred commands are
    /// useful for syntax/access semantics, but do not identify the production
    /// ABI or preprocessor build variant.
    #[serde(default = "default_true")]
    pub authoritative: bool,
    pub size: usize,
    pub alignment: usize,
    #[serde(default)]
    pub packed: bool,
    pub fields: Vec<CompilerFieldLayout>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct CompilerFieldLayout {
    pub name: String,
    pub offset: usize,
    pub size: usize,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CompilerAccessFact {
    pub record_name: String,
    pub field_name: String,
    pub file: String,
    pub line: usize,
    pub access_kind: String,
    #[serde(default)]
    pub function_name: Option<String>,
    #[serde(default)]
    pub in_concurrent_context: bool,
    #[serde(default)]
    pub through_shared_indirection: bool,
    #[serde(default)]
    pub through_raw_pointer: bool,
    #[serde(default)]
    pub through_thread_local: bool,
    #[serde(default)]
    pub through_nonescaping_local: bool,
    #[serde(default)]
    pub guard_ids: Vec<String>,
    #[serde(default)]
    pub initialization_phase: bool,
}

pub fn run_compiler_sidecar(
    executable: &Path,
    project_root: &Path,
    cache_line_size: usize,
    commands: &[CppCompileCommand],
    records: &[CppStructInfo],
    evidence: &[CppEvidenceSet],
) -> Result<CompilerSemanticFacts, String> {
    let request = SidecarRequest {
        schema_version: CPP_SIDECAR_SCHEMA_VERSION,
        project_root: project_root.to_string_lossy().into_owned(),
        cache_line_size,
        compile_commands: commands,
        candidate_accesses: candidate_accesses(records, evidence),
    };
    let payload = serde_json::to_vec(&request)
        .map_err(|error| format!("failed to serialize compiler sidecar request: {error}"))?;
    let mut child = Command::new(executable)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to start compiler semantic sidecar: {error}"))?;
    child
        .stdin
        .take()
        .ok_or_else(|| "compiler semantic sidecar stdin was unavailable".to_string())?
        .write_all(&payload)
        .map_err(|error| format!("failed to write compiler sidecar request: {error}"))?;

    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| "compiler semantic sidecar stdout was unavailable".to_string())?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| "compiler semantic sidecar stderr was unavailable".to_string())?;
    let stdout_reader = std::thread::spawn(move || read_bounded(stdout));
    let stderr_reader = std::thread::spawn(move || read_bounded(stderr));

    let started = Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) if started.elapsed() < SIDECAR_TIMEOUT => {
                std::thread::sleep(Duration::from_millis(10));
            }
            Ok(None) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!(
                    "compiler semantic sidecar exceeded {} second timeout",
                    SIDECAR_TIMEOUT.as_secs()
                ));
            }
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!(
                    "failed to wait for compiler semantic sidecar: {error}"
                ));
            }
        }
    };
    let stdout = stdout_reader
        .join()
        .map_err(|_| "compiler sidecar stdout reader panicked".to_string())??;
    let stderr = stderr_reader
        .join()
        .map_err(|_| "compiler sidecar stderr reader panicked".to_string())??;
    if !status.success() {
        return Err(format!(
            "compiler semantic sidecar exited with {status}: {}",
            String::from_utf8_lossy(&stderr).trim()
        ));
    }
    let facts: CompilerSemanticFacts = serde_json::from_slice(&stdout)
        .map_err(|error| format!("invalid compiler semantic sidecar response: {error}"))?;
    if facts.schema_version != CPP_SIDECAR_SCHEMA_VERSION {
        return Err(format!(
            "unsupported compiler semantic sidecar schema '{}', expected '{}'",
            facts.schema_version, CPP_SIDECAR_SCHEMA_VERSION
        ));
    }
    Ok(facts)
}

fn read_bounded(reader: impl Read) -> Result<Vec<u8>, String> {
    let mut output = Vec::new();
    reader
        .take(MAX_SIDECAR_OUTPUT_BYTES + 1)
        .read_to_end(&mut output)
        .map_err(|error| format!("failed to read compiler sidecar output: {error}"))?;
    if output.len() as u64 > MAX_SIDECAR_OUTPUT_BYTES {
        return Err("compiler semantic sidecar output exceeded 64 MiB".to_string());
    }
    Ok(output)
}

fn candidate_accesses(
    records: &[CppStructInfo],
    evidence: &[CppEvidenceSet],
) -> Vec<SidecarCandidateAccess> {
    records
        .iter()
        .zip(evidence)
        .flat_map(|(record, evidence)| {
            evidence.items.iter().filter_map(|item| {
                Some(SidecarCandidateAccess {
                    record_name: record.qualified_name.clone(),
                    field_name: item.field_name.clone()?,
                    file: item.file.clone(),
                    line: item.line,
                    source_access_kind: access_kind_name(item.access_kind.as_ref()?).to_string(),
                    function_name: item.function_name.clone(),
                    in_concurrent_context: item.in_concurrent_context,
                    through_shared_indirection: item.through_shared_indirection,
                    through_raw_pointer: item.through_raw_pointer,
                    through_thread_local: item.through_thread_local,
                    through_nonescaping_local: item.through_nonescaping_local,
                    guard_ids: item.guard_ids.clone(),
                    initialization_phase: item.initialization_phase,
                })
            })
        })
        .collect()
}

fn access_kind_name(kind: &CppAccessKind) -> &'static str {
    match kind {
        CppAccessKind::Read => "read",
        CppAccessKind::Write => "write",
        CppAccessKind::ReadModifyWrite => "read_modify_write",
    }
}

pub fn apply_compiler_facts(
    facts: &CompilerSemanticFacts,
    records: &mut [CppStructInfo],
    evidence: &mut [CppEvidenceSet],
    cache_line_size: usize,
) -> (usize, usize) {
    let layouts = apply_record_layouts(&facts.records, records, cache_line_size);
    let accesses = apply_access_facts(&facts.accesses, records, evidence);
    (layouts, accesses)
}

fn apply_record_layouts(
    facts: &[CompilerRecordLayout],
    records: &mut [CppStructInfo],
    cache_line_size: usize,
) -> usize {
    let mut applied = 0usize;
    for record in records {
        let candidates = facts
            .iter()
            .filter(|fact| fact.authoritative && layout_matches_record(fact, record))
            .collect::<Vec<_>>();
        let Some(first) = candidates.first() else {
            continue;
        };
        if candidates
            .iter()
            .skip(1)
            .any(|candidate| !same_layout(first, candidate))
        {
            // Different target/configuration variants cannot be collapsed into
            // one "exact" layout. Keep the source-inferred may-layout.
            continue;
        }
        let by_name = first
            .fields
            .iter()
            .map(|field| (field.name.as_str(), field))
            .collect::<HashMap<_, _>>();
        if !record
            .fields
            .iter()
            .all(|field| by_name.contains_key(field.name.as_str()))
        {
            continue;
        }
        for field in &mut record.fields {
            let compiler_field = by_name[field.name.as_str()];
            field.offset = Some(compiler_field.offset);
            field.estimated_size = Some(compiler_field.size.max(1));
        }
        record.total_estimated_size = Some(first.size);
        record.align_bytes = Some(first.alignment);
        record.is_cache_aligned = first.alignment >= cache_line_size;
        record.is_packed = first.packed;
        record.has_cache_padding |= record.is_cache_aligned;
        record.cache_line_groups = exact_cache_line_groups(&record.fields, cache_line_size);
        // Exact ABI offsets do not make absolute cache-line groups exact when
        // the object base itself may start at several residues modulo B.
        // A B-aligned record has a fixed residue; otherwise the core keeps an
        // existential placement test while still reporting compiler-exact
        // offsets and sizes.
        record.cache_line_groups_precise = first.alignment >= cache_line_size;
        record.compiler_layout_exact = true;
        applied += 1;
    }
    applied
}

fn default_true() -> bool {
    true
}

fn layout_matches_record(fact: &CompilerRecordLayout, record: &CppStructInfo) -> bool {
    if let Some(canonical) = &fact.canonical_type {
        return canonical == &record.qualified_name;
    }
    if fact.name != record.name {
        return false;
    }
    fact.file
        .as_deref()
        .is_none_or(|file| file == record.file || record.file.ends_with(file))
}

fn same_layout(left: &CompilerRecordLayout, right: &CompilerRecordLayout) -> bool {
    left.size == right.size
        && left.alignment == right.alignment
        && left.packed == right.packed
        && left.fields == right.fields
}

fn exact_cache_line_groups(
    fields: &[super::types::CppFieldInfo],
    cache_line_size: usize,
) -> Vec<Vec<String>> {
    let mut groups = HashMap::<usize, Vec<String>>::new();
    for field in fields {
        let (Some(offset), Some(size)) = (field.offset, field.estimated_size) else {
            continue;
        };
        let last = offset.saturating_add(size.max(1) - 1) / cache_line_size;
        for line in offset / cache_line_size..=last {
            groups.entry(line).or_default().push(field.name.clone());
        }
    }
    let mut groups = groups.into_iter().collect::<Vec<_>>();
    groups.sort_by_key(|(line, _)| *line);
    groups.into_iter().map(|(_, fields)| fields).collect()
}

fn apply_access_facts(
    facts: &[CompilerAccessFact],
    records: &[CppStructInfo],
    evidence: &mut [CppEvidenceSet],
) -> usize {
    let mut applied = 0usize;
    for fact in facts {
        let candidates = records
            .iter()
            .enumerate()
            .filter(|(_, record)| {
                fact.record_name == record.name || fact.record_name == record.qualified_name
            })
            .collect::<Vec<_>>();
        if candidates.len() != 1 {
            continue;
        }
        let (record_index, record) = candidates[0];
        if !record
            .fields
            .iter()
            .any(|field| field.name == fact.field_name)
        {
            continue;
        }
        let Some(access_kind) = parse_access_kind(&fact.access_kind) else {
            continue;
        };
        let set = &mut evidence[record_index];
        set.items.retain(|item| {
            !(item.field_name.as_deref() == Some(fact.field_name.as_str())
                && item.file == fact.file
                && item.line == fact.line
                && item.access_kind.is_some())
        });
        set.push_item(CppEvidenceItem {
            element_member_path: Vec::new(),
            object_identity: None,
            execution_identity: None,
            concurrent_call_path: Vec::new(),
            kind: CppEvidenceKind::CompilerSemanticAccess,
            access_kind: Some(access_kind),
            field_name: Some(fact.field_name.clone()),
            hotness_score: 1.0,
            in_concurrent_context: fact.in_concurrent_context,
            through_shared_indirection: fact.through_shared_indirection,
            through_raw_pointer: fact.through_raw_pointer,
            through_thread_local: fact.through_thread_local,
            through_nonescaping_local: fact.through_nonescaping_local,
            through_automatic_receiver: false,
            guard_ids: fact.guard_ids.clone(),
            initialization_phase: fact.initialization_phase,
            in_record_constructor: false,
            function_name: fact.function_name.clone(),
            description: format!(
                "compiler-confirmed {} access to '{}.{}' at {}:{}",
                fact.access_kind, record.name, fact.field_name, fact.file, fact.line
            ),
            file: fact.file.clone(),
            line: fact.line,
        });
        applied += 1;
    }
    applied
}

fn parse_access_kind(kind: &str) -> Option<CppAccessKind> {
    match kind {
        "read" => Some(CppAccessKind::Read),
        "write" => Some(CppAccessKind::Write),
        "read_modify_write" | "rmw" => Some(CppAccessKind::ReadModifyWrite),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpp_detection::layout::collect_cpp_structs;
    use crate::cpp_detection::parser::parse_cpp_files;
    use crate::cpp_detection::types::CppFile;
    #[cfg(unix)]
    use std::fs;
    #[cfg(unix)]
    use std::os::unix::fs::PermissionsExt;

    fn record(source: &str) -> CppStructInfo {
        let files = parse_cpp_files(vec![CppFile {
            path: "candidate.cpp".to_string(),
            source: source.to_string(),
        }]);
        collect_cpp_structs(&files, "test", 64).remove(0)
    }

    #[test]
    fn compiler_layout_is_exact_only_when_variants_agree() {
        let mut records = vec![record("struct Counters { int left; int right; };")];
        let layout = CompilerRecordLayout {
            name: "Counters".to_string(),
            canonical_type: Some("Counters".to_string()),
            file: None,
            build_variant: Some("debug".to_string()),
            authoritative: true,
            size: 128,
            alignment: 64,
            packed: false,
            fields: vec![
                CompilerFieldLayout {
                    name: "left".to_string(),
                    offset: 0,
                    size: 4,
                },
                CompilerFieldLayout {
                    name: "right".to_string(),
                    offset: 64,
                    size: 4,
                },
            ],
        };
        assert_eq!(
            apply_record_layouts(std::slice::from_ref(&layout), &mut records, 64),
            1
        );
        assert!(records[0].compiler_layout_exact);
        assert!(records[0].is_cache_aligned);
        assert_eq!(records[0].cache_line_groups.len(), 2);

        let mut records = vec![record("struct Counters { int left; int right; };")];
        let mut release = layout.clone();
        release.build_variant = Some("release".to_string());
        release.fields[1].offset = 4;
        assert_eq!(
            apply_record_layouts(&[layout, release], &mut records, 64),
            0
        );
        assert!(!records[0].compiler_layout_exact);
    }

    #[test]
    fn inferred_layout_never_replaces_the_source_layout() {
        let mut records = vec![record("struct Counters { int left; int right; };")];
        let layout = CompilerRecordLayout {
            name: "Counters".to_string(),
            canonical_type: Some("Counters".to_string()),
            file: None,
            build_variant: Some("inferred-candidate-tu".to_string()),
            authoritative: false,
            size: 128,
            alignment: 64,
            packed: false,
            fields: vec![
                CompilerFieldLayout {
                    name: "left".to_string(),
                    offset: 0,
                    size: 4,
                },
                CompilerFieldLayout {
                    name: "right".to_string(),
                    offset: 64,
                    size: 4,
                },
            ],
        };

        assert_eq!(apply_record_layouts(&[layout], &mut records, 64), 0);
        assert!(!records[0].compiler_layout_exact);
        assert_ne!(records[0].fields[1].offset, Some(64));
    }

    #[test]
    fn compiler_access_replaces_a_source_misclassification() {
        let records = vec![record("struct Counters { int value; };")];
        let mut evidence = vec![CppEvidenceSet::default()];
        evidence[0].push_item(CppEvidenceItem {
            element_member_path: Vec::new(),
            object_identity: None,
            execution_identity: None,
            concurrent_call_path: Vec::new(),
            kind: CppEvidenceKind::HotScalarWrite,
            access_kind: Some(CppAccessKind::Write),
            field_name: Some("value".to_string()),
            hotness_score: 1.0,
            in_concurrent_context: false,
            through_shared_indirection: false,
            through_raw_pointer: false,
            through_thread_local: false,
            through_nonescaping_local: false,
            through_automatic_receiver: false,
            guard_ids: Vec::new(),
            initialization_phase: false,
            in_record_constructor: false,
            function_name: None,
            description: "source guess".to_string(),
            file: "candidate.cpp".to_string(),
            line: 2,
        });
        let facts = [CompilerAccessFact {
            record_name: "Counters".to_string(),
            field_name: "value".to_string(),
            file: "candidate.cpp".to_string(),
            line: 2,
            access_kind: "read".to_string(),
            function_name: Some("read".to_string()),
            in_concurrent_context: false,
            through_shared_indirection: false,
            through_raw_pointer: false,
            through_thread_local: false,
            through_nonescaping_local: false,
            guard_ids: Vec::new(),
            initialization_phase: false,
        }];
        assert_eq!(apply_access_facts(&facts, &records, &mut evidence), 1);
        assert_eq!(evidence[0].items.len(), 1);
        assert_eq!(evidence[0].items[0].access_kind, Some(CppAccessKind::Read));
        assert_eq!(
            evidence[0].items[0].kind,
            CppEvidenceKind::CompilerSemanticAccess
        );
    }

    #[cfg(unix)]
    #[test]
    fn sidecar_process_uses_the_versioned_protocol() {
        let root = tempfile::tempdir().expect("create temporary project");
        let sidecar = root.path().join("sidecar.sh");
        fs::write(
            &sidecar,
            format!(
                "#!/bin/sh\ncat >/dev/null\nprintf '%s' '{{\"schema_version\":\"{}\",\"records\":[],\"accesses\":[]}}'\n",
                CPP_SIDECAR_SCHEMA_VERSION
            ),
        )
        .expect("write fake sidecar");
        let mut permissions = fs::metadata(&sidecar)
            .expect("sidecar metadata")
            .permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&sidecar, permissions).expect("make sidecar executable");
        let command = CppCompileCommand {
            directory: root.path().to_string_lossy().into_owned(),
            file: root
                .path()
                .join("candidate.cpp")
                .to_string_lossy()
                .into_owned(),
            compiler: "clang++".to_string(),
            arguments: vec!["clang++".to_string(), "candidate.cpp".to_string()],
            semantic_arguments: Vec::new(),
            command_hash: "hash".to_string(),
            variant_id: "variant".to_string(),
        };
        let facts = run_compiler_sidecar(&sidecar, root.path(), 64, &[command], &[], &[])
            .expect("run fake sidecar");
        assert_eq!(facts.schema_version, CPP_SIDECAR_SCHEMA_VERSION);
    }
}
