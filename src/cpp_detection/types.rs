use std::collections::{HashMap, HashSet};

use crate::types::{AnalysisDiagnostic, ItemVisibility, UsageLocation};
use serde::Serialize;

pub const CPP_CACHE_LINE_SIZE: usize = 64;
const MAX_EVIDENCE_ITEMS_PER_RECORD: usize = 64;
const MAX_API_ITEMS_PER_RECORD: usize = 16;
const MAX_EVIDENCE_DESCRIPTIONS: usize = 16;
const MAX_OMITTED_ACCESS_ROLES: usize = 1024;

#[derive(Debug, Clone)]
pub struct CppProject {
    pub name: String,
    pub files: Vec<CppFile>,
    pub has_compile_commands: bool,
    pub has_cmake: bool,
    /// Build variants recovered from compile_commands.json.  The source-only
    /// frontend may ignore these, while compiler/IR sidecars consume their
    /// normalized semantic arguments and stable variant identity.
    pub compile_commands: Vec<CppCompileCommand>,
    pub diagnostics: Vec<AnalysisDiagnostic>,
}

#[derive(Debug, Clone, Serialize)]
pub struct CppCompileCommand {
    pub directory: String,
    pub file: String,
    pub compiler: String,
    pub arguments: Vec<String>,
    pub semantic_arguments: Vec<String>,
    pub command_hash: String,
    pub variant_id: String,
}

#[derive(Debug, Clone)]
pub struct CppFile {
    pub path: String,
    pub source: String,
}

#[derive(Debug, Clone)]
pub struct CppStructInfo {
    pub name: String,
    /// Namespace-qualified identity used for reporting and root-cause keys.
    pub qualified_name: String,
    pub kind: CppRecordKind,
    pub file: String,
    pub line: usize,
    pub project_name: String,
    pub cache_line_size: usize,
    pub fields: Vec<CppFieldInfo>,
    /// Static data members are not part of an object instance layout. They are
    /// retained separately for static_data static-storage analysis.
    pub static_fields: Vec<CppFieldInfo>,
    pub align_bytes: Option<usize>,
    pub is_cache_aligned: bool,
    pub is_packed: bool,
    pub has_cache_padding: bool,
    pub has_base_classes: bool,
    pub has_no_unique_address: bool,
    /// Source-established order of ordinary, non-overlapping own members.
    /// This does not establish offsets, base layout, or complete object size.
    pub ordered_own_fields: bool,
    pub visibility: ItemVisibility,
    pub public_fields: Vec<String>,
    pub public_methods: Vec<String>,
    pub atomic_fields: Vec<String>,
    pub hot_scalar_fields: Vec<String>,
    pub hot_sync_fields: Vec<String>,
    pub total_estimated_size: Option<usize>,
    pub cache_line_groups: Vec<Vec<String>>,
    pub cache_line_groups_precise: bool,
    /// True only when the compiler sidecar returned a complete target-specific
    /// layout for this exact build variant.
    pub compiler_layout_exact: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CppRecordKind {
    Struct,
    Class,
}

#[derive(Debug, Clone)]
pub struct CppFieldInfo {
    pub name: String,
    /// Non-zero-width bit-fields in one uninterrupted declaration sequence
    /// denote one memory location, irrespective of their distinct names.
    /// None means a regular member or an unresolved sequence/width.
    pub bitfield_group: Option<usize>,
    pub ty_str: String,
    pub line: usize,
    pub estimated_size: Option<usize>,
    pub offset: Option<usize>,
    pub is_atomic: bool,
    pub is_hot_scalar: bool,
    pub is_hot_sync: bool,
    pub is_cache_padded: bool,
    pub is_manual_padding: bool,
    pub is_indirect: bool,
    pub is_array: bool,
    pub is_static: bool,
    pub array_len: Option<usize>,
    pub element_type: Option<String>,
    /// Source-level thread-safety annotation such as GUARDED_BY(mutex).
    /// This is only an exclusion for same-object candidates when the same guard
    /// covers the complete candidate pair.
    pub guarded_by: Option<String>,
    pub visibility: ItemVisibility,
}

/// The object owns a separate contiguous allocation, not inline element bytes.
/// Unknown aliases/containers are not enough to assert this storage domain.
pub(crate) fn has_contiguous_elements(field: &CppFieldInfo) -> bool {
    let mut depth = 0usize;
    for ch in field.ty_str.chars() {
        match ch {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            '*' | '&' if depth == 0 => return false,
            _ => {}
        }
    }
    if field.is_array {
        return true;
    }
    field.ty_str.split('<').next().is_some_and(|base| {
        matches!(
            base.split(|ch: char| !ch.is_alphanumeric() && ch != '_')
                .rfind(|token| !token.is_empty()),
            Some(
                "vector"
                    | "array"
                    | "span"
                    | "FixedArray"
                    | "small_vector"
                    | "SmallVector"
                    | "View"
            )
        )
    })
}

/// A source-bound self access and the runtime entry points that can reach it.
/// Empty entries mean only lifecycle roots or unreachable private helpers in
/// the bounded, fully resolved member graph. This is default report policy,
/// not a whole-program proof of exclusive ownership.
#[derive(Debug, Clone)]
pub struct CppMethodRole {
    pub file: String,
    pub function: String,
    pub line: usize,
    pub field: String,
    pub entries: Vec<String>,
}

#[derive(Debug, Clone, Default)]
pub struct CppEvidenceSet {
    pub method_roles: Vec<CppMethodRole>,
    pub items: Vec<CppEvidenceItem>,
    pub api_items: Vec<CppApiEvidence>,
    pub truncated_items: usize,
    pub truncated_api_items: usize,
    /// Negative information only: these memberships may veto an incomplete
    /// callable partition, but never supply a conflict or concurrency witness.
    pub omitted_access_roles: Vec<CppOmittedAccessRole>,
    pub omitted_access_roles_overflow: bool,
}

#[derive(Debug, Clone)]
pub struct CppOmittedAccessRole {
    pub file: String,
    pub function: String,
    pub field: String,
    pub written: bool,
    pub runtime_entries: Vec<String>,
}

impl CppEvidenceSet {
    pub fn push_item(&mut self, item: CppEvidenceItem) {
        if self.items.iter().any(|existing| {
            existing.kind == item.kind
                && existing.access_kind == item.access_kind
                && existing.field_name == item.field_name
                && existing.element_member_path == item.element_member_path
                && existing.file == item.file
                && existing.line == item.line
                && evidence_role(existing) == evidence_role(&item)
        }) {
            return;
        }
        if self.items.len() < MAX_EVIDENCE_ITEMS_PER_RECORD {
            self.items.push(item);
            return;
        }

        self.truncated_items = self.truncated_items.saturating_add(1);

        // Repeated hot writes must not crowd out a peer's sole read, a
        // different function partition, or an unguarded runtime access. The
        // evidence cap is a presentation/resource budget, not a proof that
        // omitted access roles do not exist.
        let incoming_role = evidence_role(&item);
        let incoming_field_role = evidence_field_role(&item);
        let mut counts = HashMap::new();
        let mut field_counts = HashMap::new();
        for existing in &self.items {
            *counts.entry(evidence_role(existing)).or_insert(0usize) += 1;
            *field_counts
                .entry(evidence_field_role(existing))
                .or_insert(0usize) += 1;
        }
        let new_role = !counts.contains_key(&incoming_role);
        let new_field_role = !field_counts.contains_key(&incoming_field_role);
        let replacement = self
            .items
            .iter()
            .enumerate()
            .filter(|(_, existing)| {
                if new_field_role {
                    field_counts[&evidence_field_role(existing)] > 1
                } else if new_role {
                    counts[&evidence_role(existing)] > 1
                } else {
                    evidence_role(existing) == incoming_role
                }
            })
            .min_by_key(|(_, existing)| evidence_rank(existing))
            .or_else(|| {
                new_role.then(|| {
                    self.items
                        .iter()
                        .enumerate()
                        .filter(|(_, existing)| {
                            new_field_role || evidence_field_role(existing) == incoming_field_role
                        })
                        .min_by_key(|(_, existing)| evidence_rank(existing))
                        .expect("the evidence budget is full")
                })
            });
        if let Some((idx, existing)) = replacement {
            let redundant = counts[&evidence_role(existing)] > 1;
            let field_redundant = field_counts[&evidence_field_role(existing)] > 1;
            if (new_field_role && field_redundant)
                || (new_role && redundant)
                || evidence_rank(&item) > evidence_rank(existing)
            {
                let omitted = std::mem::replace(&mut self.items[idx], item);
                self.remember_omitted_access(&omitted);
                return;
            }
        }
        self.remember_omitted_access(&item);
    }

    fn remember_omitted_access(&mut self, item: &CppEvidenceItem) {
        if item.initialization_phase
            || item.through_thread_local
            || item.through_nonescaping_local
            || item.through_automatic_receiver
            || item.kind == CppEvidenceKind::ContiguousElementAccess
        {
            return;
        }
        let (Some(function), Some(field), Some(kind)) =
            (&item.function_name, &item.field_name, &item.access_kind)
        else {
            return;
        };
        let written = matches!(kind, CppAccessKind::Write | CppAccessKind::ReadModifyWrite);
        if let Some(role) = self.omitted_access_roles.iter_mut().find(|role| {
            role.file == item.file && role.function == *function && role.field == *field
        }) {
            role.written |= written;
        } else if self.omitted_access_roles.len() < MAX_OMITTED_ACCESS_ROLES {
            self.omitted_access_roles.push(CppOmittedAccessRole {
                file: item.file.clone(),
                function: function.clone(),
                field: field.clone(),
                written,
                runtime_entries: Vec::new(),
            });
        } else {
            self.omitted_access_roles_overflow = true;
        }
    }

    pub fn push_api_item(&mut self, item: CppApiEvidence) {
        if self.api_items.iter().any(|existing| {
            existing.description == item.description
                && existing.file == item.file
                && existing.line == item.line
        }) {
            return;
        }
        if self.api_items.len() < MAX_API_ITEMS_PER_RECORD {
            self.api_items.push(item);
            return;
        }

        self.truncated_api_items = self.truncated_api_items.saturating_add(1);

        if let Some((weakest_idx, weakest_score)) = self
            .api_items
            .iter()
            .enumerate()
            .map(|(idx, existing)| (idx, existing.score))
            .min_by(|(_, left), (_, right)| left.total_cmp(right))
            && item.score > weakest_score
        {
            self.api_items[weakest_idx] = item;
        }
    }

    pub fn has_evidence(&self) -> bool {
        !self.items.is_empty()
    }

    pub fn has_api_signal(&self) -> bool {
        !self.api_items.is_empty()
    }

    pub fn descriptions(&self) -> Vec<String> {
        unique_strings(
            self.items
                .iter()
                .map(|item| item.description.clone())
                .chain(self.api_items.iter().map(|item| item.description.clone())),
        )
    }

    pub fn concurrency_descriptions(&self) -> Vec<String> {
        unique_strings(self.items.iter().map(|item| item.description.clone()))
    }

    pub fn usage_locations(&self) -> Vec<UsageLocation> {
        self.items
            .iter()
            .map(|item| UsageLocation {
                file: item.file.clone(),
                line: item.line,
                description: item.description.clone(),
            })
            .chain(self.api_items.iter().map(|item| UsageLocation {
                file: item.file.clone(),
                line: item.line,
                description: item.description.clone(),
            }))
            .collect()
    }

    pub fn has_concurrency_signal(&self) -> bool {
        self.items.iter().any(|item| {
            matches!(
                item.kind,
                CppEvidenceKind::ThreadSpawn
                    | CppEvidenceKind::OpenMp
                    | CppEvidenceKind::ParallelLibrary
                    | CppEvidenceKind::SharedOwnership
                    | CppEvidenceKind::ConcurrentFieldAccess
            ) || item.in_concurrent_context
        })
    }

    pub fn has_strong_parallel_signal(&self) -> bool {
        self.items.iter().any(|item| {
            item.in_concurrent_context
                || matches!(
                    item.kind,
                    CppEvidenceKind::ThreadSpawn
                        | CppEvidenceKind::OpenMp
                        | CppEvidenceKind::ParallelLibrary
                        | CppEvidenceKind::ConcurrentFieldAccess
                )
        })
    }

    pub fn has_shared_ownership_signal(&self) -> bool {
        self.items
            .iter()
            .any(|item| item.kind == CppEvidenceKind::SharedOwnership)
    }

    pub fn has_lock_signal(&self) -> bool {
        self.items
            .iter()
            .any(|item| item.kind == CppEvidenceKind::LockProtected)
    }

    pub fn has_contiguous_object_storage(&self) -> bool {
        self.items.iter().any(|item| {
            item.kind == CppEvidenceKind::ContiguousObjectStorage
                && !item.through_nonescaping_local
                && !item.through_thread_local
        })
    }

    pub fn has_allocator_object_storage(&self) -> bool {
        self.items
            .iter()
            .any(|item| item.kind == CppEvidenceKind::AllocatorObjectStorage)
    }

    pub fn max_hotness(&self) -> f32 {
        self.items
            .iter()
            .map(|item| item.hotness_score)
            .fold(0.0, f32::max)
    }

    pub fn max_api_score(&self) -> f32 {
        self.api_items
            .iter()
            .map(|item| item.score)
            .fold(0.0, f32::max)
    }

    pub fn written_fields_matching(&self, candidates: &[String]) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.items
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                )
            })
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }

    pub fn concurrent_written_fields_matching(&self, candidates: &[String]) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.items
            .iter()
            .filter(|item| item.in_concurrent_context)
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                )
            })
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }

    pub fn accessed_fields_matching(&self, candidates: &[String]) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.items
            .iter()
            .filter(|item| item.access_kind.is_some())
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }

    pub fn concurrent_accessed_fields_matching(&self, candidates: &[String]) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.items
            .iter()
            .filter(|item| item.in_concurrent_context && item.access_kind.is_some())
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }

    pub fn hot_written_fields_matching(
        &self,
        candidates: &[String],
        min_hotness: f32,
    ) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.items
            .iter()
            .filter(|item| item.hotness_score >= min_hotness)
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(CppAccessKind::Write | CppAccessKind::ReadModifyWrite)
                )
            })
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }

    pub fn read_fields_matching(&self, candidates: &[String]) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.items
            .iter()
            .filter(|item| matches!(item.access_kind, Some(CppAccessKind::Read)))
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }
}

fn unique_strings(values: impl Iterator<Item = String>) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for value in values {
        if seen.insert(value.clone()) {
            out.push(value);
            if out.len() == MAX_EVIDENCE_DESCRIPTIONS {
                break;
            }
        }
    }
    out
}

fn evidence_rank(item: &CppEvidenceItem) -> u32 {
    let concurrent = u32::from(item.in_concurrent_context) * 100;
    let mutation = match item.access_kind {
        Some(CppAccessKind::ReadModifyWrite) => 30,
        Some(CppAccessKind::Write) => 20,
        Some(CppAccessKind::Read) => 5,
        None => 0,
    };
    let semantic = match item.kind {
        CppEvidenceKind::ConcurrentFieldAccess
        | CppEvidenceKind::ThreadSpawn
        | CppEvidenceKind::OpenMp
        | CppEvidenceKind::ParallelLibrary
        | CppEvidenceKind::CompilerSemanticAccess
        | CppEvidenceKind::InlineMemberAccess
        | CppEvidenceKind::ContiguousElementAccess => 20,
        CppEvidenceKind::AtomicFieldOps | CppEvidenceKind::SharedOwnership => 10,
        CppEvidenceKind::ContiguousObjectStorage | CppEvidenceKind::AllocatorObjectStorage => 5,
        CppEvidenceKind::HotScalarWrite
        | CppEvidenceKind::LockProtected
        | CppEvidenceKind::LoopHotness => 0,
    };
    concurrent + mutation + semantic + item.hotness_score.min(100.0) as u32
}

#[derive(PartialEq, Eq, Hash)]
struct EvidenceFieldRole<'a> {
    field: Option<&'a str>,
    access: Option<&'a CppAccessKind>,
    // HotScalarWrite and LoopHotness can describe the same memory access.
    // Non-access evidence still needs its distinct topology/concurrency role.
    non_access_kind: Option<&'a CppEvidenceKind>,
    heap_element: bool,
    initialization: bool,
    construction: bool,
    thread_local: bool,
    nonescaping_local: bool,
    automatic_receiver: bool,
    guarded: bool,
}

#[derive(PartialEq, Eq, Hash)]
struct EvidenceRole<'a> {
    field: EvidenceFieldRole<'a>,
    function: Option<&'a str>,
    concurrent: bool,
    shared: bool,
    raw_pointer: bool,
    guards: &'a [String],
}

fn evidence_field_role(item: &CppEvidenceItem) -> EvidenceFieldRole<'_> {
    EvidenceFieldRole {
        field: item.field_name.as_deref(),
        access: item.access_kind.as_ref(),
        non_access_kind: item.access_kind.is_none().then_some(&item.kind),
        heap_element: item.kind == CppEvidenceKind::ContiguousElementAccess,
        initialization: item.initialization_phase,
        construction: item.in_record_constructor,
        thread_local: item.through_thread_local,
        nonescaping_local: item.through_nonescaping_local,
        automatic_receiver: item.through_automatic_receiver,
        guarded: !item.guard_ids.is_empty(),
    }
}

fn evidence_role(item: &CppEvidenceItem) -> EvidenceRole<'_> {
    EvidenceRole {
        field: evidence_field_role(item),
        function: item.function_name.as_deref(),
        concurrent: item.in_concurrent_context,
        shared: item.through_shared_indirection,
        raw_pointer: item.through_raw_pointer,
        guards: &item.guard_ids,
    }
}

#[derive(Debug, Clone)]
pub struct CppEvidenceItem {
    /// Resolved inline members inside a contiguous element. The owning field
    /// remains the storage identity; these are projections, not pointer slots.
    pub element_member_path: Vec<String>,
    pub kind: CppEvidenceKind,
    pub access_kind: Option<CppAccessKind>,
    pub field_name: Option<String>,
    pub hotness_score: f32,
    pub in_concurrent_context: bool,
    pub through_shared_indirection: bool,
    pub through_raw_pointer: bool,
    /// The concrete receiver/storage is declared thread_local/__thread.  Such
    /// accesses belong to distinct per-thread instances and cannot establish
    /// MHP for a same-instance candidate pair by themselves.
    pub through_thread_local: bool,
    /// The concrete receiver is a function-local value (or locally created
    /// unique owner) whose address/value is not returned, captured, passed to
    /// another call, or registered with a worker API in the analyzed source.
    pub through_nonescaping_local: bool,
    /// Access within the callable owning an automatic value, including when
    /// escape is unresolved. This is weaker than a nonescape proof and only
    /// downgrades default same-object reportability, not the may-risk theory.
    pub through_automatic_receiver: bool,
    /// Concrete scalar lock expressions held at this access. Indexed lock
    /// expressions are deliberately excluded because `locks[i]` and
    /// `locks[j]` do not serialize a candidate pair.
    pub guard_ids: Vec<String>,
    /// The access is to the unpublished receiver being constructed, or lies
    /// in a source-proved fresh-allocation range before alias/publication.
    /// This does not exclude writes on adjacent, separately owned instances.
    pub initialization_phase: bool,
    /// AST-bound constructor owner is the accessed record. This includes
    /// accesses to an existing source object and does not imply freshness.
    pub in_record_constructor: bool,
    pub function_name: Option<String>,
    /// Receiver-bound concurrency propagation; empty for direct accesses.
    pub concurrent_call_path: Vec<String>,
    pub description: String,
    pub file: String,
    pub line: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CppEvidenceKind {
    AtomicFieldOps,
    HotScalarWrite,
    ThreadSpawn,
    OpenMp,
    ParallelLibrary,
    SharedOwnership,
    ConcurrentFieldAccess,
    CompilerSemanticAccess,
    /// Receiver-bound effect recovered from an inline member method body.
    InlineMemberAccess,
    /// Access to an element in a field's separately allocated contiguous
    /// payload, not a read/write of the owning vector's control block.
    ContiguousElementAccess,
    LockProtected,
    LoopHotness,
    /// The record is instantiated in an array/vector-like contiguous storage
    /// topology containing multiple logical objects.
    ContiguousObjectStorage,
    /// The record has a heap/allocation site that may create multiple live
    /// allocator-managed objects.  This is weaker than contiguous storage but
    /// is a required source witness for allocator-object rules.
    AllocatorObjectStorage,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CppAccessKind {
    Read,
    Write,
    ReadModifyWrite,
}

#[derive(Debug, Clone)]
pub struct CppApiEvidence {
    pub description: String,
    pub file: String,
    pub line: usize,
    pub score: f32,
}

#[derive(Debug, Clone)]
pub struct IndexedWriteCandidate {
    pub file: String,
    pub line: usize,
    pub snippet: String,
    /// Enclosing callable at the concrete mutation site.  Function-level
    /// ground truth must not be forced to fall back to a storage declaration
    /// symbol merely because the candidate was produced by an array rule.
    pub function_name: Option<String>,
    /// Record whose adjacent instances/fields form the root cause, when the
    /// bounded interprocedural analysis can resolve it.
    pub record_name: Option<String>,
    pub record_line: Option<usize>,
    /// A different inline field in the next worker-owned record. This is an
    /// adjacent-object boundary, not two elements of one worker's array.
    pub record_peer: Option<CppIndexedPeerAccess>,
    /// Concrete array passed to the worker whose record fields are accessed.
    pub record_storage: Option<String>,
    pub field_name: Option<String>,
    /// User-visible alias bound to the partitioned element/region.  Keeping
    /// both names lets reports identify the backing storage and the mutation
    /// name without conflating the two data-flow roles.
    pub alias_name: Option<String>,
    /// Source-derived access kind for the indexed target.  Candidate
    /// collection must identify the mutation on the indexed expression itself;
    /// an unrelated assignment elsewhere on the line is not sufficient.
    pub access_kind: CppAccessKind,
    /// The index is derived directly from a thread/worker/slot partition (or
    /// from an equivalent bounded worker-flow proof), rather than merely
    /// appearing near a parallel construct.
    pub has_direct_partition_evidence: bool,
    /// A runtime thread identity or an observed concurrent execution region.
    /// Caller-selected API partitions remain potential external concurrency.
    pub access_in_concurrent_context: bool,
    /// Scalar locks held by the indexed mutation. A common scalar lock across
    /// the dynamic site serializes all selected elements; indexed locks are
    /// intentionally not represented here.
    pub guard_ids: Vec<String>,
    pub evidence: Vec<String>,
    /// Unambiguous declaration-bound storage identity for cross-file
    /// occurrence clustering.
    pub storage_identity: Option<String>,
}

#[derive(Debug, Clone)]
pub struct AtomicAliasArrayCandidate {
    pub file: String,
    pub line: usize,
    pub alias: String,
    pub storage_name: String,
    pub snippet: String,
    pub access_file: Option<String>,
    pub access_line: Option<usize>,
    pub access_kind: Option<CppAccessKind>,
    pub access_in_concurrent_context: bool,
    /// A public/non-const indexed accessor returns a mutable reference to an
    /// element. This is a write capability even when the caller is external.
    pub access_is_mutable_api: bool,
    pub guard_ids: Vec<String>,
    pub evidence: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct StaticHotStateCandidate {
    pub file: String,
    pub line: usize,
    pub snippet: String,
    pub field_name: Option<String>,
    pub is_array_like: bool,
    /// File/namespace-scope storage can participate in a sibling-array group;
    /// class-static members stay on their existing single-candidate path.
    pub is_file_scope: bool,
    /// Generic mutable arrays are retained for sibling grouping but are not
    /// emitted as standalone hot-state findings without a domain-specific
    /// signal.
    pub is_generic_array: bool,
    pub access_file: Option<String>,
    pub access_line: Option<usize>,
    pub access_index: Option<String>,
    pub access_function: Option<String>,
    pub access_kind: Option<CppAccessKind>,
    pub access_in_concurrent_context: bool,
    pub has_partitioned_index_evidence: bool,
    pub guard_ids: Vec<String>,
    pub evidence: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct CppIndexedPeerAccess {
    pub field: String,
    pub line: usize,
    pub kind: CppAccessKind,
    pub guard_ids: Vec<String>,
}
