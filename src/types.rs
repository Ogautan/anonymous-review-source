use clap::ValueEnum;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

pub const REPORT_SCHEMA_VERSION: &str = "false-sharing-static-report/v5";
pub const DETECTOR_VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Severity {
    High,
    Medium,
    Low,
}

/// Public rules classify the storage relation of the actual access pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, ValueEnum)]
#[serde(rename_all = "snake_case")]
#[clap(rename_all = "snake_case")]
pub enum RuleId {
    SameObjectFields,
    ContiguousElements,
    IndependentAllocations,
    IndependentStatics,
}

impl RuleId {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::SameObjectFields => "same_object_fields",
            Self::ContiguousElements => "contiguous_elements",
            Self::IndependentAllocations => "independent_allocations",
            Self::IndependentStatics => "independent_statics",
        }
    }
}

impl std::fmt::Display for RuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

pub const ALL_RULES: [RuleId; 4] = [
    RuleId::SameObjectFields,
    RuleId::ContiguousElements,
    RuleId::IndependentAllocations,
    RuleId::IndependentStatics,
];

/// Discovery provenance, not independently selectable public rules.
/// Several discovery methods can produce the same storage relation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CandidateKind {
    FieldGroup,
    ContainerElements,
    WriterNeighbor,
    ObjectInstances,
    StaticData,
    IndexedWrites,
    AtomicArray,
    SiblingArrays,
    MixedFields,
    SeparateAllocations,
}

impl CandidateKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::FieldGroup => "field_group",
            Self::ContainerElements => "container_elements",
            Self::WriterNeighbor => "writer_neighbor",
            Self::ObjectInstances => "object_instances",
            Self::StaticData => "static_data",
            Self::IndexedWrites => "indexed_writes",
            Self::AtomicArray => "atomic_array",
            Self::SiblingArrays => "sibling_arrays",
            Self::MixedFields => "mixed_fields",
            Self::SeparateAllocations => "separate_allocations",
        }
    }

    /// Preserve existing finding identities across the reporting migration.
    /// These historical salts are never used to select or classify a rule.
    pub(crate) fn identity_salt(self) -> &'static str {
        match self {
            Self::FieldGroup => "FS001",
            Self::ContainerElements => "FS002",
            Self::WriterNeighbor => "FS003",
            Self::ObjectInstances => "FS004",
            Self::StaticData => "FS005",
            Self::IndexedWrites => "FS006",
            Self::AtomicArray => "FS007",
            Self::SiblingArrays => "FS008",
            Self::MixedFields => "FS009",
            Self::SeparateAllocations => "FS010",
        }
    }

    pub fn supports(self, rule: RuleId) -> bool {
        match self {
            Self::FieldGroup | Self::WriterNeighbor | Self::MixedFields => {
                rule == RuleId::SameObjectFields
            }
            Self::ContainerElements
            | Self::IndexedWrites
            | Self::AtomicArray
            | Self::SiblingArrays => rule == RuleId::ContiguousElements,
            Self::ObjectInstances => matches!(
                rule,
                RuleId::ContiguousElements | RuleId::IndependentAllocations
            ),
            Self::StaticData => matches!(
                rule,
                RuleId::ContiguousElements | RuleId::IndependentStatics
            ),
            Self::SeparateAllocations => rule == RuleId::IndependentAllocations,
        }
    }
}

impl std::fmt::Display for CandidateKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl PartialEq<&str> for CandidateKind {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

/// Analysis components that can be removed for controlled evaluation.
///
/// These switches are not intended as user-facing detector tuning knobs.  They
/// define the leave-one-component-out configurations used by the paper
/// artifact, while preserving the same parser, rule set, and output schema.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, ValueEnum)]
#[serde(rename_all = "snake_case")]
#[clap(rename_all = "snake_case")]
pub enum AblationComponent {
    Layout,
    Write,
    MayParallel,
    Hotness,
    Api,
    Protection,
}

impl AblationComponent {
    pub fn as_str(self) -> &'static str {
        match self {
            AblationComponent::Layout => "layout",
            AblationComponent::Write => "write",
            AblationComponent::MayParallel => "may_parallel",
            AblationComponent::Hotness => "hotness",
            AblationComponent::Api => "api",
            AblationComponent::Protection => "protection",
        }
    }
}

pub const ALL_ABLATION_COMPONENTS: [AblationComponent; 6] = [
    AblationComponent::Layout,
    AblationComponent::Write,
    AblationComponent::MayParallel,
    AblationComponent::Hotness,
    AblationComponent::Api,
    AblationComponent::Protection,
];

#[derive(Debug, Clone)]
pub struct AnalysisOptions {
    pub enabled_rules: HashSet<RuleId>,
    pub category_filter: Option<RiskCategory>,
    /// Effective cache-line/interference granularity used by layout analysis.
    ///
    /// The CLI restricts this to 32, 64, or 128 bytes. Library callers should
    /// use the same supported values so layout grouping and protection
    /// thresholds remain meaningful.
    pub cache_line_size: usize,
    /// C++ maximum findings returned after ranking. `None` preserves the
    /// complete candidate set for library callers and research evaluation.
    pub max_findings: Option<usize>,
    pub use_rustc_layout: bool,
    /// Propagate Rust function summaries through the bounded call graph.
    ///
    /// This is enabled in normal analysis and exposed separately so the paper
    /// evaluation can measure the contribution of interprocedural evidence.
    pub use_interprocedural_evidence: bool,
    /// Optional compiler semantic sidecar executable for C++. The sidecar
    /// consumes normalized compilation commands and returns exact layout and
    /// compiler-classified access facts over a versioned JSON protocol.
    pub cpp_semantic_sidecar: Option<PathBuf>,
    /// Include weak C++ may-risk candidates lacking actionable concurrency or
    /// storage evidence. Independent of the output-size limit.
    pub cpp_include_speculative: bool,
    /// Components removed in controlled paper-evaluation configurations.
    pub ablated_components: HashSet<AblationComponent>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructKey {
    pub crate_name: String,
    pub module_path: String,
    pub name: String,
}

impl StructKey {
    pub fn new(
        crate_name: impl Into<String>,
        module_path: impl Into<String>,
        name: impl Into<String>,
    ) -> Self {
        Self {
            crate_name: crate_name.into(),
            module_path: module_path.into(),
            name: name.into(),
        }
    }

    pub fn from_struct(si: &StructInfo) -> Self {
        Self::new(
            si.crate_name
                .clone()
                .unwrap_or_else(|| "unknown".to_string()),
            si.module_path.clone(),
            si.name.clone(),
        )
    }

    pub fn qualified_name(&self) -> String {
        if self.module_path.is_empty() {
            self.name.clone()
        } else {
            format!("{}::{}", self.module_path, self.name)
        }
    }
}

impl AnalysisOptions {
    pub fn with_rules(rules: &[RuleId]) -> Self {
        Self {
            enabled_rules: rules.iter().copied().collect(),
            category_filter: None,
            cache_line_size: crate::struct_layout::CACHE_LINE_SIZE,
            max_findings: None,
            use_rustc_layout: false,
            use_interprocedural_evidence: true,
            cpp_semantic_sidecar: None,
            cpp_include_speculative: false,
            ablated_components: HashSet::new(),
        }
    }

    pub fn all_rules() -> Self {
        Self::with_rules(&ALL_RULES)
    }

    pub fn enabled(&self, rule: RuleId) -> bool {
        self.enabled_rules.contains(&rule)
    }

    /// Run every discovery method capable of producing a selected relation.
    /// A second filter uses the recovered relation before grouping.
    pub fn candidate_enabled(&self, kind: CandidateKind) -> bool {
        self.enabled_rules.iter().any(|rule| kind.supports(*rule))
    }

    pub fn enabled_rule_names(&self) -> Vec<&'static str> {
        ALL_RULES
            .iter()
            .filter(|r| self.enabled(**r))
            .map(|r| r.as_str())
            .collect()
    }

    pub fn ablated(&self, component: AblationComponent) -> bool {
        self.ablated_components.contains(&component)
    }

    pub fn ablated_component_names(&self) -> Vec<&'static str> {
        ALL_ABLATION_COMPONENTS
            .iter()
            .filter(|component| self.ablated(**component))
            .map(|component| component.as_str())
            .collect()
    }
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum RiskCategory {
    HotInProject,
    ApiUsageLatent,
    ColdOrConditional,
}

impl std::fmt::Display for RiskCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RiskCategory::HotInProject => write!(f, "hot_in_project"),
            RiskCategory::ApiUsageLatent => write!(f, "api_usage_latent"),
            RiskCategory::ColdOrConditional => write!(f, "cold_or_conditional"),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct LayoutContext {
    pub language: String,
    pub struct_name: String,
    /// Crate/module-qualified type name when the frontend can recover it.
    pub canonical_type: String,
    /// Source declaration line, used to disambiguate same-named records during
    /// clustering and stable group-ID construction.
    pub declaration_line: usize,
    pub cache_line_size: usize,
    pub layout_certainty: String,
    pub fields: Vec<LayoutFieldContext>,
    pub cache_line_groups: Vec<Vec<String>>,
    /// Compiler-backed groups include every phase allowed by object alignment.
    pub cache_line_groups_precise: bool,
    pub repr_c: bool,
    pub repr_rust: bool,
    pub repr_align_bytes: Option<usize>,
    pub repr_packed: bool,
    pub has_cache_padded: bool,
    pub manual_padding_fields: Vec<String>,
    pub total_estimated_size: Option<usize>,
    pub layout_source: String,
    pub used_rustc_layout: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct LayoutFieldContext {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub estimated_size: Option<usize>,
    pub offset: Option<usize>,
    pub range: Option<LayoutByteRange>,
    pub cache_line: Option<usize>,
    pub cache_line_range: Option<LayoutCacheLineRange>,
    pub is_atomic: bool,
    pub is_hot_scalar: bool,
    pub is_hot_sync: bool,
    pub is_cache_padded: bool,
    pub is_manual_padding: bool,
    pub is_indirect: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct LayoutByteRange {
    pub start: usize,
    pub end_exclusive: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct LayoutCacheLineRange {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct Finding {
    pub category: RiskCategory,
    pub rule_id: RuleId,
    pub candidate_kind: CandidateKind,
    /// Additional discovery methods for the same grouped risk.
    pub related_candidate_kinds: Vec<CandidateKind>,
    /// Stable identity of the clustered, reviewable root cause.
    pub finding_group_id: String,
    /// Number of detector occurrences merged into this root-cause group.
    pub finding_occurrence_count: usize,
    pub title: &'static str,
    pub severity: Severity,
    pub file: String,
    pub line: usize,
    pub crate_name: Option<String>,
    pub snippet: String,
    pub suggestion: &'static str,
    pub confidence: f32,
    pub struct_name: Option<String>,
    pub symbol: Option<String>,
    pub field_list: Vec<String>,
    /// A machine-readable witness for the theory-level false-sharing pattern.
    ///
    /// Rust and C++ findings populate this field through language-specific
    /// adapters to the shared false-sharing predicate.
    pub static_pattern: Option<StaticPatternContext>,
    pub layout_context: Option<LayoutContext>,
    pub access_evidence: Vec<AccessEvidenceContext>,
    pub risk_factors: Vec<String>,
    pub concurrency_evidence: Vec<String>,
    pub usage_locations: Vec<UsageLocation>,
    pub finding_hash: String,
    /// Frontend-resolved storage identity used for cross-file clustering.
    /// Access-site evidence remains in `usage_locations`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub storage_identity: Option<String>,
}

impl Finding {
    pub fn has_candidate(&self, kind: CandidateKind) -> bool {
        self.candidate_kind == kind || self.related_candidate_kinds.contains(&kind)
    }
}

/// The access interference induced by two distinct abstract locations.
///
/// `WriteUnknownPeer` means that a writer is known but the access kind of the
/// second location is unresolved.  It is intentionally weaker than inventing
/// a second write from a field name or type name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum AccessPattern {
    WriteWrite,
    WriteRead,
    WriteUnknownPeer,
}

/// How two abstract locations can occupy one coherence block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ColocationPattern {
    SameObjectFields,
    ContiguousElements,
    AdjacentObjects,
    /// Separately allocated objects that may be packed into adjacent allocator
    /// slots.  This differs from `AdjacentObjects`, whose adjacency follows
    /// directly from a language-level contiguous container.
    AllocatorObjects,
    StaticStorage,
}

impl ColocationPattern {
    /// Adjacent object fields refine continuous storage, not a fifth rule.
    pub fn rule_id(self) -> RuleId {
        match self {
            Self::SameObjectFields => RuleId::SameObjectFields,
            Self::ContiguousElements | Self::AdjacentObjects => RuleId::ContiguousElements,
            Self::AllocatorObjects => RuleId::IndependentAllocations,
            Self::StaticStorage => RuleId::IndependentStatics,
        }
    }
}

/// Strength of the static may-happen-in-parallel witness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ParallelismEvidence {
    ConcurrentContext,
    SharedReachability,
    ExternalApiPotential,
    Unresolved,
}

/// Strength of the cache-line co-location witness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ColocationEvidence {
    CompilerExact,
    RepresentationBounded,
    SourceEstimated,
    Symbolic,
}

/// Theory-level witness attached to a static-risk finding.
///
/// The core candidate predicate is the conjunction of `distinct_locations`,
/// `distinct_accesses`, `independently_accessible`, `may_share_cache_line`,
/// `may_happen_in_parallel`, `has_write`, and `protection_excluded`.
/// `repetition_evidence` ranks likely performance significance but is not
/// required for a coherence-conflict may-risk.
#[derive(Debug, Clone, Serialize)]
pub struct StaticPatternContext {
    pub model_version: &'static str,
    pub rule_id: RuleId,
    pub candidate_kind: CandidateKind,
    /// Frontend that established the language-specific facts in this witness.
    pub frontend: &'static str,
    /// Explicit assumptions introduced by that frontend (for example ABI
    /// layout estimates, raw-pointer aliasing, or Rust shared reachability).
    pub language_specific_assumptions: Vec<&'static str>,
    pub access_pattern: AccessPattern,
    pub colocation_pattern: ColocationPattern,
    pub parallelism_evidence: ParallelismEvidence,
    pub colocation_evidence: ColocationEvidence,
    pub distinct_locations: bool,
    /// Two different abstract locations have access witnesses (or the
    /// topology itself denotes distinct indexed/object instances).
    pub distinct_accesses: bool,
    /// The access relation contains at least two separable location roles,
    /// rather than two fields that are always manipulated as one protocol
    /// state. Indexed/object topologies establish this by construction.
    pub independently_accessible: bool,
    pub may_share_cache_line: bool,
    pub may_happen_in_parallel: bool,
    pub has_write: bool,
    pub repetition_evidence: bool,
    pub protection_excluded: bool,
    pub witness_locations: Vec<String>,
}

/// Machine-readable projection of the evidence used by static rules.
///
/// This DTO deliberately contains only language-neutral values so downstream
/// tools do not depend on Rust/C++ analyzer implementation types or prose.
#[derive(Debug, Clone, Serialize)]
pub struct AccessEvidenceContext {
    pub evidence_kind: String,
    pub access_kind: Option<String>,
    pub field_name: Option<String>,
    pub hotness_score: f32,
    pub in_concurrent_context: bool,
    pub access_mode: String,
    pub function_name: Option<String>,
    pub propagation_depth: usize,
    pub call_path: Vec<String>,
    pub semantic_contexts: Vec<String>,
    pub through_shared_indirection: bool,
    pub through_raw_pointer: bool,
    pub file: String,
    pub line: usize,
    pub description: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct UsageLocation {
    pub file: String,
    pub line: usize,
    pub description: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct ReportSummary {
    pub hot_in_project: usize,
    pub api_usage_latent: usize,
    pub cold_or_conditional: usize,
    pub candidate_findings: usize,
    pub suppressed_candidates: usize,
    /// C++ root-cause groups excluded by the evidence/reportability policy,
    /// before the ordinary output-size limit. These are not proven negatives.
    pub cpp_speculative_candidates: usize,
    /// Detector occurrences before root-cause clustering.
    pub finding_occurrence_count: usize,
    /// Reviewable root-cause groups after clustering and filtering.
    pub finding_group_count: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticSeverity {
    Warning,
    Error,
}

/// A structured explanation of work the analyzer could not complete.
///
/// Diagnostics are deliberately part of the JSON report: a successful scan
/// with no findings is materially different from a scan that skipped inputs.
#[derive(Debug, Clone, Serialize)]
pub struct AnalysisDiagnostic {
    pub severity: DiagnosticSeverity,
    pub stage: &'static str,
    pub file: Option<String>,
    pub message: String,
    pub fatal: bool,
}

impl AnalysisDiagnostic {
    pub fn warning(
        stage: &'static str,
        file: Option<impl Into<String>>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            severity: DiagnosticSeverity::Warning,
            stage,
            file: file.map(Into::into),
            message: message.into(),
            fatal: false,
        }
    }

    pub fn fatal(
        stage: &'static str,
        file: Option<impl Into<String>>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            stage,
            file: file.map(Into::into),
            message: message.into(),
            fatal: true,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct Report {
    pub schema_version: &'static str,
    pub detector_version: &'static str,
    pub scanned_files: usize,
    pub scanned_crates: Vec<String>,
    pub enabled_rules: Vec<&'static str>,
    pub ablated_components: Vec<&'static str>,
    /// Effective cache-line/interference granularity used for this run.
    pub cache_line_size: usize,
    /// True when input, parsing, or bounded-analysis failures mean the report
    /// is not a complete account of the requested source set.
    pub analysis_incomplete: bool,
    /// Facts deliberately dropped by bounded analyses.
    pub truncated_facts: usize,
    pub diagnostics: Vec<AnalysisDiagnostic>,
    pub summary: ReportSummary,
    pub findings: Vec<Finding>,
}

impl Report {
    pub fn has_fatal_diagnostics(&self) -> bool {
        self.diagnostics.iter().any(|diagnostic| diagnostic.fatal)
    }
}

// --- Pass 1 data structures ---

#[derive(Debug, Clone)]
pub struct StructInfo {
    pub name: String,
    pub module_path: String,
    pub file: String,
    pub line: usize,
    pub crate_name: Option<String>,
    pub cache_line_size: usize,
    pub fields: Vec<FieldInfo>,
    pub repr_align_bytes: Option<usize>,
    pub repr_align: bool,
    pub repr_packed: bool,
    pub repr_c: bool,
    pub has_cache_padded: bool,
    pub atomic_fields: Vec<String>,
    pub hot_scalar_fields: Vec<String>,
    pub hot_sync_fields: Vec<String>,
    pub total_estimated_size: Option<usize>,
    pub cache_line_groups: Vec<Vec<String>>,
    pub cache_line_groups_precise: bool,
    pub layout_source: LayoutSource,
    pub visibility: ItemVisibility,
    pub public_fields: Vec<String>,
    /// Source-proven failure of Sync; opaque types remain unresolved.
    pub known_not_sync: bool,
    /// API projections of shared field references, not memory-access witnesses.
    pub shared_field_projections: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub name: String,
    pub ty_str: String,
    pub estimated_size: Option<usize>,
    pub offset: Option<usize>,
    pub is_atomic: bool,
    pub is_hot_scalar: bool,
    pub is_hot_sync: bool,
    pub is_cache_padded: bool,
    pub is_manual_padding: bool,
    pub is_indirect: bool,
    pub visibility: ItemVisibility,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LayoutSource {
    RustDefaultEstimate,
    ReprCEstimate,
    RustcExact,
    CppEstimate,
}

impl LayoutSource {
    pub fn as_str(self) -> &'static str {
        match self {
            LayoutSource::RustDefaultEstimate => "rust_default_estimate",
            LayoutSource::ReprCEstimate => "repr_c_estimate",
            LayoutSource::RustcExact => "rustc_exact",
            LayoutSource::CppEstimate => "cpp_estimate",
        }
    }

    pub fn used_rustc_layout(self) -> bool {
        matches!(self, LayoutSource::RustcExact)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ItemVisibility {
    Private,
    Public,
    Restricted,
}

impl ItemVisibility {
    pub fn is_exposed(self) -> bool {
        matches!(self, ItemVisibility::Public | ItemVisibility::Restricted)
    }

    /// Exposed outside the current crate. `pub(crate)`/`pub(super)` are useful
    /// for in-project reachability, but cannot justify an open-world external
    /// caller by themselves.
    pub fn is_externally_exposed(self) -> bool {
        matches!(self, ItemVisibility::Public)
    }
}

#[derive(Debug, Clone, Default)]
pub struct ApiUsageEvidenceSet {
    pub evidence: Vec<ApiUsageEvidence>,
}

impl ApiUsageEvidenceSet {
    pub fn has_exposed_type_signal(&self) -> bool {
        self.evidence
            .iter()
            .any(|item| item.kind == ApiUsageKind::PublicStruct)
    }

    pub fn has_usage_signal(&self) -> bool {
        self.evidence
            .iter()
            .any(|item| item.kind.is_usage_semantic())
    }

    /// Evidence that an external caller can plausibly create overlapping
    /// agents, rather than merely call an ordinary `&T` method.
    pub fn has_parallel_usage_signal(&self) -> bool {
        self.evidence.iter().any(|item| {
            matches!(
                item.kind,
                ApiUsageKind::SharedWrapperInSignature
                    | ApiUsageKind::SharedReceiverMethod
                    | ApiUsageKind::RawPointerInSignature
                    | ApiUsageKind::CallbackOrBatchApi
            )
        })
    }

    pub fn descriptions(&self) -> Vec<String> {
        unique_descriptions(self.evidence.iter().map(|item| item.description.as_str()))
    }

    pub fn max_score(&self) -> f32 {
        self.evidence
            .iter()
            .map(|item| item.score)
            .fold(0.0, f32::max)
    }
}

#[derive(Debug, Clone)]
pub struct ApiUsageEvidence {
    pub kind: ApiUsageKind,
    pub description: String,
    pub file: String,
    pub line: usize,
    pub score: f32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ApiUsageKind {
    PublicStruct,
    PublicField,
    MethodNameSuggestsHotUse,
    FunctionNameSuggestsHotUse,
    SharedWrapperInSignature,
    /// A public method accepts a non-exclusive `&self` receiver.  This is only
    /// an external parallelism capability; rules must still recover distinct
    /// accesses and a write before it can contribute to a finding.
    SharedReceiverMethod,
    /// A public unsafe/raw-pointer API can expose aliases without Rust's
    /// exclusive-reference discipline.  This remains a may-parallel witness,
    /// not a claim that the caller actually uses it concurrently.
    RawPointerInSignature,
    ReferenceInSignature,
    HandleLikeReturn,
    CallbackOrBatchApi,
    SemanticTypeOrFieldName,
}

impl ApiUsageKind {
    pub fn is_usage_semantic(&self) -> bool {
        !matches!(
            self,
            ApiUsageKind::PublicStruct
                | ApiUsageKind::PublicField
                | ApiUsageKind::SemanticTypeOrFieldName
        )
    }
}

// --- Concurrency evidence ---

#[derive(Debug, Clone, Default)]
pub struct ConcurrencyEvidenceSet {
    pub evidence: Vec<EvidenceItem>,
}

impl ConcurrencyEvidenceSet {
    pub fn has_evidence(&self) -> bool {
        !self.evidence.is_empty()
    }

    pub fn descriptions(&self) -> Vec<String> {
        unique_descriptions(self.evidence.iter().map(|item| item.description.as_str()))
    }

    pub fn total_hotness(&self) -> f32 {
        self.evidence.iter().map(|item| item.hotness_score).sum()
    }

    pub fn atomic_write_count(&self) -> usize {
        self.evidence
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .count()
    }

    pub fn has_kind(&self, kind: EvidenceKind) -> bool {
        self.evidence.iter().any(|item| item.kind == kind)
    }

    pub fn has_lock_wrapper(&self) -> bool {
        self.has_kind(EvidenceKind::MutexWrapped) || self.has_kind(EvidenceKind::RwLockWrapped)
    }

    pub fn has_concurrency_signal(&self) -> bool {
        self.evidence.iter().any(|item| {
            matches!(
                item.kind,
                EvidenceKind::ArcWrapped
                    | EvidenceKind::UsedInSpawn
                    | EvidenceKind::UsedInParallelIter
                    | EvidenceKind::FieldAccessInConcurrentContext
            ) || item.in_concurrent_context
        })
    }

    pub fn has_strong_parallel_signal(&self) -> bool {
        self.evidence.iter().any(|item| {
            item.in_concurrent_context
                || matches!(
                    item.kind,
                    EvidenceKind::UsedInSpawn
                        | EvidenceKind::UsedInParallelIter
                        | EvidenceKind::FieldAccessInConcurrentContext
                )
        })
    }

    pub fn has_shared_ownership_signal(&self) -> bool {
        self.has_kind(EvidenceKind::ArcWrapped)
            || self
                .evidence
                .iter()
                .any(|item| item.through_shared_indirection)
    }

    pub fn max_hotness(&self) -> f32 {
        self.evidence
            .iter()
            .map(|item| item.hotness_score)
            .fold(0.0, f32::max)
    }

    pub fn written_fields_matching(&self, candidates: &[String]) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.evidence
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }

    pub fn write_count_matching(&self, candidates: &[String]) -> usize {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.evidence
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .count()
    }

    pub fn hot_written_fields_matching(
        &self,
        candidates: &[String],
        min_hotness: f32,
    ) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.evidence
            .iter()
            .filter(|item| item.hotness_score >= min_hotness)
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }

    pub fn concurrent_written_fields_matching(&self, candidates: &[String]) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.evidence
            .iter()
            .filter(|item| item.in_concurrent_context)
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }

    pub fn read_fields_matching(&self, candidates: &[String]) -> HashSet<String> {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.evidence
            .iter()
            .filter(|item| matches!(item.access_kind, Some(AtomicAccessKind::Read)))
            .filter_map(|item| item.field_name.as_deref())
            .filter(|field| candidate_set.contains(field))
            .map(ToOwned::to_owned)
            .collect()
    }

    pub fn has_exclusive_writes_without_sharing(&self, candidates: &[String]) -> bool {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        let write_items: Vec<&EvidenceItem> = self
            .evidence
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .filter(|item| {
                item.field_name
                    .as_deref()
                    .map(|field| candidate_set.contains(field))
                    .unwrap_or(false)
            })
            .collect();

        !write_items.is_empty()
            && write_items.iter().all(|item| !item.in_concurrent_context)
            && write_items
                .iter()
                .all(|item| item.access_mode.is_exclusive())
    }

    pub fn has_only_exclusive_plain_writes_matching(&self, candidates: &[String]) -> bool {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        let write_items: Vec<&EvidenceItem> = self
            .evidence
            .iter()
            .filter(|item| item.kind == EvidenceKind::PlainFieldWrite)
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .filter(|item| {
                item.field_name
                    .as_deref()
                    .map(|field| candidate_set.contains(field))
                    .unwrap_or(false)
            })
            .collect();

        !write_items.is_empty()
            && write_items
                .iter()
                .all(|item| !item.in_concurrent_context && item.access_mode.is_exclusive())
    }

    pub fn has_shared_or_concurrent_writes_matching(&self, candidates: &[String]) -> bool {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        self.evidence
            .iter()
            .filter(|item| {
                matches!(
                    item.access_kind,
                    Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
                )
            })
            .filter(|item| {
                item.field_name
                    .as_deref()
                    .map(|field| candidate_set.contains(field))
                    .unwrap_or(false)
            })
            .any(|item| item.in_concurrent_context || !item.access_mode.is_exclusive())
    }

    pub fn writes_co_located_in_single_function(&self, candidates: &[String]) -> bool {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        let mut per_fn: HashMap<String, HashSet<String>> = HashMap::new();
        let mut all_fields = HashSet::new();

        for item in &self.evidence {
            if item
                .semantic_contexts
                .iter()
                .any(|context| context == "container_element_pointee")
            {
                continue;
            }
            if !matches!(
                item.access_kind,
                Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite)
            ) {
                continue;
            }

            let Some(field_name) = item.field_name.as_deref() else {
                continue;
            };
            if !candidate_set.contains(field_name) {
                continue;
            }

            let Some(function_name) = item.function_name.as_deref() else {
                return false;
            };

            all_fields.insert(field_name.to_string());
            per_fn
                .entry(function_name.to_string())
                .or_default()
                .insert(field_name.to_string());
        }

        all_fields.len() >= 2
            && per_fn.len() == 1
            && per_fn
                .values()
                .next()
                .map(|fields| fields.len() == all_fields.len())
                .unwrap_or(false)
    }

    pub fn summarize_for_candidates(
        &self,
        candidates: &[String],
        min_hotness: f32,
    ) -> CandidateEvidenceSummary {
        let candidate_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
        let mut summary = CandidateEvidenceSummary::default();
        let mut write_items = Vec::new();
        let mut plain_write_items = Vec::new();
        let mut per_fn: HashMap<String, HashSet<String>> = HashMap::new();
        let mut all_function_fields = HashSet::new();
        let mut missing_function_name = false;
        let mut has_candidate_access = false;

        for item in &self.evidence {
            if item
                .semantic_contexts
                .iter()
                .any(|context| context == "container_element_pointee")
            {
                continue;
            }
            let Some(field_name) = item.field_name.as_deref() else {
                continue;
            };
            if !candidate_set.contains(field_name) {
                continue;
            }

            has_candidate_access |= item.access_kind.is_some();
            summary.total_hotness += item.hotness_score;
            summary.max_hotness = summary.max_hotness.max(item.hotness_score);
            summary.has_concurrency |= item.in_concurrent_context
                || matches!(
                    item.kind,
                    EvidenceKind::UsedInSpawn
                        | EvidenceKind::UsedInParallelIter
                        | EvidenceKind::FieldAccessInConcurrentContext
                );
            summary.has_strong_parallel |= item.in_concurrent_context
                || item.kind == EvidenceKind::FieldAccessInConcurrentContext;
            summary.has_shared_ownership |= item.through_shared_indirection
                || item.through_raw_pointer
                || item.kind == EvidenceKind::ArcWrapped;
            summary.lock_protected |= matches!(
                item.kind,
                EvidenceKind::MutexWrapped | EvidenceKind::RwLockWrapped
            );

            match item.access_kind {
                Some(AtomicAccessKind::Read) => {
                    summary.read_fields.insert(field_name.to_string());
                }
                Some(AtomicAccessKind::Write | AtomicAccessKind::ReadModifyWrite) => {
                    summary.written_fields.insert(field_name.to_string());
                    write_items.push(item);
                    if item.kind == EvidenceKind::PlainFieldWrite {
                        plain_write_items.push(item);
                    }
                    if item.in_concurrent_context {
                        summary
                            .concurrent_written_fields
                            .insert(field_name.to_string());
                    }
                    if item.hotness_score >= min_hotness {
                        summary.hot_written_fields.insert(field_name.to_string());
                    }
                    if item.in_concurrent_context || !item.access_mode.is_exclusive() {
                        summary.shared_or_concurrent_writes = true;
                    }
                    if let Some(function_name) = item.function_name.as_deref() {
                        all_function_fields.insert(field_name.to_string());
                        per_fn
                            .entry(function_name.to_string())
                            .or_default()
                            .insert(field_name.to_string());
                    } else {
                        missing_function_name = true;
                    }
                }
                None => {}
            }
        }

        // Type-wide ownership/parallel facts may strengthen a candidate only
        // after an access path has reached one of its fields. This prevents an
        // unrelated hot member from lending evidence to every field pair in a
        // large record.
        if has_candidate_access {
            for item in self
                .evidence
                .iter()
                .filter(|item| item.field_name.is_none())
            {
                summary.has_concurrency |= item.in_concurrent_context
                    || matches!(
                        item.kind,
                        EvidenceKind::UsedInSpawn | EvidenceKind::UsedInParallelIter
                    );
                summary.has_strong_parallel |= item.in_concurrent_context
                    || matches!(
                        item.kind,
                        EvidenceKind::UsedInSpawn | EvidenceKind::UsedInParallelIter
                    );
                summary.has_shared_ownership |= item.kind == EvidenceKind::ArcWrapped
                    || item.through_shared_indirection
                    || item.through_raw_pointer;
            }
        }

        summary.ownership_partitioned = !write_items.is_empty()
            && write_items.iter().all(|item| !item.in_concurrent_context)
            && write_items
                .iter()
                .all(|item| item.access_mode.is_exclusive());

        summary.exclusive_plain_writes_only = !plain_write_items.is_empty()
            && plain_write_items
                .iter()
                .all(|item| !item.in_concurrent_context && item.access_mode.is_exclusive());

        summary.likely_true_sharing = !missing_function_name
            && all_function_fields.len() >= 2
            && per_fn.len() == 1
            && per_fn
                .values()
                .next()
                .map(|fields| fields.len() == all_function_fields.len())
                .unwrap_or(false);

        summary
    }
}

#[derive(Debug, Clone, Default)]
pub struct CandidateEvidenceSummary {
    pub written_fields: HashSet<String>,
    pub concurrent_written_fields: HashSet<String>,
    pub hot_written_fields: HashSet<String>,
    pub read_fields: HashSet<String>,
    pub total_hotness: f32,
    pub max_hotness: f32,
    pub has_concurrency: bool,
    pub has_strong_parallel: bool,
    pub has_shared_ownership: bool,
    pub lock_protected: bool,
    pub likely_true_sharing: bool,
    pub ownership_partitioned: bool,
    pub exclusive_plain_writes_only: bool,
    pub shared_or_concurrent_writes: bool,
}

#[derive(Debug, Clone)]
pub struct EvidenceItem {
    pub kind: EvidenceKind,
    pub access_kind: Option<AtomicAccessKind>,
    pub field_name: Option<String>,
    pub loop_context: Option<LoopContext>,
    pub hotness_score: f32,
    pub in_concurrent_context: bool,
    pub access_mode: AccessMode,
    pub function_name: Option<String>,
    pub propagation_depth: usize,
    pub call_path: Vec<String>,
    pub semantic_contexts: Vec<String>,
    pub through_shared_indirection: bool,
    pub through_raw_pointer: bool,
    pub description: String,
    pub file: String,
    pub line: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessMode {
    Unknown,
    Shared,
    Exclusive,
}

impl AccessMode {
    pub fn is_exclusive(self) -> bool {
        matches!(self, AccessMode::Exclusive)
    }
}

#[derive(Debug, Clone)]
pub struct LoopContext {
    pub nesting_depth: usize,
    pub iteration_estimate: IterationEstimate,
}

#[derive(Debug, Clone)]
pub enum IterationEstimate {
    Constant(u64),
    Dynamic,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AtomicAccessKind {
    Read,            // load
    Write,           // store
    ReadModifyWrite, // fetch_add, fetch_sub, swap, compare_exchange, etc.
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EvidenceKind {
    ArcWrapped,
    MutexWrapped,
    RwLockWrapped,
    /// An explicit `Send`/`Sync` implementation provides a type-level
    /// cross-agent capability. It is not sufficient without candidate-scoped
    /// non-exclusive accesses.
    SendSyncCapability,
    UsedInSpawn,
    UsedInParallelIter,
    AtomicFieldOps,
    HotSyncFieldOps,
    PlainFieldWrite,
    PlainFieldRead,
    FieldAccessInConcurrentContext,
}

/// A parsed source file ready for analysis.
pub struct ParsedFile {
    pub path: String,
    pub module_path: String,
    pub source: String,
    pub ast: syn::File,
    pub crate_name: Option<String>,
}

fn unique_descriptions<'a>(descriptions: impl Iterator<Item = &'a str>) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for description in descriptions {
        if seen.insert(description) {
            out.push(description.to_string());
        }
    }
    out
}
