use quote::ToTokens;
use sha2::{Digest, Sha256};
use std::path::Path;

pub fn find_line(src: &str, needle: &str) -> Option<usize> {
    src.find(needle).map(|idx| line_of_offset(src, idx))
}

pub fn line_of_offset(src: &str, offset: usize) -> usize {
    src[..offset].bytes().filter(|b| *b == b'\n').count() + 1
}

pub fn compact_snippet(src: &str, start: usize, end: usize) -> String {
    let mut s = src[start..end].replace('\n', " ");
    if s.len() > 120 {
        s.truncate(120);
    }
    s
}

pub fn path_to_string(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

pub fn stable_finding_hash(candidate_kind: &str, file: &str, line: usize, snippet: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(candidate_kind.as_bytes());
    hasher.update(b"|");
    hasher.update(file.as_bytes());
    hasher.update(b"|");
    hasher.update(line.to_string().as_bytes());
    hasher.update(b"|");
    hasher.update(snippet.as_bytes());
    hex::encode(hasher.finalize())
}

pub fn normalize_type_name(raw: &str) -> Option<String> {
    let mut ty = raw.trim();

    while let Some(rest) = ty.strip_prefix('&') {
        ty = rest.trim_start();
    }
    if let Some(rest) = ty.strip_prefix("mut ") {
        ty = rest.trim_start();
    }
    if ty.starts_with("* const") || ty.starts_with("* mut") {
        return Some("Pointer".to_string());
    }

    let head = ty.split('<').next()?.trim();
    let last_segment = head.split("::").last()?.trim();
    if last_segment.is_empty() {
        None
    } else {
        Some(last_segment.to_string())
    }
}

pub fn is_atomic_type(ty: &str) -> bool {
    match normalize_type_name(ty).as_deref() {
        Some("AtomicBool" | "AtomicPtr") => true,
        Some(name) if name.starts_with("AtomicI") || name.starts_with("AtomicU") => true,
        Some(name) if name.starts_with("Atomic") => true,
        _ => false,
    }
}

pub fn contains_atomic_payload_type(ty: &str) -> bool {
    ty.contains("Atomic")
}

pub fn is_indirection_type(ty: &str) -> bool {
    if ty.trim_start().starts_with('&')
        || ty.trim_start().starts_with("* const")
        || ty.trim_start().starts_with("* mut")
    {
        return true;
    }

    matches!(
        normalize_type_name(ty).as_deref(),
        Some("Arc" | "Box" | "Rc" | "Vec" | "NonNull" | "Pointer")
    )
}

pub fn is_cache_padded_type(ty: &str) -> bool {
    let compact: String = ty.chars().filter(|ch| !ch.is_whitespace()).collect();
    matches!(
        compact.split('<').next(),
        Some("crossbeam_utils::CachePadded" | "crossbeam::utils::CachePadded")
    )
}

pub fn is_manual_padding_field(name: &str, ty: &str) -> bool {
    let lower = name.to_lowercase();
    if !(lower.contains("pad")
        || lower.contains("padding")
        || lower == "_pad"
        || lower.starts_with("_pad"))
    {
        return false;
    }

    let compact: String = ty.chars().filter(|c| !c.is_whitespace()).collect();
    compact.starts_with("[u8;")
        || compact.starts_with("[MaybeUninit<u8>;")
        || compact.starts_with("[std::mem::MaybeUninit<u8>;")
}

pub fn is_hot_sync_type(ty: &str) -> bool {
    if contains_atomic_payload_type(ty) {
        return true;
    }

    let normalized = normalize_type_name(ty);
    matches!(
        normalized.as_deref(),
        Some(
            "Mutex"
                | "RwLock"
                | "UnsafeCell"
                | "AtomicWaker"
                | "Notify"
                | "SeqLock"
                | "WordLock"
                | "Parker"
        )
    ) || ty.contains("Mutex")
        || ty.contains("RwLock")
        || ty.contains("UnsafeCell")
        || ty.contains("AtomicWaker")
        || ty.contains("Notify")
        || ty.contains("SeqLock")
        || ty.contains("WordLock")
}

pub fn is_hot_static_singleton_type(ty: &str) -> bool {
    let normalized = normalize_type_name(ty);
    matches!(
        normalized.as_deref(),
        Some("OnceCell" | "OnceLock" | "Lazy" | "LazyLock")
    ) || ty.contains("OnceCell")
        || ty.contains("OnceLock")
        || ty.contains("LazyLock")
        || ty.contains("Lazy <")
        || ty.contains("Lazy<")
}

pub fn is_hot_scalar_field(name: &str, ty: &str) -> bool {
    let hot_name = [
        "count", "counter", "stat", "hits", "miss", "idx", "index", "tail", "head", "write",
        "read", "epoch", "tick",
    ]
    .iter()
    .any(|k| name.to_lowercase().contains(k));

    let scalar = [
        "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
        "bool",
    ]
    .contains(&ty);

    hot_name && scalar
}

pub fn is_hot_container_name(name: &str) -> bool {
    [
        "counter", "context", "detected", "epoch", "hist", "bucket", "lock", "locks", "queue",
        "shard", "slot", "stat", "task", "worker", "waker",
    ]
    .iter()
    .any(|k| name.to_lowercase().contains(k))
}

pub fn is_array_like_type(ty: &str) -> bool {
    ty.contains('[')
        || ty.contains("Vec <")
        || ty.contains("Vec<")
        || ty.contains("Box < [")
        || ty.contains("Box<[")
        || ty.contains("Arc < Vec")
        || ty.contains("Arc<Vec")
}

pub fn is_whole_container_lock_type(ty: &str) -> bool {
    let compact: String = ty.chars().filter(|ch| !ch.is_whitespace()).collect();
    compact.contains("Mutex<Vec<")
        || compact.contains("RwLock<Vec<")
        || compact.contains("Mutex<Box<[")
        || compact.contains("RwLock<Box<[")
        || compact.contains("Arc<Mutex<Vec<")
        || compact.contains("Arc<RwLock<Vec<")
        || compact.contains("Arc<Mutex<Box<[")
        || compact.contains("Arc<RwLock<Box<[")
}

pub fn is_array_like_hot_container(name: &str, ty: &str) -> bool {
    is_array_like_type(ty)
        && !is_whole_container_lock_type(ty)
        && is_hot_sync_type(ty)
        && is_hot_container_name(name)
}

pub(crate) fn cfg_is_test_only(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if attr.path().is_ident("test") {
            return true;
        }
        if !attr.path().is_ident("cfg") {
            return false;
        }
        let compact: String = attr
            .meta
            .to_token_stream()
            .to_string()
            .chars()
            .filter(|ch| !ch.is_whitespace())
            .collect();
        compact == "cfg(test)"
            || (compact.starts_with("cfg(all(")
                && compact
                    .trim_start_matches("cfg(all(")
                    .trim_end_matches("))")
                    .split(',')
                    .any(|term| term == "test"))
    })
}
