pub mod analyzer;
pub mod compile_database;
pub mod compiler_sidecar;
pub mod evidence;
pub mod initialization;
pub mod layout;
mod layout_macros;
pub mod parser;
pub mod pattern;
mod reportability;
pub mod rules;
mod type_bindings;
pub mod types;
mod unevaluated;
pub mod workspace;

pub use analyzer::{analyze_cpp_path_with_options, looks_like_cpp_project};
