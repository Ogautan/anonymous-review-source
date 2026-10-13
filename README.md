# Static false-sharing analyzer

Source code for a Rust/C++ static risk analyzer, with synthetic regression
tests and an optional Clang semantic interface.

## Requirements and build

Install a Rust toolchain supporting edition 2024 and Cargo. Cargo downloads
the dependencies pinned in `Cargo.lock` on the first build.

```sh
cargo build --release --locked
cargo test --locked
```

## Usage

```sh
./target/release/false-sharing-detector --help
./target/release/false-sharing-detector /path/to/rust-project --language rust --json
./target/release/false-sharing-detector /path/to/cpp-project --language cpp --json
```

The default cache-line/interference size is 64 bytes. Set
`--cache-line-size 32`, `64`, or `128` explicitly when needed. C++ and mixed
analysis return at most 200 findings by default; use `--all-candidates` to
remove that limit. `--cpp-include-speculative` separately includes candidates
with incomplete concurrency or storage evidence. Inspect report diagnostics,
`analysis_incomplete`, and `truncated_facts` when interpreting results.

A finding is a source-level potential risk, rather than proof of runtime
cache contention or a performance regression. Default analysis does not
require the target project to compile. Source-estimated Rust layouts are
not ABI guarantees. The optional `--rustc-layout` mode requires nightly Rust
and a target that Cargo can build.

Rust container findings require accesses to potentially distinct elements
with at least one element write. Single-element arrays and accesses confined
to one recovered constant index do not supply an element pair. In C++, member
alignment constrains the start address without padding the member's type;
aligning one scalar does not isolate it from the following scalar.

C++ syntax trees use the original active source. Evidence and text fallback
use a comment-masked view with the same byte offsets and line numbers. Semantic
AST traversal skips comment nodes; quoted literals and include header names are
preserved. Alignment must come from attribute syntax associated with the declaration. Rust pattern
bindings respect scope; mutable index effects invalidate constant facts, and
unresolved integer widths cannot supply an overflowing constant exclusion.
Native Rust sequence accessors retain integer index constraints through
`get`/`get_unchecked` and their element-reference `unwrap`/`expect` projections.
Continuous-element findings from different container fields keep separate
storage-pair groups in both frontends.

## Source layout

- `src/`: shared pattern model, Rust frontend, C++ frontend, and CLI.
- `tests/`: synthetic detector regression tests.
- `examples/`: small C++ evidence inspection utilities written in Rust.
- `scripts/cpp/`: optional compiler semantic interface.

## Optional Clang semantic interface

Default C++ analysis uses the source parser. For compiler-derived layout and
access facts, provide the target's `compile_commands.json`, Python 3, and
Clang resource headers matching libclang 18.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r scripts/cpp/requirements-clang-ast.txt
FSD_CLANG_PYTHON=.venv/bin/python \
FSD_CLANG_RESOURCE_DIR=/path/to/lib/clang/18 \
./target/release/false-sharing-detector /path/to/cpp-project --language cpp --json \
  --cpp-semantic-sidecar scripts/cpp/run_clang_ast_sidecar.sh
```

The compile database alone does not enable this interface. Its Python tests
can be run with `.venv/bin/python -m unittest discover -s tests/python`.

## File integrity

`SHA256SUMS` lists the delivered files. Verify them with `sha256sum -c SHA256SUMS`.
