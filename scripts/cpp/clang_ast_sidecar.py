#!/usr/bin/env python3
"""libclang AST producer for the C++ semantic-sidecar v1 protocol.

The detector supplies normalized compilation commands and source-derived
candidate accesses on stdin. This process reparses bounded translation units,
returns ABI record layouts for candidate record types, and replaces access
guesses only when a matching AST member expression can be classified.

Install the Python ``libclang`` wheel in an isolated environment and launch
this file through ``run_clang_ast_sidecar.sh``. The producer deliberately
returns no facts for unparsed/incomplete inputs; the Rust consumer then keeps
its source-level may-analysis instead of treating missing compiler facts as an
exclusion.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable


SCHEMA_VERSION = "false-sharing-cpp-semantic-sidecar/v1"
DEFAULT_MAX_TUS = 64
DEFAULT_TIME_BUDGET_SECONDS = 50.0
DEFAULT_MAX_CFG_TUS = 8
MAX_DIAGNOSTICS = 100

FUNCTION_KINDS = {
    "FUNCTION_DECL",
    "FUNCTION_TEMPLATE",
    "CXX_METHOD",
    "CONSTRUCTOR",
    "DESTRUCTOR",
    "CONVERSION_FUNCTION",
}
CONSTRUCTOR_KINDS = {"CONSTRUCTOR"}
CONTROL_FLOW_KINDS = {
    "IF_STMT",
    "SWITCH_STMT",
    "CASE_STMT",
    "DEFAULT_STMT",
    "FOR_STMT",
    "CXX_FOR_RANGE_STMT",
    "WHILE_STMT",
    "DO_STMT",
    "CONDITIONAL_OPERATOR",
}

RMW_CALL_MARKERS = (
    "fetch_add",
    "fetch_sub",
    "fetch_or",
    "fetch_and",
    "fetch_xor",
    "exchange",
    "compare_exchange",
    "test_and_set",
    "increment",
    "decrement",
)
WRITE_CALL_MARKERS = (".store", ".clear", ".reset", ".push_", ".emplace")
LOAD_CALL_MARKERS = ("atomic_load", ".load")
C_ATOMIC_RMW_MARKERS = (
    "atomic_fetch_add",
    "atomic_fetch_sub",
    "atomic_fetch_or",
    "atomic_fetch_and",
    "atomic_fetch_xor",
    "atomic_exchange",
    "atomic_compare_exchange",
    "atomic_flag_test_and_set",
)
C_ATOMIC_WRITE_MARKERS = ("atomic_store", "atomic_flag_clear", "atomic_init")


def _load_cindex():
    try:
        from clang import cindex  # type: ignore
    except ImportError as error:
        raise RuntimeError(
            "Python libclang is unavailable; install it with "
            "`uv pip install --python <venv>/bin/python libclang==18.1.1`"
        ) from error
    return cindex


def _canonical_path(value: str, directory: str | None = None) -> str:
    path = Path(value)
    if not path.is_absolute() and directory:
        path = Path(directory) / path
    return str(path.resolve(strict=False))


def _bounded_int(name: str, default: int, minimum: int, maximum: int) -> int:
    try:
        value = int(os.environ.get(name, default))
    except ValueError:
        return default
    return min(maximum, max(minimum, value))


def _bounded_float(name: str, default: float, minimum: float, maximum: float) -> float:
    try:
        value = float(os.environ.get(name, default))
    except ValueError:
        return default
    return min(maximum, max(minimum, value))


def _qualified_record_name(cursor: Any) -> str:
    parts = [cursor.spelling]
    parent = cursor.semantic_parent
    while parent is not None and parent.kind.name != "TRANSLATION_UNIT":
        if parent.kind.name in {
            "NAMESPACE",
            "STRUCT_DECL",
            "CLASS_DECL",
            "CLASS_TEMPLATE",
        } and parent.spelling:
            parts.append(parent.spelling)
        parent = parent.semantic_parent
    return "::".join(reversed(parts))


def _record_matches(cursor: Any, target_names: set[str]) -> bool:
    qualified = _qualified_record_name(cursor)
    return cursor.spelling in target_names or qualified in target_names


def _safe_type_size(clang_type: Any) -> int | None:
    try:
        size = int(clang_type.get_size())
    except Exception:
        return None
    return size if size >= 0 else None


def _safe_type_alignment(clang_type: Any) -> int | None:
    try:
        alignment = int(clang_type.get_align())
    except Exception:
        return None
    return alignment if alignment > 0 else None


def _safe_children(cursor: Any) -> list[Any]:
    children: list[Any] = []
    try:
        iterator = iter(cursor.get_children())
        while True:
            children.append(next(iterator))
    except StopIteration:
        return children
    except Exception:
        # Some libclang/Python-binding combinations expose a valid parent AST
        # cursor but an unknown template-argument cursor kind. Treat that
        # subtree as uncovered instead of failing the complete sidecar run.
        return children


def _record_layout(
    cursor: Any, variant_id: str, authoritative: bool
) -> dict[str, Any] | None:
    size = _safe_type_size(cursor.type)
    alignment = _safe_type_alignment(cursor.type)
    if size is None or alignment is None or not cursor.is_definition():
        return None

    fields: list[dict[str, Any]] = []
    packed = False
    for child in _safe_children(cursor):
        if child.kind.name == "PACKED_ATTR":
            packed = True
            continue
        if child.kind.name != "FIELD_DECL":
            continue
        # The consumer labels an accepted record as compiler-exact. Anonymous
        # or target-dependent fields that cannot be represented by protocol v1
        # make the record incomplete, so fall back as a whole.
        if not child.spelling:
            return None
        field_size = _safe_type_size(child.type)
        try:
            bit_offset = int(child.get_field_offsetof())
        except Exception:
            return None
        if bit_offset < 0 or field_size is None or field_size == 0:
            return None
        fields.append(
            {
                "name": child.spelling,
                "offset": bit_offset // 8,
                "size": field_size,
            }
        )
    if not fields:
        return None

    location_file = cursor.location.file
    tokens = "".join(token.spelling for token in cursor.get_tokens()).lower()
    packed = packed or "__attribute__((packed" in tokens
    return {
        "name": cursor.spelling,
        "canonical_type": _qualified_record_name(cursor),
        "file": _canonical_path(location_file.name) if location_file else None,
        "build_variant": variant_id,
        "authoritative": authoritative,
        "size": size,
        "alignment": alignment,
        "packed": packed,
        "fields": fields,
    }


def _assignment_token(cursor: Any) -> str | None:
    assignment_tokens = {
        "=",
        "+=",
        "-=",
        "*=",
        "/=",
        "%=",
        "|=",
        "&=",
        "^=",
        "<<=",
        ">>=",
    }
    for token in cursor.get_tokens():
        if token.spelling in assignment_tokens:
            return token.spelling
    return None


def _source_line_effect(cursor: Any, file: str, line: int) -> str | None:
    """Classify compiler-visible macro spelling on the member's source line.

    C11 atomic operations are macros on common libc implementations. libclang
    can expose the referenced field below an UNEXPOSED_EXPR without retaining
    a CALL_EXPR. Tokens still carry their original expansion locations, so a
    unique atomic operation on that exact line is safe to use. Conflicting
    operations deliberately produce no fact.
    """

    spellings: list[str] = []
    for token in cursor.get_tokens():
        location_file = token.location.file
        if (
            location_file is not None
            and _canonical_path(location_file.name) == file
            and token.location.line == line
        ):
            spellings.append(token.spelling)
    source = "".join(spellings).lower()
    effects: set[str] = set()
    if "atomic_load" in source:
        effects.add("read")
    if any(marker in source for marker in C_ATOMIC_RMW_MARKERS):
        effects.add("read_modify_write")
    if any(marker in source for marker in C_ATOMIC_WRITE_MARKERS):
        effects.add("write")
    return next(iter(effects)) if len(effects) == 1 else None


def _classify_member_access(
    ancestors: list[tuple[Any, int]], file: str, line: int
) -> str | None:
    address_taken = False
    for parent, branch in reversed(ancestors):
        kind = parent.kind.name
        if kind == "COMPOUND_ASSIGNMENT_OPERATOR":
            return "read_modify_write" if branch == 0 else "read"
        if kind == "UNARY_OPERATOR":
            tokens = {token.spelling for token in parent.get_tokens()}
            if "++" in tokens or "--" in tokens:
                return "read_modify_write"
            if "&" in tokens:
                address_taken = True
        if kind == "BINARY_OPERATOR":
            operator = _assignment_token(parent)
            if operator is not None:
                if branch != 0:
                    return "read"
                return "write" if operator == "=" else "read_modify_write"
        if kind in {
            "CALL_EXPR",
            "CXX_MEMBER_CALL_EXPR",
            "VAR_DECL",
            "UNEXPOSED_EXPR",
            "DECL_STMT",
            "COMPOUND_STMT",
        }:
            source_effect = _source_line_effect(parent, file, line)
            if source_effect is not None:
                return source_effect
            call = (
                parent.spelling
                + " "
                + "".join(token.spelling for token in parent.get_tokens())
            ).lower()
            if any(marker in call for marker in LOAD_CALL_MARKERS):
                return "read"
            if any(marker in call for marker in RMW_CALL_MARKERS):
                return "read_modify_write"
            if "atomic_store" in call or any(marker in call for marker in WRITE_CALL_MARKERS):
                return "write"
            # Without interprocedural parameter effects, passing &field to an
            # arbitrary call is not enough for the AST producer to override
            # the source fact in either direction.
            if address_taken and kind in {"CALL_EXPR", "CXX_MEMBER_CALL_EXPR"}:
                return None
        if address_taken and kind in {"DECL_STMT", "COMPOUND_STMT", "FUNCTION_DECL"}:
            return None
    return None if address_taken else "read"


def _candidate_key(file: str, line: int, field: str) -> tuple[str, int, str]:
    return (_canonical_path(file), int(line), field)


def _cursor_identity(cursor: Any) -> str:
    try:
        usr = cursor.get_usr()
    except Exception:
        usr = ""
    if usr:
        return usr
    location = cursor.location
    location_file = location.file.name if location.file else ""
    return f"{_qualified_record_name(cursor)}@{location_file}:{location.line}"


def _enclosing_function(ancestors: list[tuple[Any, int]]) -> Any | None:
    for cursor, _ in reversed(ancestors):
        if cursor.kind.name in FUNCTION_KINDS:
            return cursor
    return None


def _qualified_function_name(cursor: Any | None) -> str | None:
    if cursor is None:
        return None
    parts = [cursor.spelling or cursor.displayname]
    parent = cursor.semantic_parent
    while parent is not None and parent.kind.name != "TRANSLATION_UNIT":
        if parent.spelling and parent.kind.name in {
            "NAMESPACE",
            "STRUCT_DECL",
            "CLASS_DECL",
            "CLASS_TEMPLATE",
        }:
            parts.append(parent.spelling)
        parent = parent.semantic_parent
    return "::".join(reversed([part for part in parts if part])) or None


def _descendants(cursor: Any) -> Iterable[Any]:
    for child in _safe_children(cursor):
        yield child
        yield from _descendants(child)


def _local_receiver_decl(member_cursor: Any) -> Any | None:
    """Return a direct, by-value local object used as a member receiver."""

    for child in _descendants(member_cursor):
        if child.kind.name != "DECL_REF_EXPR" or child.referenced is None:
            continue
        declaration = child.referenced
        if declaration.kind.name != "VAR_DECL":
            continue
        type_kind = declaration.type.kind.name
        if type_kind in {
            "POINTER",
            "LVALUEREFERENCE",
            "RVALUEREFERENCE",
            "MEMBERPOINTER",
        }:
            continue
        parent = declaration.semantic_parent
        if parent is not None and parent.kind.name in FUNCTION_KINDS:
            return declaration
    return None


def _collect_semantics(root: Any) -> dict[str, Any]:
    """Build bounded AST callgraph/control-flow and local-escape summaries.

    Missing call edges never prove single-threaded execution. The callgraph is
    only used to propagate positive concurrency roots. A local object is
    non-escaping only when every reference is a direct member receiver and no
    reference is nested in a lambda.
    """

    functions: dict[str, Any] = {}
    call_edges: set[tuple[str, str]] = set()
    thread_roots: set[str] = set()
    local_safe: dict[str, bool] = {}
    control_nodes = 0

    def visit(cursor: Any, current: Any | None, ancestors: list[Any]) -> None:
        nonlocal control_nodes
        kind = cursor.kind.name
        if kind in FUNCTION_KINDS:
            current = cursor
            functions[_cursor_identity(cursor)] = cursor
        if kind in CONTROL_FLOW_KINDS and current is not None:
            control_nodes += 1
        if kind == "VAR_DECL" and current is not None:
            type_kind = cursor.type.kind.name
            if type_kind not in {
                "POINTER",
                "LVALUEREFERENCE",
                "RVALUEREFERENCE",
                "MEMBERPOINTER",
            }:
                local_safe[_cursor_identity(cursor)] = True
        if kind == "DECL_REF_EXPR" and cursor.referenced is not None:
            declaration = cursor.referenced
            local_id = _cursor_identity(declaration)
            if local_id in local_safe:
                direct_member_receiver = any(
                    ancestor.kind.name == "MEMBER_REF_EXPR" for ancestor in ancestors[-2:]
                )
                captured = any(ancestor.kind.name == "LAMBDA_EXPR" for ancestor in ancestors)
                if not direct_member_receiver or captured:
                    local_safe[local_id] = False
        if kind in {"CALL_EXPR", "CXX_MEMBER_CALL_EXPR"} and current is not None:
            caller = _cursor_identity(current)
            referenced = cursor.referenced
            if referenced is not None and referenced.kind.name in FUNCTION_KINDS:
                call_edges.add((caller, _cursor_identity(referenced)))
            call_text = "".join(token.spelling for token in cursor.get_tokens()).lower()
            if any(
                marker in call_text
                for marker in ("pthread_create", "std::thread", "std::jthread", "std::async")
            ):
                for child in _descendants(cursor):
                    target = child.referenced
                    if target is not None and target.kind.name in FUNCTION_KINDS:
                        target_id = _cursor_identity(target)
                        if referenced is None or target_id != _cursor_identity(referenced):
                            thread_roots.add(target_id)
        for child in _safe_children(cursor):
            visit(child, current, ancestors + [cursor])

    visit(root, None, [])
    return {
        "functions": functions,
        "call_edges": call_edges,
        "thread_roots": thread_roots,
        "local_safe": local_safe,
        "control_nodes": control_nodes,
    }


def _reachable_functions(
    seeds: set[str], edges: set[tuple[str, str]]
) -> set[str]:
    outgoing: dict[str, set[str]] = defaultdict(set)
    for caller, callee in edges:
        outgoing[caller].add(callee)
    reached = set(seeds)
    pending = list(seeds)
    while pending:
        caller = pending.pop()
        for callee in outgoing.get(caller, set()):
            if callee not in reached:
                reached.add(callee)
                pending.append(callee)
    return reached


def _walk_translation_unit(
    cursor: Any,
    target_records: set[str],
    candidates: dict[tuple[str, int, str], list[dict[str, Any]]],
    layouts: list[dict[str, Any]],
    accesses: dict[tuple[str, int, str, str], dict[str, Any]],
    variant_id: str,
    authoritative: bool,
    semantics: dict[str, Any],
    concurrent_functions: set[str],
    ancestors: list[tuple[Any, int]] | None = None,
) -> None:
    ancestors = ancestors or []
    kind = cursor.kind.name
    if kind in {"STRUCT_DECL", "CLASS_DECL"} and cursor.spelling:
        if _record_matches(cursor, target_records):
            layout = _record_layout(cursor, variant_id, authoritative)
            if layout is not None:
                layouts.append(layout)

    if kind == "MEMBER_REF_EXPR" and cursor.spelling and cursor.location.file:
        key = _candidate_key(
            cursor.location.file.name,
            cursor.location.line,
            cursor.spelling,
        )
        for candidate in candidates.get(key, []):
            referenced = cursor.referenced
            owner = referenced.semantic_parent if referenced is not None else None
            owner_name = _qualified_record_name(owner) if owner is not None else ""
            requested_owner = str(candidate.get("record_name") or "")
            if requested_owner and owner_name not in {
                requested_owner,
                requested_owner.split("::")[-1],
            } and owner_name.split("::")[-1] != requested_owner.split("::")[-1]:
                continue
            access_kind = _classify_member_access(
                ancestors,
                _canonical_path(cursor.location.file.name),
                cursor.location.line,
            )
            if access_kind is None:
                continue
            function = _enclosing_function(ancestors)
            function_id = _cursor_identity(function) if function is not None else ""
            local_decl = _local_receiver_decl(cursor)
            local_is_safe = bool(
                local_decl is not None
                and semantics["local_safe"].get(_cursor_identity(local_decl), False)
            )
            fact = {
                "record_name": requested_owner or owner_name,
                "field_name": cursor.spelling,
                # Preserve the detector's exact spelling so the Rust consumer
                # replaces the source fact rather than adding a duplicate.
                "file": candidate["file"],
                "line": candidate["line"],
                "access_kind": access_kind,
                "function_name": _qualified_function_name(function)
                or candidate.get("function_name"),
                "in_concurrent_context": bool(candidate.get("in_concurrent_context"))
                or function_id in concurrent_functions,
                "through_shared_indirection": bool(
                    candidate.get("through_shared_indirection")
                ),
                "through_raw_pointer": bool(candidate.get("through_raw_pointer")),
                "through_thread_local": bool(candidate.get("through_thread_local")),
                "through_nonescaping_local": bool(
                    candidate.get("through_nonescaping_local")
                )
                or local_is_safe,
                "guard_ids": list(candidate.get("guard_ids") or []),
                "initialization_phase": bool(candidate.get("initialization_phase"))
                or bool(function is not None and function.kind.name in CONSTRUCTOR_KINDS),
            }
            fact_key = (
                fact["record_name"],
                fact["field_name"],
                fact["file"],
                fact["line"],
            )
            strength = {"read": 0, "write": 1, "read_modify_write": 2}
            current = accesses.get(fact_key)
            if current is None or strength[access_kind] > strength[current["access_kind"]]:
                accesses[fact_key] = fact

    children = _safe_children(cursor)
    for index, child in enumerate(children):
        _walk_translation_unit(
            child,
            target_records,
            candidates,
            layouts,
            accesses,
            variant_id,
            authoritative,
            semantics,
            concurrent_functions,
            ancestors + [(cursor, index)],
        )


def _parse_arguments(command: dict[str, Any]) -> list[str]:
    arguments = [str(argument) for argument in command.get("semantic_arguments") or []]
    suffix = Path(str(command.get("file") or "")).suffix.lower()
    if not any(argument == "-x" or argument.startswith("-x") for argument in arguments):
        arguments.extend(["-x", "c" if suffix == ".c" else "c++"])
    directory = str(command.get("directory") or "")
    if directory:
        arguments.append(f"-working-directory={directory}")
    resource_dir = _clang_resource_dir()
    if resource_dir is not None and "-nostdinc" not in arguments:
        arguments.append(f"-resource-dir={resource_dir}")
    else:
        resource_include = _gcc_builtin_include()
        if resource_include is not None and "-nostdinc" not in arguments:
            arguments.extend(["-isystem", resource_include])
    return arguments


@lru_cache(maxsize=1)
def _clang_resource_dir() -> str | None:
    configured = os.environ.get("FSD_CLANG_RESOURCE_DIR")
    if not configured:
        return None
    path = Path(configured).expanduser().resolve(strict=False)
    return str(path) if (path / "include" / "stddef.h").is_file() else None


@lru_cache(maxsize=1)
def _gcc_builtin_include() -> str | None:
    """Locate compiler builtin headers absent from the libclang wheel.

    The wheel bundles ``libclang.so`` but not Clang's resource-header tree.
    GCC's local builtin include directory supplies headers such as stddef.h;
    only the fixed system gcc executable is queried, never a compiler path
    taken from an untrusted compilation database.
    """

    gcc = shutil.which("gcc")
    if gcc is None:
        return None
    try:
        completed = subprocess.run(
            [gcc, "-print-file-name=include"],
            check=True,
            capture_output=True,
            text=True,
            timeout=2,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    path = Path(completed.stdout.strip())
    return str(path.resolve()) if path.is_dir() else None


def _select_commands(
    commands: Iterable[dict[str, Any]],
    candidate_files: set[str],
    candidate_counts: dict[str, int],
    maximum: int,
) -> list[dict[str, Any]]:
    commands = list(commands)
    commands.sort(
        key=lambda command: (
            _canonical_path(
                str(command.get("file") or ""), str(command.get("directory") or "")
            )
            not in candidate_files,
            -candidate_counts.get(
                _canonical_path(
                    str(command.get("file") or ""),
                    str(command.get("directory") or ""),
                ),
                0,
            ),
            str(command.get("file") or ""),
            str(command.get("variant_id") or ""),
        )
    )
    return commands[:maximum]


def _infer_include_directories(project_root: Path, candidate_files: set[str]) -> list[str]:
    directories = {project_root.resolve(strict=False)}
    for value in candidate_files:
        path = Path(value).resolve(strict=False)
        directories.add(path.parent)
        for parent in list(path.parents)[:4]:
            if parent == project_root or project_root in parent.parents:
                directories.add(parent)
    for name in ("include", "src", "lib", "source"):
        path = project_root / name
        if path.is_dir():
            directories.add(path.resolve(strict=False))
    # Nested include roots cover the common project/module layout without
    # constructing an unbounded command line for very large repositories.
    try:
        for path in project_root.glob("*/include"):
            if path.is_dir():
                directories.add(path.resolve(strict=False))
    except OSError:
        pass
    return [str(path) for path in sorted(directories, key=str)[:96]]


def _infer_commands(project_root: str, candidate_files: set[str]) -> list[dict[str, Any]]:
    root = Path(project_root).resolve(strict=False)
    include_dirs = _infer_include_directories(root, candidate_files)
    commands: list[dict[str, Any]] = []
    for file in sorted(candidate_files):
        path = Path(file).resolve(strict=False)
        if not path.is_file():
            continue
        language = "c" if path.suffix.lower() == ".c" else "c++"
        standard = "-std=gnu11" if language == "c" else "-std=gnu++20"
        semantic_arguments = [standard, "-D_GNU_SOURCE"]
        for directory in include_dirs:
            semantic_arguments.extend(["-I", directory])
        commands.append(
            {
                "directory": str(root),
                "file": str(path),
                "compiler": "",
                "arguments": [],
                "semantic_arguments": semantic_arguments,
                "command_hash": f"inferred:{path}",
                "variant_id": "inferred-candidate-tu",
                "provenance": "inferred",
            }
        )
    return commands


def _candidate_concurrency_seeds(
    functions: dict[str, Any], raw_candidates: list[dict[str, Any]]
) -> set[str]:
    concurrent_locations = {
        (_canonical_path(str(candidate.get("file") or "")), int(candidate.get("line") or 0))
        for candidate in raw_candidates
        if candidate.get("in_concurrent_context")
    }
    seeds: set[str] = set()
    for identity, function in functions.items():
        start = function.extent.start
        end = function.extent.end
        if start.file is None or end.file is None:
            continue
        file = _canonical_path(start.file.name)
        if any(
            candidate_file == file and start.line <= line <= end.line
            for candidate_file, line in concurrent_locations
        ):
            seeds.add(identity)
    return seeds


def _cfg_probe(
    command: dict[str, Any], file: str, timeout: float
) -> tuple[bool, int, str | None]:
    clang = os.environ.get("FSD_CLANG_BINARY")
    if not clang:
        return (False, 0, None)
    binary = Path(clang).expanduser().resolve(strict=False)
    if not binary.is_file():
        return (False, 0, f"configured Clang CFG binary does not exist: {binary}")
    arguments = [
        argument
        for argument in _parse_arguments(command)
        if not argument.startswith("-resource-dir=")
    ]
    resource_dir = os.environ.get("FSD_CFG_CLANG_RESOURCE_DIR") or os.environ.get(
        "FSD_CLANG_RESOURCE_DIR"
    )
    if resource_dir:
        arguments.append(f"-resource-dir={resource_dir}")
    invocation = [
        str(binary),
        *arguments,
        "-fsyntax-only",
        "-Xclang",
        "-analyze",
        "-Xclang",
        "-analyzer-checker=debug.DumpCFG",
        file,
    ]
    try:
        completed = subprocess.run(
            invocation,
            capture_output=True,
            text=True,
            timeout=max(1.0, timeout),
        )
    except (OSError, subprocess.SubprocessError) as error:
        return (False, 0, f"Clang CFG probe failed for {file}: {error}")
    output = completed.stdout + "\n" + completed.stderr
    blocks = len(re.findall(r"^ \[B\d+", output, flags=re.MULTILINE))
    if completed.returncode != 0:
        return (False, blocks, f"Clang CFG probe rejected {file}")
    return (blocks > 0, blocks, None)


def produce(request: dict[str, Any]) -> dict[str, Any]:
    if request.get("schema_version") != SCHEMA_VERSION:
        raise ValueError(f"unsupported request schema: {request.get('schema_version')!r}")
    cindex = _load_cindex()
    index = cindex.Index.create()

    raw_candidates = list(request.get("candidate_accesses") or [])
    candidates: dict[tuple[str, int, str], list[dict[str, Any]]] = defaultdict(list)
    for candidate in raw_candidates:
        try:
            candidates[
                _candidate_key(candidate["file"], candidate["line"], candidate["field_name"])
            ].append(candidate)
        except (KeyError, TypeError, ValueError):
            continue

    target_records = {
        str(candidate.get("record_name") or "") for candidate in raw_candidates
    } - {""}
    target_records |= {name.split("::")[-1] for name in target_records}
    candidate_files = {key[0] for key in candidates}
    candidate_counts: dict[str, int] = defaultdict(int)
    for key, rows in candidates.items():
        candidate_counts[key[0]] += len(rows)
    maximum = _bounded_int("FSD_CLANG_MAX_TUS", DEFAULT_MAX_TUS, 1, 4096)
    time_budget = _bounded_float(
        "FSD_CLANG_TIME_BUDGET_SECONDS",
        DEFAULT_TIME_BUDGET_SECONDS,
        1.0,
        55.0,
    )
    supplied_commands = list(request.get("compile_commands") or [])
    command_mode = "compile_database" if supplied_commands else "inferred_candidate_tus"
    available_commands = supplied_commands or _infer_commands(
        str(request.get("project_root") or ""), candidate_files
    )
    commands = _select_commands(
        available_commands, candidate_files, candidate_counts, maximum
    )

    layouts: list[dict[str, Any]] = []
    accesses: dict[tuple[str, int, str, str], dict[str, Any]] = {}
    diagnostics: list[str] = []
    parsed = 0
    clean = 0
    attempted = 0
    function_ids: set[str] = set()
    call_edges: set[tuple[str, str]] = set()
    control_nodes = 0
    cfg_files = 0
    cfg_blocks = 0
    max_cfg_tus = _bounded_int("FSD_CLANG_MAX_CFG_TUS", DEFAULT_MAX_CFG_TUS, 0, 128)
    started = time.monotonic()
    for command in commands:
        if time.monotonic() - started >= time_budget:
            diagnostics.append(
                f"libclang AST time budget reached after {parsed}/{len(commands)} translation units"
            )
            break
        file = _canonical_path(
            str(command.get("file") or ""), str(command.get("directory") or "")
        )
        attempted += 1
        try:
            translation_unit = index.parse(
                file,
                args=_parse_arguments(command),
                options=cindex.TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD,
            )
        except Exception as error:
            diagnostics.append(f"failed to parse {file}: {error}")
            continue
        parsed += 1
        has_parse_error = False
        for diagnostic in translation_unit.diagnostics:
            if diagnostic.severity >= cindex.Diagnostic.Error:
                has_parse_error = True
                diagnostics.append(f"{file}: {diagnostic}")
                if len(diagnostics) >= MAX_DIAGNOSTICS:
                    break
        # A partial AST can still contain plausible-looking offsets and
        # expressions. It is not compiler-exact, so never let it override the
        # detector's conservative source facts.
        if has_parse_error:
            continue
        clean += 1
        try:
            semantics = _collect_semantics(translation_unit.cursor)
            function_ids.update(semantics["functions"])
            call_edges.update(semantics["call_edges"])
            control_nodes += int(semantics["control_nodes"])
            seeds = set(semantics["thread_roots"])
            seeds.update(_candidate_concurrency_seeds(semantics["functions"], raw_candidates))
            concurrent_functions = _reachable_functions(seeds, semantics["call_edges"])
            authoritative = (
                str(command.get("provenance") or "compile_database") != "inferred"
            )
            _walk_translation_unit(
                translation_unit.cursor,
                target_records,
                candidates,
                layouts,
                accesses,
                str(
                    command.get("variant_id")
                    or command.get("command_hash")
                    or "default"
                ),
                authoritative,
                semantics,
                concurrent_functions,
            )
        except Exception as error:
            if len(diagnostics) < MAX_DIAGNOSTICS:
                diagnostics.append(f"failed to extract semantic facts from {file}: {error}")
            continue
        if cfg_files < max_cfg_tus and os.environ.get("FSD_CLANG_BINARY"):
            remaining = max(1.0, time_budget - (time.monotonic() - started))
            cfg_ok, block_count, cfg_error = _cfg_probe(
                command, file, min(5.0, remaining)
            )
            if cfg_ok:
                cfg_files += 1
                cfg_blocks += block_count
            elif cfg_error and len(diagnostics) < MAX_DIAGNOSTICS:
                diagnostics.append(cfg_error)

    unique_layouts: dict[str, dict[str, Any]] = {}
    for layout in layouts:
        identity = json.dumps(layout, sort_keys=True, separators=(",", ":"))
        unique_layouts[identity] = layout
    if not commands:
        diagnostics.append("no candidate translation units could be inferred")
    elif parsed == 0:
        diagnostics.append("libclang did not parse any translation unit")
    if len(commands) < len(available_commands):
        diagnostics.append(
            f"translation units bounded to {len(commands)}/{len(available_commands)}"
        )
    return {
        "schema_version": SCHEMA_VERSION,
        "records": list(unique_layouts.values()),
        "accesses": list(accesses.values()),
        "diagnostics": diagnostics[:MAX_DIAGNOSTICS],
        "coverage": {
            "command_mode": command_mode,
            "commands_selected": len(commands),
            "translation_units_attempted": attempted,
            "translation_units_clean": clean,
            "candidate_accesses": len(raw_candidates),
            "confirmed_accesses": len(accesses),
            "functions": len(function_ids),
            "call_edges": len(call_edges),
            "ast_control_nodes": control_nodes,
            "cfg_files": cfg_files,
            "cfg_blocks": cfg_blocks,
        },
    }


def main() -> int:
    try:
        request = json.load(sys.stdin)
        response = produce(request)
        json.dump(response, sys.stdout, separators=(",", ":"))
        sys.stdout.write("\n")
        return 0
    except Exception as error:
        print(f"clang AST sidecar error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
