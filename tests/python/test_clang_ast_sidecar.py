import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
SIDECAR_PATH = PROJECT_ROOT / "scripts" / "cpp" / "clang_ast_sidecar.py"


def load_sidecar():
    spec = importlib.util.spec_from_file_location("clang_ast_sidecar", SIDECAR_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


class ClangAstSidecarTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            from clang import cindex  # type: ignore

            cindex.Index.create()
        except (ImportError, OSError):
            raise unittest.SkipTest("Python libclang is not installed")

    def test_emits_exact_layout_and_read_write_rmw_accesses(self):
        sidecar = load_sidecar()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "candidate.cpp"
            source.write_text(
                """struct Counters {
    int left;
    alignas(64) int right;
};
int read_value(Counters *state) { return state->left; }
void write_value(Counters *state) { state->right = 1; }
void increment(Counters *state) { state->left++; }
""",
                encoding="utf-8",
            )
            common = {
                "record_name": "Counters",
                "file": str(source),
                "function_name": None,
                "in_concurrent_context": True,
                "through_shared_indirection": False,
                "through_raw_pointer": True,
                "through_thread_local": False,
                "through_nonescaping_local": False,
                "guard_ids": [],
                "initialization_phase": False,
            }
            request = {
                "schema_version": sidecar.SCHEMA_VERSION,
                "project_root": str(root),
                "cache_line_size": 64,
                "compile_commands": [
                    {
                        "directory": str(root),
                        "file": str(source),
                        "compiler": "clang++",
                        "arguments": ["clang++", "-std=c++17", str(source)],
                        "semantic_arguments": ["-std=c++17"],
                        "command_hash": "fixture",
                        "variant_id": "fixture",
                    }
                ],
                "candidate_accesses": [
                    dict(common, field_name="left", line=5, source_access_kind="write"),
                    dict(common, field_name="right", line=6, source_access_kind="read"),
                    dict(common, field_name="left", line=7, source_access_kind="read"),
                ],
            }

            response = sidecar.produce(request)
            self.assertEqual(response["schema_version"], sidecar.SCHEMA_VERSION)
            layout = next(row for row in response["records"] if row["name"] == "Counters")
            self.assertEqual(layout["size"], 128)
            self.assertEqual(layout["alignment"], 64)
            self.assertEqual(
                {field["name"]: field["offset"] for field in layout["fields"]},
                {"left": 0, "right": 64},
            )
            accesses = {
                (row["field_name"], row["line"]): row for row in response["accesses"]
            }
            self.assertEqual(accesses[("left", 5)]["access_kind"], "read")
            self.assertEqual(accesses[("right", 6)]["access_kind"], "write")
            self.assertEqual(accesses[("left", 7)]["access_kind"], "read_modify_write")
            self.assertTrue(all(row["in_concurrent_context"] for row in accesses.values()))

    def test_classifies_c11_atomic_macro_expansions(self):
        sidecar = load_sidecar()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "atomics.c"
            source.write_text(
                """#include <stdatomic.h>
struct Counters { atomic_int left; atomic_int right; };
int update(struct Counters *state) {
    int value = atomic_load_explicit(&state->left, memory_order_relaxed);
    atomic_store_explicit(&state->right, value, memory_order_relaxed);
    return atomic_fetch_add_explicit(&state->left, 1, memory_order_relaxed);
}
""",
                encoding="utf-8",
            )
            common = {
                "record_name": "Counters",
                "file": str(source),
                "function_name": "update",
                "in_concurrent_context": True,
                "through_shared_indirection": True,
                "through_raw_pointer": True,
                "through_thread_local": False,
                "through_nonescaping_local": False,
                "guard_ids": [],
                "initialization_phase": False,
            }
            request = {
                "schema_version": sidecar.SCHEMA_VERSION,
                "project_root": str(root),
                "cache_line_size": 64,
                "compile_commands": [
                    {
                        "directory": str(root),
                        "file": str(source),
                        "semantic_arguments": ["-std=c11"],
                        "variant_id": "fixture-c11",
                    }
                ],
                "candidate_accesses": [
                    dict(common, field_name="left", line=4, source_access_kind="write"),
                    dict(common, field_name="right", line=5, source_access_kind="read"),
                    dict(common, field_name="left", line=6, source_access_kind="read"),
                ],
            }

            response = sidecar.produce(request)
            self.assertEqual(response["diagnostics"], [])
            accesses = {
                (row["field_name"], row["line"]): row["access_kind"]
                for row in response["accesses"]
            }
            self.assertEqual(accesses[("left", 4)], "read")
            self.assertEqual(accesses[("right", 5)], "write")
            self.assertEqual(accesses[("left", 6)], "read_modify_write")

    def test_parse_errors_do_not_emit_exact_facts(self):
        sidecar = load_sidecar()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "broken.cpp"
            source.write_text(
                """#include <definitely_missing_fsd_header.h>
struct Counters { int left; int right; };
int read_value(Counters *state) { return state->left; }
""",
                encoding="utf-8",
            )
            response = sidecar.produce(
                {
                    "schema_version": sidecar.SCHEMA_VERSION,
                    "project_root": str(root),
                    "cache_line_size": 64,
                    "compile_commands": [
                        {
                            "directory": str(root),
                            "file": str(source),
                            "semantic_arguments": ["-std=c++17"],
                            "variant_id": "broken",
                        }
                    ],
                    "candidate_accesses": [
                        {
                            "record_name": "Counters",
                            "field_name": "left",
                            "file": str(source),
                            "line": 3,
                            "source_access_kind": "write",
                        }
                    ],
                }
            )
            self.assertEqual(response["records"], [])
            self.assertEqual(response["accesses"], [])
            self.assertTrue(response["diagnostics"])

    def test_infers_candidate_tu_without_claiming_exact_layout(self):
        sidecar = load_sidecar()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "local.cpp"
            source.write_text(
                """struct Counters {
    int left;
    int right;
    Counters() { left = 0; right = 0; }
};
void update() {
    Counters local;
    local.left++;
    local.right++;
}
""",
                encoding="utf-8",
            )
            common = {
                "record_name": "Counters",
                "file": str(source),
                "source_access_kind": "read",
                "in_concurrent_context": False,
            }
            response = sidecar.produce(
                {
                    "schema_version": sidecar.SCHEMA_VERSION,
                    "project_root": str(root),
                    "cache_line_size": 64,
                    "compile_commands": [],
                    "candidate_accesses": [
                        dict(common, field_name="left", line=4),
                        dict(common, field_name="right", line=4),
                        dict(common, field_name="left", line=8),
                        dict(common, field_name="right", line=9),
                    ],
                }
            )

            self.assertEqual(response["coverage"]["command_mode"], "inferred_candidate_tus")
            self.assertEqual(response["coverage"]["translation_units_clean"], 1)
            self.assertTrue(response["records"])
            self.assertTrue(all(not row["authoritative"] for row in response["records"]))
            accesses = {(row["field_name"], row["line"]): row for row in response["accesses"]}
            self.assertTrue(accesses[("left", 4)]["initialization_phase"])
            self.assertTrue(accesses[("right", 4)]["initialization_phase"])
            self.assertTrue(accesses[("left", 8)]["through_nonescaping_local"])
            self.assertTrue(accesses[("right", 9)]["through_nonescaping_local"])


if __name__ == "__main__":
    unittest.main()
