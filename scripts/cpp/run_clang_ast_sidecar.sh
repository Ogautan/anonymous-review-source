#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PYTHON_BIN=${FSD_CLANG_PYTHON:-python3}

exec "$PYTHON_BIN" "$SCRIPT_DIR/clang_ast_sidecar.py"
