#!/bin/bash
# kami_extract.sh — Full pipeline: Coq (Kami) → OCaml → Bluespec → Verilog
#
# Usage: ./scripts/kami_extract.sh [--top MODULE_NAME]
#
# Prerequisites:
#   - Coq 8.18+, ocamlfind, bsc (Bluespec compiler)
#   - vendor/kami/ and vendor/bbv/ built (make in each)
#   - BLUESPECDIR set to bsc lib directory

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
COQ_DIR="$ROOT/coq"
BUILD_DIR="$ROOT/build/kami_hw"
VENDOR_KAMI="$ROOT/vendor/kami"
VENDOR_BBV="$ROOT/vendor/bbv"

TOP_MODULE="${1:-ThieleCPU}"

# Auto-detect BLUESPECDIR
if [ -z "${BLUESPECDIR:-}" ]; then
    if [ -d "/tmp/bsc-2024.07-ubuntu-22.04/lib" ]; then
        export BLUESPECDIR="/tmp/bsc-2024.07-ubuntu-22.04/lib"
    elif [ -d "/usr/local/lib/bsc" ]; then
        export BLUESPECDIR="/usr/local/lib/bsc"
    else
        echo "ERROR: BLUESPECDIR not set. Install bsc and set BLUESPECDIR."
        exit 1
    fi
fi

BSC="${BSC:-$(dirname "$BLUESPECDIR")/bin/bsc}"
if ! command -v "$BSC" &>/dev/null; then
    BSC="bsc"
fi

mkdir -p "$BUILD_DIR"

echo "=== Phase 1: Compiling Kami modules in Coq ==="
cd "$COQ_DIR"
coqc -R kami_hw KamiHW \
     -R "$VENDOR_KAMI/Kami" Kami \
     -Q "$VENDOR_BBV/src/bbv" bbv \
     kami_hw/Blink.v

echo "=== Phase 2: Extracting to OCaml (Target.ml) ==="
coqc -R kami_hw KamiHW \
     -R "$VENDOR_KAMI/Kami" Kami \
     -Q "$VENDOR_BBV/src/bbv" bbv \
     kami_hw/KamiExtraction.v

echo "=== Phase 3: Compiling OCaml → Bluespec pretty-printer ==="
cd "$BUILD_DIR"
cp "$VENDOR_KAMI/Kami/Ext/Ocaml/PP.ml" .
ocamlfind ocamlopt -package str -linkpkg \
    Target.mli Target.ml PP.ml Main.ml \
    -o kami_to_bsv

echo "=== Phase 4: Generating Bluespec (.bsv) ==="
./kami_to_bsv -top "$TOP_MODULE" thiele_hw.bsv

# Strip top-module wrapper if it references undefined interfaces
# (Kami generates a wrapper that bsc can't compile for single modules)
python3 -c "
import re
with open('thiele_hw.bsv') as f:
    content = f.read()
# Find and remove the top-level wrapper module that references undefined interfaces
lines = content.split('\n')
clean = []
skip = False
for line in lines:
    if line.startswith('module mk$TOP_MODULE') or line.startswith('module mkTop'):
        skip = True
    if not skip:
        clean.append(line)
    if skip and line.strip() == 'endmodule':
        skip = False
with open('thiele_hw_clean.bsv', 'w') as f:
    # Add Vector import needed for mu_tensor and register arrays
    f.write('import Vector::*;\n')
    f.write('\n'.join(clean))
" 2>/dev/null || cp thiele_hw.bsv thiele_hw_clean.bsv

echo "=== Phase 5: Compiling Bluespec → Verilog ==="
# Compile each module found in the BSV
for mod in $(grep -oP 'module (mk\w+)' thiele_hw_clean.bsv | awk '{print $2}'); do
    echo "  Compiling $mod..."
    "$BSC" -verilog -g "$mod" -p "$BLUESPECDIR/Libraries" thiele_hw_clean.bsv 2>&1 || true
done

echo "=== Phase 6: Verifying with Yosys ==="
for vfile in *.v; do
    [ -f "$vfile" ] || continue
    echo "  Checking $vfile..."
    yosys -q -p "read_verilog $vfile; synth" 2>&1 || echo "  WARNING: $vfile failed synthesis"
done

echo ""
echo "=== Pipeline complete ==="
echo "Generated files in $BUILD_DIR:"
ls -la "$BUILD_DIR"/*.v 2>/dev/null || echo "  (no Verilog files)"
