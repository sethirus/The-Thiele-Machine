#!/bin/bash
# kami_extract.sh — Full pipeline: Coq (Kami) -> OCaml -> Bluespec -> Verilog
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
COQ_KAMI_DIR="$COQ_DIR/kami_hw"
BUILD_DIR="$ROOT/build/kami_hw"
VENDOR_KAMI="$ROOT/vendor/kami"
VENDOR_BBV="$ROOT/vendor/bbv"

TOP_MODULE="${1:-ThieleCPU}"

# Auto-detect BLUESPECDIR (optional — only needed for Phase 5 Verilog synthesis)
if [ -z "${BLUESPECDIR:-}" ]; then
    if [ -d "/tmp/bsc-2024.07-ubuntu-22.04/lib" ]; then
        export BLUESPECDIR="/tmp/bsc-2024.07-ubuntu-22.04/lib"
    elif [ -f "/usr/local/lib/Libraries/Prelude.bo" ]; then
        export BLUESPECDIR="/usr/local/lib"
    elif [ -d "/usr/local/lib/bsc" ]; then
        export BLUESPECDIR="/usr/local/lib/bsc"
    else
        BLUESPECDIR=""
    fi
fi

BSC="${BSC:-$(dirname "$BLUESPECDIR")/bin/bsc}"
if ! command -v "$BSC" &>/dev/null; then
    BSC="bsc"
fi

BSC_AVAILABLE=1
if ! command -v "$BSC" &>/dev/null; then
    echo "WARNING: bsc compiler not found. Phases 1-4 (Coq→OCaml→BSV) will run; Phase 5+ (BSV→Verilog) will be skipped."
    BSC_AVAILABLE=0
fi

export OCAMLRUNPARAM="${OCAMLRUNPARAM:-l=500M}"

mkdir -p "$BUILD_DIR"

echo "=== Preflight: Reset stale kami_hw artifacts (namespace-safe rebuild) ==="
find "$COQ_KAMI_DIR" -maxdepth 1 -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' \) -delete
find "$BUILD_DIR" -maxdepth 1 -type f \( -name '*.v' -o -name '*.bsv' -o -name 'Target.*' -o -name 'Main.*' -o -name 'PP.*' -o -name 'kami_to_bsv*' \) -delete

echo "=== Phase 1: Compiling Kami modules in Coq ==="
cd "$COQ_DIR"
# Build COQFLAGS from _CoqProject (all paths are relative to COQ_DIR)
COQFLAGS=""
while IFS= read -r line; do
    case "$line" in
        -R\ *|-Q\ *) COQFLAGS="$COQFLAGS $line" ;;
    esac
done < "$COQ_DIR/_CoqProject"
# Replace relative vendor paths with absolute ones
COQFLAGS=$(echo "$COQFLAGS" | sed \
    "s|../vendor/kami/Kami|$VENDOR_KAMI/Kami|g" \
    | sed "s|../vendor/bbv/src/bbv|$VENDOR_BBV/src/bbv|g")

# Compile each kami_hw file from COQ_DIR (coqc writes .vo next to .v)
for f in Blink ThieleTypes ThieleCPUCore Compatibility Abstraction ThieleCPUBusTop VerilogRefinement CanonicalCPUProof; do
    eval "coqc $COQFLAGS kami_hw/${f}.v"
done

echo "=== Phase 2: Extracting to OCaml (Target.ml) ==="
cd "$COQ_DIR"
eval "coqc $COQFLAGS kami_hw/KamiExtraction.v"

echo "=== Phase 3: Compiling OCaml -> Bluespec pretty-printer ==="
cd "$BUILD_DIR"
cp "$VENDOR_KAMI/Kami/Ext/Ocaml/PP.ml" .
cp "$VENDOR_KAMI/Kami/Ext/Ocaml/Main.ml" .
cp "$VENDOR_KAMI/Kami/Ext/Ocaml/Header.bsv" .
# Coq 8.18 extraction emits Nil1 in Target.ml while upstream PP.ml still matches Nil.
# Normalize PP pattern matches for compatibility with extracted Target type constructors.
perl -0777 -pe 's/\bNil\b/Nil1/g' -i PP.ml
# Coq 8.18+ extraction uses canonical_cpu_module; Main.ml expects targetB.
# Add shim alias so the entry point resolves without modifying vendor files.
if ! grep -q 'targetB' Target.ml; then
    printf '\n(** val targetB : int -> bModule list option **)\n' >> Target.ml
    printf 'let targetB _ = canonical_cpu_module\n' >> Target.ml
fi
if ! grep -q 'targetB' Target.mli; then
    printf '\nval targetB : int -> bModule list option\n' >> Target.mli
fi
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
lines = content.split('\\n')
clean = []
skip = False
for line in lines:
    if line.startswith('module mkThieleCPU') or line.startswith('module mkTop') or line.startswith('module mk$TOP_MODULE'):
        skip = True
    if not skip:
        clean.append(line)
    if skip and line.strip() == 'endmodule':
        skip = False
with open('thiele_hw_clean.bsv', 'w') as f:
    # Add Vector import needed for mu_tensor and register arrays
    f.write('import Vector::*;\\n')
    f.write('\\n'.join(clean))
" 2>/dev/null || cp thiele_hw.bsv thiele_hw_clean.bsv

# Bluespec 2024.07 in this environment does not resolve `vec(...)` constructors
# emitted by Kami extraction; rewrite them to explicit unpacked concatenations.
python3 - <<'PY'
import re
p='thiele_hw_clean.bsv'
s=open(p).read()
s=re.sub(r'vec\(([^()]*)\)', r'unpack({\1})', s)
open(p,'w').write(s)
PY

# SimpleBRAM is imported by Kami extraction boilerplate but unused in the module body.
# It is not in the standard BSC library and has no pre-compiled .bo file — remove it.
sed -i '/^import SimpleBRAM::\*;/d' thiele_hw_clean.bsv

echo "=== Phase 5: Compiling Bluespec -> Verilog ==="
# Compile each module found in the BSV
if [ "$BSC_AVAILABLE" = "0" ]; then
    echo "  SKIPPED: bsc not available. Install Bluespec to complete Phase 5."
    echo "  BSV artifact: $BUILD_DIR/thiele_hw.bsv (ready for bsc when available)"
else
for mod in $(grep -oP 'module (mk\w+)' thiele_hw_clean.bsv | awk '{print $2}'); do
    echo "  Compiling $mod..."
    "$BSC" -verilog -g "$mod" -p "$BLUESPECDIR/Libraries:." thiele_hw_clean.bsv 2>&1
done
fi

echo "=== Phase 5b: Post-processing for synthesis (flat regs → arrays) ==="
# The BSC output flattens Kami vectors into individual scalar registers or
# wide bit-vectors. The synth transform replaces these with proper Verilog
# arrays while preserving all logic exactly.
if [ "$BSC_AVAILABLE" = "0" ]; then
    echo "  SKIPPED: bsc not available."
else
for vfile in *.v; do
    [ -f "$vfile" ] || continue
    synth_out="${vfile%.v}_synth.v"
    echo "  Transforming $vfile → $synth_out..."
    python3 "$ROOT/scripts/verilog_synth_transform.py" "$vfile" "$synth_out" 2>&1
done
fi

if [ "${SKIP_YOSYS:-0}" = "1" ] || [ "$BSC_AVAILABLE" = "0" ]; then
    if [ "$BSC_AVAILABLE" = "0" ]; then
        echo "=== Phase 6: Verifying with Yosys (skipped: bsc not available) ==="
    else
        echo "=== Phase 6: Verifying with Yosys (skipped: SKIP_YOSYS=1) ==="
    fi
else
    echo "=== Phase 6: Verifying with Yosys ==="
    for vfile in *_synth.v; do
        [ -f "$vfile" ] || continue
        echo "  Checking $vfile..."
        yosys -q -p "read_verilog $vfile; synth" 2>&1 || echo "  WARNING: $vfile failed synthesis"
    done
fi

echo ""
echo "=== Pipeline complete ==="
echo "Generated files in $BUILD_DIR:"
ls -la "$BUILD_DIR"/*.bsv 2>/dev/null || echo "  (no BSV files)"
ls -la "$BUILD_DIR"/*.v   2>/dev/null || echo "  (no Verilog files — run with bsc to generate)"
echo ""
echo "Synthesis-ready files:"
ls -la "$BUILD_DIR"/*_synth.v 2>/dev/null || echo "  (none — requires bsc for Verilog generation)"
