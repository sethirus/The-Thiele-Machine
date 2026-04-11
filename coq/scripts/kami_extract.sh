#!/bin/bash
# kami_extract.sh — Full pipeline: Coq (Kami) -> OCaml -> Bluespec -> Verilog
#
# Usage: ./scripts/kami_extract.sh [OPTIONS] [--top MODULE_NAME]
#
# Options:
#   --skip-coq          Skip Phases 1-2 (Coq compilation/extraction).
#                       Use when Target.ml already exists in build/kami_hw/.
#   --top MODULE_NAME   Set the BSV top module name (default: ThieleCPU)
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
TRACKED_RTL="$ROOT/thielecpu/hardware/rtl/thiele_cpu_kami.v"

# Parse arguments
SKIP_COQ=0
TOP_MODULE="ThieleCPU"
while [[ $# -gt 0 ]]; do
    case "$1" in
        --skip-coq)
            SKIP_COQ=1
            shift
            ;;
        --top)
            TOP_MODULE="$2"
            shift 2
            ;;
        *)
            TOP_MODULE="$1"
            shift
            ;;
    esac
done

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

# Build COQFLAGS from _CoqProject (all paths are relative to COQ_DIR)
cd "$COQ_DIR"
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

if [ "$SKIP_COQ" -eq 1 ]; then
    echo "=== Skipping Phases 1-2 (--skip-coq): Using existing Target.ml ==="
    if [ ! -f "$BUILD_DIR/Target.ml" ]; then
        echo "ERROR: Target.ml not found in $BUILD_DIR"
        echo "Remove --skip-coq to rebuild from kami_hw sources."
        exit 1
    fi
    # Only clean BSV/Verilog artifacts, preserve Target.ml
    find "$BUILD_DIR" -maxdepth 1 -type f \( -name '*.v' -o -name '*.bsv' -o -name 'kami_to_bsv*' \) -delete
else
    echo "=== Preflight: Reset stale kami_hw artifacts (namespace-safe rebuild) ==="
    find "$COQ_KAMI_DIR" -maxdepth 1 -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' \) -delete
    find "$BUILD_DIR" -maxdepth 1 -type f \( -name '*.v' -o -name '*.bsv' -o -name 'Target.*' -o -name 'Main.*' -o -name 'PP.*' -o -name 'kami_to_bsv*' \) -delete

    echo "=== Phase 1: Compiling Kami modules in Coq ==="
    cd "$COQ_DIR"
    # Compile each kami_hw file from COQ_DIR (coqc writes .vo next to .v)
    for f in ThieleTypes ThieleCPUCore Compatibility Abstraction ThieleCPUBusTop VerilogRefinement CanonicalCPUProof; do
        eval "coqc $COQFLAGS kami_hw/${f}.v"
    done

    echo "=== Phase 2: Extracting to OCaml (Target.ml) ==="
    cd "$COQ_DIR"
    eval "coqc $COQFLAGS kami_hw/KamiExtraction.v"
fi

echo "=== Phase 3: Compiling OCaml -> Bluespec pretty-printer ==="
cd "$BUILD_DIR"
# Regenerate Target.mli from current Target.ml to handle name differences
# between monolithic and modular extraction (e.g. kami_read_mem vs read_mem)
ocamlfind ocamlopt -package str -linkpkg -i Target.ml > Target.mli 2>/dev/null || true
cp "$VENDOR_KAMI/Kami/Ext/Ocaml/PP.ml" .
cp "$VENDOR_KAMI/Kami/Ext/Ocaml/Main.ml" .
cp "$VENDOR_KAMI/Kami/Ext/Ocaml/Header.bsv" .
# Check which variant Target.ml uses and normalize PP.ml to match.
# Coq extraction sometimes emits Nil1 (Coq 8.18+) or Nil (older/different configs).
if grep -q "| Nil1$" Target.ml 2>/dev/null; then
    perl -0777 -pe 's/\bNil\b/Nil1/g' -i PP.ml
elif grep -q "| Nil$" Target.ml 2>/dev/null; then
    echo "  (Target.ml uses Nil - no PP.ml patching needed)"
fi
# Use project-specific Header.bsv without unused SimpleBRAM import.
if [ -f "$ROOT/scripts/Header.bsv" ]; then
    cp "$ROOT/scripts/Header.bsv" .
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

echo "=== Phase 4b: RegFile transform (large Vector registers -> RegFile) ==="
# BSC cannot elaborate mkReg(unpack(0)) for Vector#(4096, ...) — stack overflow.
# Replace Reg#(Vector#(N, T)) with RegFile#(Bit#(log2(N)), T) for N >= 256,
# rewriting reads to .sub() and writes to .upd(). Logic is unchanged.
python3 "$ROOT/scripts/bsv_regfile_transform.py" thiele_hw_clean.bsv thiele_hw_clean.bsv

# Compile vendor BSV packages (RegFileZero, MulDiv) needed by thiele_hw_clean.bsv.
# These packages live in the Kami BSV frontend directory; we compile them into the
# build dir so Phase 5 can find their .bo files on its search path.
BSV_VENDOR_DIR="$VENDOR_KAMI/Kami/Ext/BluespecFrontEnd/verilog"
if [ "$BSC_AVAILABLE" != "0" ]; then
    for pkg in RegFileZero MulDiv; do
        BSV_SRC="$BSV_VENDOR_DIR/${pkg}.bsv"
        if [ -f "$BSV_SRC" ] && [ ! -f "${pkg}.bo" ]; then
            echo "  Compiling ${pkg}.bsv..."
            "$BSC" -verilog -bdir . -p "$BLUESPECDIR/Libraries:." "$BSV_SRC" 2>&1
        fi
    done
fi

echo "=== Phase 5: Compiling Bluespec -> Verilog ==="
# Compile each module found in the BSV
if [ "$BSC_AVAILABLE" = "0" ]; then
    echo "  SKIPPED: bsc not available. Install Bluespec to complete Phase 5."
    echo "  BSV artifact: $BUILD_DIR/thiele_hw.bsv (ready for bsc when available)"
else
REGFILE_ZERO_DIR="$VENDOR_KAMI/Kami/Ext/BluespecFrontEnd/verilog"
for mod in $(grep -oP 'module (mk\w+)' thiele_hw_clean.bsv | awk '{print $2}'); do
    echo "  Compiling $mod..."
    "$BSC" +RTS -K64M -RTS -verilog -g "$mod" -p "$BLUESPECDIR/Libraries:$REGFILE_ZERO_DIR:." thiele_hw_clean.bsv 2>&1
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
    [[ "$vfile" == *_synth.v ]] && continue  # Skip already-transformed files
    synth_out="${vfile%.v}_synth.v"
    echo "  Transforming $vfile → $synth_out..."
    python3 "$ROOT/scripts/verilog_synth_transform.py" "$vfile" "$synth_out" 2>&1
done
fi

echo "=== Phase 5c: Publishing canonical synth RTL ==="
if [ "$BSC_AVAILABLE" = "0" ]; then
    echo "  SKIPPED: bsc not available. Tracked RTL not refreshed."
elif [ ! -f "$BUILD_DIR/mkModule1_synth.v" ]; then
    echo "  WARNING: $BUILD_DIR/mkModule1_synth.v not found; tracked RTL not refreshed."
else
    install -m 0644 "$BUILD_DIR/mkModule1_synth.v" "$TRACKED_RTL"
    echo "  Published mkModule1_synth.v -> $TRACKED_RTL"
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
        [[ "$vfile" == *_synth_synth.v ]] && continue
        echo "  Checking $vfile..."
        REGFILE_V="$ROOT/thielecpu/hardware/rtl/RegFile.v"
        MOD_NAME=$(basename "$vfile" _synth.v)
        if [ -f "$REGFILE_V" ]; then
            yosys -q -p "read_verilog -sv -DSYNTHESIS $REGFILE_V $vfile; prep -top $MOD_NAME; check; stat" 2>&1 || echo "  WARNING: $vfile failed synthesis"
        else
            yosys -q -p "read_verilog -sv -DSYNTHESIS $vfile; prep -top $MOD_NAME; check; stat" 2>&1 || echo "  WARNING: $vfile failed synthesis"
        fi
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
