#!/bin/bash
# fpga_build.sh — Full FPGA build pipeline for Thiele CPU
#
# Runs:  yosys (synthesis) → nextpnr-ecp5 (place & route) → ecppack (bitstream)
#
# Usage:
#   ./scripts/fpga_build.sh [--board ulx3s|colorlight] [--skip-synth]
#
# Output:
#   build/thiele_ecp5.json   — Yosys netlist
#   build/thiele_ecp5.config — nextpnr output
#   build/thiele_ecp5.bit    — FPGA bitstream
#
# Prerequisites:
#   yosys, nextpnr-ecp5, ecppack (from prjtrellis)

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RTL_DIR="$ROOT/thielecpu/hardware/rtl"
BUILD_DIR="$ROOT/build"

# Defaults
BOARD="ulx3s"
SKIP_SYNTH=false
DEVICE="--85k"
PACKAGE="CABGA381"
SPEED="6"

# Parse args
while [[ $# -gt 0 ]]; do
    case "$1" in
        --board)    BOARD="$2"; shift 2 ;;
        --skip-synth) SKIP_SYNTH=true; shift ;;
        *)          echo "Unknown arg: $1"; exit 1 ;;
    esac
done

# Board-specific LPF selection
case "$BOARD" in
    ulx3s)
        LPF="$RTL_DIR/ulx3s.lpf"
        ;;
    *)
        echo "Unsupported board: $BOARD (supported: ulx3s)"
        echo "Create an LPF file for your board at $RTL_DIR/<board>.lpf"
        exit 1
        ;;
esac

mkdir -p "$BUILD_DIR"

# ──────────────────────────────────────────────────────────────────────
phase() { echo ""; echo "=== FPGA BUILD: $1 ==="; echo ""; }
# ──────────────────────────────────────────────────────────────────────

# Phase 1: Yosys synthesis
if [ "$SKIP_SYNTH" = false ] || [ ! -f "$BUILD_DIR/thiele_ecp5.json" ]; then
    phase "SYNTHESIS (yosys)"
    cd "$RTL_DIR"
    yosys synth_ecp5.ys 2>&1 | tee "$BUILD_DIR/yosys.log"
    cd "$ROOT"
    echo "Netlist: $BUILD_DIR/thiele_ecp5.json"
else
    echo "Skipping synthesis (--skip-synth, netlist exists)"
fi

# Phase 2: Place & Route
phase "PLACE & ROUTE (nextpnr-ecp5)"
nextpnr-ecp5 \
    $DEVICE \
    --package "$PACKAGE" \
    --speed "$SPEED" \
    --json "$BUILD_DIR/thiele_ecp5.json" \
    --lpf "$LPF" \
    --textcfg "$BUILD_DIR/thiele_ecp5.config" \
    --freq 25 \
    --seed 42 \
    2>&1 | tee "$BUILD_DIR/nextpnr.log"

echo "Config: $BUILD_DIR/thiele_ecp5.config"

# Phase 3: Bitstream generation
phase "BITSTREAM (ecppack)"
ecppack \
    --svf "$BUILD_DIR/thiele_ecp5.svf" \
    "$BUILD_DIR/thiele_ecp5.config" \
    "$BUILD_DIR/thiele_ecp5.bit"

echo "Bitstream: $BUILD_DIR/thiele_ecp5.bit"
echo "SVF:       $BUILD_DIR/thiele_ecp5.svf"

# Summary
phase "DONE"
ls -lh "$BUILD_DIR/thiele_ecp5.json" "$BUILD_DIR/thiele_ecp5.config" "$BUILD_DIR/thiele_ecp5.bit"
echo ""
echo "To program ULX3S via USB:"
echo "  fujprog $BUILD_DIR/thiele_ecp5.bit"
echo ""
echo "To load a program via UART (after programming):"
echo "  python3 scripts/fpga_upload.py --port /dev/ttyUSB0 program.bin"
