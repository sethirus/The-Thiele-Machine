#!/bin/bash
# ============================================================================
# Thiele CPU FPGA Synthesis Runner (Open-Source Yosys/nextpnr Flow)
# ============================================================================
#
# Requires: yosys, nextpnr-ecp5, ecppack (from Project Trellis)
# Target:   ULX3S (Lattice ECP5, LFE5U-85F-6BG381C)
#
# Usage:
#   ./fpga/run_synthesis.sh           # ECP5 (default)
#   ./fpga/run_synthesis.sh ice40     # iCE40 (experimental)

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RTL_DIR="$REPO_ROOT/thielecpu/hardware/rtl"
BUILD_DIR="$REPO_ROOT/build"

mkdir -p "$BUILD_DIR"

TARGET="${1:-ecp5}"

case "$TARGET" in
  ecp5)
    echo "=== Thiele CPU ECP5 Synthesis ==="
    echo ""

    # Step 1: Yosys synthesis
    if ! command -v yosys &> /dev/null; then
        echo "ERROR: yosys not found. Install: apt install yosys"
        exit 1
    fi
    echo "[1/3] Yosys synthesis..."
    cd "$RTL_DIR"
    yosys synth_ecp5.ys

    # Step 2: Place & route
    if ! command -v nextpnr-ecp5 &> /dev/null; then
        echo "WARNING: nextpnr-ecp5 not found. Synthesis JSON written to build/thiele_ecp5.json"
        echo "Install nextpnr-ecp5 to continue with place & route."
        exit 0
    fi
    echo "[2/3] nextpnr place & route..."
    nextpnr-ecp5 --85k --package CABGA381 \
      --json "$BUILD_DIR/thiele_ecp5.json" \
      --lpf "$REPO_ROOT/fpga/thiele_ecp5.lpf" \
      --textcfg "$BUILD_DIR/thiele_ecp5.config" \
      --lpf-allow-unconstrained

    # Step 3: Bitstream generation
    if ! command -v ecppack &> /dev/null; then
        echo "WARNING: ecppack not found. Config written to build/thiele_ecp5.config"
        echo "Install ecppack (Project Trellis) to generate bitstream."
        exit 0
    fi
    echo "[3/3] ecppack bitstream..."
    ecppack "$BUILD_DIR/thiele_ecp5.config" "$BUILD_DIR/thiele_ecp5.bit"

    echo ""
    echo "Done: $BUILD_DIR/thiele_ecp5.bit"
    echo "Program to FPGA: openFPGALoader -b ulx3s $BUILD_DIR/thiele_ecp5.bit"
    ;;

  ice40)
    echo "=== Thiele CPU iCE40 Synthesis (experimental) ==="
    echo ""
    echo "WARNING: The full mkModule1 design is large (~74k ECP5 cells)."
    echo "iCE40 HX8K may not fit. Use ECP5 target for production."
    echo ""

    if ! command -v yosys &> /dev/null; then
        echo "ERROR: yosys not found. Install: apt install yosys"
        exit 1
    fi
    echo "[1/3] Yosys synthesis..."
    cd "$RTL_DIR"
    yosys synth_ice40.ys

    if ! command -v nextpnr-ice40 &> /dev/null; then
        echo "WARNING: nextpnr-ice40 not found."
        exit 0
    fi
    echo "[2/3] nextpnr place & route..."
    nextpnr-ice40 --hx8k --package bg121 \
      --json "$BUILD_DIR/thiele_ice40.json" \
      --pcf "$REPO_ROOT/fpga/thiele_ice40.pcf" \
      --asc "$BUILD_DIR/thiele_ice40.asc"

    if ! command -v icepack &> /dev/null; then
        echo "WARNING: icepack not found."
        exit 0
    fi
    echo "[3/3] icepack bitstream..."
    icepack "$BUILD_DIR/thiele_ice40.asc" "$BUILD_DIR/thiele_ice40.bin"

    echo ""
    echo "Done: $BUILD_DIR/thiele_ice40.bin"
    ;;

  *)
    echo "Usage: $0 [ecp5|ice40]"
    exit 1
    ;;
esac
