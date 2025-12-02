#!/usr/bin/env bash
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

# Run Verilog simulation and produce trace for isomorphism verification

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
HW_DIR="$REPO_ROOT/hardware"
BUILD_DIR="$REPO_ROOT/build"

# Create build directory
mkdir -p "$BUILD_DIR"

echo "=== Verilog Trace Generation ==="
echo "Hardware dir: $HW_DIR"
echo "Build dir: $BUILD_DIR"

# Check for iverilog
if ! command -v iverilog &> /dev/null; then
    echo "Error: iverilog not found. Please install with:"
    echo "  sudo apt install iverilog"
    exit 1
fi

# Compile Verilog
echo ""
echo "Compiling Verilog..."
iverilog -g2012 \
    -o "$BUILD_DIR/partition_core_tb" \
    "$HW_DIR/partition_core.v" \
    "$HW_DIR/partition_core_tb.v"

# Run simulation
echo "Running simulation..."
cd "$BUILD_DIR"
vvp partition_core_tb

# Check output
if [ -f "hw_trace.json" ]; then
    echo ""
    echo "=== Trace Generated ==="
    cat hw_trace.json
    echo ""
    echo "Trace file: $BUILD_DIR/hw_trace.json"
else
    echo "Error: Trace file not generated"
    exit 1
fi
