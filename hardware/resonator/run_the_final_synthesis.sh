#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BUILD_DIR="${SCRIPT_DIR}/build"

mkdir -p "${BUILD_DIR}"

if ! command -v yosys >/dev/null 2>&1; then
    echo "[resonator] yosys is required for synthesis." >&2
    echo "Install it with: sudo apt-get install -y yosys" >&2
    exit 1
fi

echo "[resonator] Synthesising classical period finder..."
yosys -ql "${BUILD_DIR}/classical.log" -p "read_verilog ${SCRIPT_DIR}/classical_period_finder.v; synth -top classical_period_finder; stat; write_json ${BUILD_DIR}/classical_period_finder.json"

echo "[resonator] Synthesising resonator period finder..."
yosys -ql "${BUILD_DIR}/resonator.log" -p "read_verilog ${SCRIPT_DIR}/period_finder.v; synth -top period_finder; stat; write_json ${BUILD_DIR}/period_finder.json"

echo "[resonator] Reports written to ${BUILD_DIR}"
