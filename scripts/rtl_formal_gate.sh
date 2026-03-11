#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ART_DIR="$ROOT/artifacts/rtl_formal"
mkdir -p "$ART_DIR"
cd "$ROOT"

run_proof() {
  local top="$1"
  local log="$ART_DIR/${top}.log"
  yosys -q -p "read_verilog -formal -sv thielecpu/hardware/rtl/RegFile.v thielecpu/hardware/rtl/thiele_cpu_kami.v thielecpu/hardware/formal/rtl_property_harness.v; prep -top ${top} -flatten; memory_map; opt_clean; sim -clock gclk -n 6" > "$log" 2>&1
}

echo "[formal] proving logic gate enforcement"
run_proof thiele_logic_gate_formal

echo "[formal] proving locality trap"
run_proof thiele_locality_formal

echo "[formal] proving error latch"
run_proof thiele_error_latch_formal

sha256sum "$ART_DIR"/*.log > "$ART_DIR/checksums.sha256"
echo "[formal] PASS"