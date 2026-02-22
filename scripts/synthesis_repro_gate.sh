#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ART_DIR="$ROOT/artifacts/synthesis_gate"
mkdir -p "$ART_DIR"
cd "$ROOT"

YOSYS_CMD='read_verilog -sv -DSYNTHESIS thielecpu/hardware/rtl/thiele_cpu_kami.v; prep -top mkModule1; check; stat'

echo "[synth] run #1"
yosys -p "$YOSYS_CMD" > "$ART_DIR/synthesis_run1.log" 2>&1

echo "[synth] run #2"
yosys -p "$YOSYS_CMD" > "$ART_DIR/synthesis_run2.log" 2>&1

for run in 1 2; do
  grep -E '=== mkModule1 ===|Number of wires:|Number of wire bits:|Number of public wires:|Number of memories:|Number of memory bits:|Number of processes:|Number of cells:' \
    "$ART_DIR/synthesis_run${run}.log" > "$ART_DIR/stats_run${run}.txt"
  if ! grep -q 'Number of cells:' "$ART_DIR/stats_run${run}.txt"; then
    echo "FAIL: synthesis run ${run} missing cell count"
    exit 1
  fi
done

if ! diff -u "$ART_DIR/stats_run1.txt" "$ART_DIR/stats_run2.txt" > "$ART_DIR/stats_diff.txt"; then
  echo "FAIL: synthesis stats are not reproducible across two runs"
  exit 1
fi

echo "[sim] compile and run extracted RTL testbench"
iverilog -g2012 -Ithielecpu/hardware/rtl -o "$ROOT/build/thiele_cpu_kami_tb.out" \
  thielecpu/hardware/rtl/thiele_cpu_kami.v \
  thielecpu/hardware/testbench/thiele_cpu_kami_tb.v
vvp "$ROOT/build/thiele_cpu_kami_tb.out" +VCD="$ROOT/build/thiele_cpu_tb.vcd" > "$ART_DIR/simulation.log" 2>&1

if ! grep -q '"status"' "$ART_DIR/simulation.log"; then
  echo "FAIL: simulation evidence missing JSON payload"
  exit 1
fi

python3 - <<'PY'
import json
from pathlib import Path
log = Path("artifacts/synthesis_gate/simulation.log").read_text(encoding="utf-8")
start = log.find('{')
if start < 0:
    raise SystemExit("missing JSON start")
decoder = json.JSONDecoder()
payload, _ = decoder.raw_decode(log[start:])
for k in ("mu", "pc", "regs", "mem", "status"):
    if k not in payload:
        raise SystemExit(f"missing key in simulation payload: {k}")
Path("artifacts/synthesis_gate/simulation_payload.json").write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
PY

sha256sum "$ART_DIR"/*.log "$ART_DIR"/*.txt "$ART_DIR"/*.json > "$ART_DIR/checksums.sha256"

echo "[synth] PASS"
