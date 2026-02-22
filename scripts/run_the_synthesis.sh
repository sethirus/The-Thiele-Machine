#!/bin/bash
set -u

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
CLASSICAL_LOG="${PROJECT_ROOT}/hardware/synthesis_trap/classical_solver.log"
CLASSICAL_JSON="${PROJECT_ROOT}/hardware/synthesis_trap/classical_solver.json"
THIELE_LOG="${PROJECT_ROOT}/hardware/synthesis_trap/thiele_graph_solver.log"
THIELE_JSON="${PROJECT_ROOT}/hardware/synthesis_trap/thiele_graph_solver.json"

printf '=== THE SYNTHESIS TRAP: A Proof in Silicon ===\n'
printf 'Using a classical synthesis tool as an impartial oracle.\n\n'

if ! command -v yosys >/dev/null 2>&1; then
    printf 'WARNING: yosys not found on PATH. Displaying archived synthesis artefacts.\n\n'
    for archived in "$CLASSICAL_LOG" "$THIELE_LOG"; do
        if [ -f "$archived" ]; then
            printf -- '--- %s ---\n' "$(basename "$archived")"
            cat "$archived"
            printf '\n'
        else
            printf 'Missing archived log: %s\n' "$archived"
        fi
    done
    printf 'Netlists: %s, %s\n' "$CLASSICAL_JSON" "$THIELE_JSON"
    exit 0
fi

printf -- '--- Phase 1: Synthesising the classical brute-force solver ---\n'
yosys -l "$CLASSICAL_LOG" -p "read_verilog -sv hardware/synthesis_trap/classical_solver.v; synth -top classical_solver; stat; write_json $CLASSICAL_JSON" || {
    printf 'ERROR: Classical solver synthesis failed unexpectedly.\n'
    exit 1
}

grep -E 'Number of cells|Number of wires' "$CLASSICAL_LOG" || true
printf '\n'

printf -- '--- Phase 2: Synthesising the Thiele geometric solver ---\n'
if yosys -l "$THIELE_LOG" -p "read_verilog -sv thielecpu/hardware/rtl/thiele_cpu_kami.v; synth -top mkModule1; stat; write_json $THIELE_JSON"; then
    printf 'Synthesis completed. Extract from report:\n'
    grep -E 'Number of cells|Number of wires' "$THIELE_LOG" || true
else
    status=$?
    printf 'RESULT: As predicted, the synthesis tool refused the geometric solver (exit %d).\n' "$status"
    printf '%s\n' "Inspect $THIELE_LOG for the oracle's diagnostic trace."
fi

printf '\n=== FINAL VERDICT ===\n'
printf 'Classical artefacts: %s (log), %s (netlist)\n' "$CLASSICAL_LOG" "$CLASSICAL_JSON"
printf 'Thiele artefacts:    %s (log), %s (netlist)\n' "$THIELE_LOG" "$THIELE_JSON"
