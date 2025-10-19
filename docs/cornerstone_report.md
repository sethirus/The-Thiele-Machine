# Operation Cornerstone: Hardware Reasoning Core Summary

## Overview
Operation Cornerstone replaces the archived residue-mask latch with a hardware stack that performs the nine-node `triadic_cascade` deduction inside the FPGA/ASIC fabric. The implementation spans three artefacts:

1. `hardware/synthesis_trap/reasoning_core.v` — a combinational propagation lattice that evaluates neighbour constraints, eliminates conflicting colours, records a legacy µ-cost activity metric, and reports newly forced vertices.
2. `hardware/synthesis_trap/thiele_graph_solver.v` — a sequential controller that asserts anchor claims, iterates the reasoning core until convergence, applies forced colours, and accumulates the µ-cost register alongside the packed colouring.
3. `coq/modular_proofs/CornerstoneThiele.v` — a Coq formalisation that mirrors the Verilog state machine, proves that the classical enumerator requires 3,786 candidate checks, and establishes that the hardware solver reaches the unique colouring with the same 23-count heuristic in nine cycles.

A Verilog testbench (`thiele_graph_solver_tb.v`) and the updated synthesis harness (`scripts/run_the_synthesis.sh`) exercise the design, regenerate the Yosys netlists, and demonstrate that the µ-cost is measured by gate activity rather than a hand-authored constant.

## Hardware Results
- `reasoning_core.v` exposes a 27-bit mask input (three one-hot colour bits per vertex) and produces:
  - `forced_masks`: the updated masks for forced vertices,
  - `force_valid`: a nine-bit flag identifying which vertices collapsed to a single colour,
  - `activity_count`: the physical µ-cost contribution (eliminated colours plus bookkeeping).
- `thiele_graph_solver.v` uses the core to colour the graph in three propagation rounds after asserting the red/green anchors. The µ-cost accumulator reaches 23 under the hardware's combinational activity model (two anchor claims plus seven forced nodes × (removed colours + 1)). This differs from the μ-spec v2.0 cost used by the Python experiment (≈1302.26 μ-bits).【F:hardware/synthesis_trap/reasoning_core.v†L117-L162】【F:hardware/synthesis_trap/thiele_graph_solver.v†L138-L176】【F:graph_demo_output/triadic_cascade/analysis_report.json†L13-L40】
- `thiele_graph_solver_tb.v` (run with `iverilog -g2012` followed by `vvp`) confirms that the solver reports the expected colouring (`0x24924`) and µ-cost (`23`).
- `scripts/run_the_synthesis.sh` rebuilds the classical baseline and the new Thiele design. Yosys reports:
  - **Classical solver:** 228 cells, 267 wire bits (unchanged).
  - **Thiele graph solver:** 866 cells, 1,237 wire bits with 517 cells inside `reasoning_core`, highlighting that the reasoning lattice is now an explicit physical structure.【F:hardware/synthesis_trap/thiele_graph_solver.log†L74-L112】

## Formal Results
`coq/modular_proofs/CornerstoneThiele.v` instantiates the same stage machine used in Verilog:

- `transition` mirrors the `thiele_graph_solver` state updates (IDLE → CLAIM → PROPAGATE → UPDATE → FINISHED).
- `reasoning_core` implements the same mask eliminations, forced-node detection, and µ-cost arithmetic as the hardware lattice.
- `classical_is_slow` evaluates the base-3 enumerator and confirms that the classical controller needs 3,786 candidates before hitting the valid colouring.
- `thiele_is_fast` and `thiele_pays_the_cost` prove that a nine-cycle input trace leads to the finished state with µ-cost 23 under the legacy counting scheme mirrored by the hardware model.

Running `coqc modular_proofs/CornerstoneThiele.v` after the standard repository setup reproduces these results without additional admits or axioms.

## Reproduction Checklist
1. Install Yosys, Icarus Verilog, and Coq per the root `AGENTS.md` instructions (`sudo apt-get install -y yosys iverilog coq`).
2. Regenerate the synthesis artefacts: `bash scripts/run_the_synthesis.sh`.
3. Simulate the solver: `iverilog -g2012 -o build/thiele_tb hardware/synthesis_trap/reasoning_core.v hardware/synthesis_trap/thiele_graph_solver.v hardware/synthesis_trap/thiele_graph_solver_tb.v && vvp build/thiele_tb`.
4. Recheck the formal model: `cd coq && coqc modular_proofs/CornerstoneThiele.v`.

Each step produces deterministic outputs that align with the values referenced in this report, providing a self-contained audit trail for the new hardware reasoning core.
