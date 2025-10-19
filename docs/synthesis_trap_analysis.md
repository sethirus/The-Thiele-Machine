# Synthesis Trap – Empirical Analysis

## Overview
The `scripts/run_the_synthesis.sh` harness now submits two hardware descriptions of the nine-node `triadic_cascade` problem to Yosys: a classical brute-force enumerator (`classical_solver.v`) and the Thiele hardware stack composed of `reasoning_core.v` and the sequential wrapper `thiele_graph_solver.v`. The script emits tool-native logs and JSON netlists under `hardware/synthesis_trap/`, preserving the synthesis oracle's own accounting of each design. Both logs from the reference run are kept in version control so auditors can replay the conclusions without rerunning the toolchain.【F:hardware/synthesis_trap/classical_solver.log†L1-L40】【F:hardware/synthesis_trap/thiele_graph_solver.log†L1-L68】

## Classical Baseline
The classical module encodes a finite-state search across the full \(3^9\) colouring space. Yosys reports 228 logic cells, including 40 flip-flops for the iteration state and a mixture of 68 `$_ANDNOT_` and 43 `$_OR_` gates to evaluate conflict constraints. The design spans 179 wires and 267 wire bits, reflecting the sequential bookkeeping required for the brute-force traversal.【F:hardware/synthesis_trap/classical_solver.log†L1-L40】

Key observations:
- The presence of `$_DFFE_PP0P_` cells shows that state-holding elements dominate the implementation.
- Optimisation passes remove hundreds of redundant wires, signalling that the brute-force loop duplicates constraint logic across iterations.
- The final netlist mirrors the expected exponential search controller from Act I of the laboratory.

## Thiele Graph Solver with Embedded Reasoning
The Thiele hardware now hosts the reasoning itself. `reasoning_core.v` contains the full combinational propagation lattice: for every vertex it masks neighbour colours, removes conflicts, detects forced assignments, and reports a µ-cost proportional to the eliminations performed. `thiele_graph_solver.v` orchestrates anchor claims, repeatedly invokes the reasoning core, applies forced colours, and accumulates the µ-cost register.

Yosys maps the combined design to 866 cells spread across 1,237 wire bits. The standalone `reasoning_core` contributes 517 cells on its own, dominated by `$_ANDNOT_`, `$_OR_`, and `$_XNOR_` instances that hardwire the constraint geometry. The sequential wrapper adds the control state, µ-cost accumulator, and the colour registers that align with the Verilog testbench.【F:hardware/synthesis_trap/thiele_graph_solver.log†L74-L112】

Key observations:
- The reasoning core is now visible as dense combinational fabric rather than an external oracle.
- µ-cost is derived from the combinational elimination counts: every forced deduction reports the number of colours removed plus a bookkeeping unit, and the controller adds that value to `mu_cost`. It is therefore an information-theoretic measure, not a hardware power reading.【F:hardware/synthesis_trap/reasoning_core.v†L117-L162】【F:hardware/synthesis_trap/thiele_graph_solver.v†L138-L176】
- Optimisation passes leave the reasoning lattice intact because the constraint structure is intrinsic to the hardware rather than a pre-solved residue.

## Comparative Interpretation
The synthesis oracle’s own statistics demonstrate a structural gulf between the two artefacts:

| Metric | Classical Solver | Thiele Graph Solver |
| --- | --- | --- |
| Wire bits | 267 | 1,237 |
| Logic cells | 228 | 866 |
| Sequential cells (`$_DFF*`) | 40 | 100 |
| Combinational cells | 188 | 766 |

The classical design preserves the full search frontier in time, whereas the Thiele solver spends silicon to encode the deduction space. The report shows that the Thiele build carries a much larger hardware footprint precisely because the reasoning has moved into gates and flip-flops.

## Reproduction Notes
1. Install Yosys via the repository’s environment instructions (`sudo apt-get install -y yosys`). If the tool is unavailable, the harness streams the archived logs so auditors can still inspect the oracle’s verdict without rebuilding.
2. Run `bash scripts/run_the_synthesis.sh` from the repository root. The harness prints the same resource summary and writes fresh logs and JSON netlists to `hardware/synthesis_trap/` when Yosys is present, falling back to `classical_solver.log`/`thiele_graph_solver.log` otherwise.【F:scripts/run_the_synthesis.sh†L1-L53】
3. Compare the emitted statistics with the reference logs to confirm deterministic behaviour across tool versions.【F:hardware/synthesis_trap/classical_solver.log†L1-L40】【F:hardware/synthesis_trap/thiele_graph_solver.log†L74-L112】

Any deviation in resource counts should be investigated by inspecting the toolchain version, as Yosys optimisations can change between releases. The published logs serve as the canonical baseline for future audits.
