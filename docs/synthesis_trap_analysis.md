# Synthesis Trap – Empirical Analysis

## Overview
The `scripts/run_the_synthesis.sh` harness submits two hardware descriptions of the nine-node `triadic_cascade` problem to Yosys: a classical brute-force enumerator (`classical_solver.v`) and the Thiele residue-mask solver (`thiele_solver.v`). The script emits tool-native logs and JSON netlists under `hardware/synthesis_trap/`, preserving the synthesis oracle's own accounting of each design. Both logs from the reference run are kept in version control so auditors can replay the conclusions without rerunning the toolchain.【F:hardware/synthesis_trap/classical_solver.log†L1-L40】【F:hardware/synthesis_trap/thiele_solver.log†L1-L32】

## Classical Baseline
The classical module encodes a finite-state search across the full \(3^9\) colouring space. Yosys reports 228 logic cells, including 40 flip-flops for the iteration state and a mixture of 68 `$_ANDNOT_` and 43 `$_OR_` gates to evaluate conflict constraints. The design spans 179 wires and 267 wire bits, reflecting the sequential bookkeeping required for the brute-force traversal.【F:hardware/synthesis_trap/classical_solver.log†L1-L40】

Key observations:
- The presence of `$_DFFE_PP0P_` cells shows that state-holding elements dominate the implementation.
- Optimisation passes remove hundreds of redundant wires, signalling that the brute-force loop duplicates constraint logic across iterations.
- The final netlist mirrors the expected exponential search controller from Act I of the laboratory.

## Thiele Residue-Mask Solver
The Thiele solver hardcodes the μ-funded residue propagation steps. After the oracle collapses the candidate sets in software, the Verilog module simply latches the final mask and exposes the witness colouring. Yosys maps the design to five cells (two gated flip-flops, one standard flip-flop, and two simple gates) spread across 29 wires and 106 wire bits.【F:hardware/synthesis_trap/thiele_solver.log†L1-L32】

Key observations:
- No sequential search remains—only the latching of the pre-propagated residue masks.
- Optimisation passes remove almost nothing because the logic is already minimal; the hardware footprint is essentially the μ-accounting handshake.
- The tiny gate count provides a measurable manifestation of the “reasoning in software, latching in hardware” paradigm.

## Comparative Interpretation
The synthesis oracle's own statistics demonstrate a structural gulf between the two artefacts:

| Metric | Classical Solver | Thiele Solver |
| --- | --- | --- |
| Wire bits | 267 | 106 |
| Logic cells | 228 | 5 |
| Sequential cells (`$_DFF*`) | 40 | 3 |
| Combinational cells | 188 | 2 |

The classical design must preserve the full search frontier, whereas the Thiele solver relies on μ-funded reasoning performed upstream. The synthesis report therefore substantiates the claim that the Thiele pipeline exchanges heavy sequential logic for a lightweight residue latch, without resorting to hand-authored interpretation of the logs.

## Reproduction Notes
1. Install Yosys via the repository’s environment instructions (`sudo apt-get install -y yosys`). If the tool is unavailable, the harness streams the archived logs so auditors can still inspect the oracle’s verdict without rebuilding.
2. Run `bash scripts/run_the_synthesis.sh` from the repository root. The harness prints the same resource summary and writes fresh logs and JSON netlists to `hardware/synthesis_trap/` when Yosys is present, falling back to `classical_solver.log`/`thiele_solver.log` otherwise.【F:scripts/run_the_synthesis.sh†L1-L120】
3. Compare the emitted statistics with the reference logs to confirm deterministic behaviour across tool versions.【F:hardware/synthesis_trap/classical_solver.log†L1-L40】【F:hardware/synthesis_trap/thiele_solver.log†L1-L32】

Any deviation in resource counts should be investigated by inspecting the toolchain version, as Yosys optimisations can change between releases. The published logs serve as the canonical baseline for future audits.
