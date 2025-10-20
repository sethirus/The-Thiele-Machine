# Operation Cornerstone: Autonomous Hardware Oracle Report

## Executive Summary
Cornerstone now culminates in a self-contained hardware oracle.  The
parameterised `reasoning_core` performs combinational constraint propagation,
and the sequential controllers have been unified: the historical scripted solver
remains for comparison, while `thiele_autonomous_solver.v` performs its own
search, backtracking, and μ-ledger accumulation on chip.  The μ-spec v2.0 metrics
reported by the hardware match the Python laboratory exactly, completing the
hardware pillar of the thesis.

## Reasoning Fabric (`reasoning_core.v`)
* Accepts runtime-programmable adjacency matrices and per-node μ-question costs.
* Emits forced masks, validity flags, legacy activity counts, and μ-spec v2.0
  question/information gains for every propagation step.【F:hardware/synthesis_trap/reasoning_core.v†L14-L132】
* Instantiated by both controllers without modification, enabling solver choice
  at synthesis time.

## Scripted Solver (`thiele_graph_solver.v`)
The historical controller asserts the anchor claims and iterates the reasoning
fabric until convergence, updating the packed colouring and μ-ledger registers.
It remains in the repository as a baseline for auditors comparing against the new
autonomous design.【F:hardware/synthesis_trap/thiele_graph_solver.v†L1-L192】

## Autonomous Solver (`thiele_autonomous_solver.v`)
* Accepts the same adjacency matrix and question-bit parameters as the scripted
  solver.
* Implements chronological backtracking: after propagation stalls, it selects a
  node, speculatively commits a colour, and retreats on conflict.
* Accumulates μ-question bits, μ-information gain (Q16), μ-total (Q16), and the
  legacy activity counter entirely in hardware while tracking decision depth and
  backtrack count.【F:hardware/synthesis_trap/thiele_autonomous_solver.v†L1-L200】

## Unified Testbench (`thiele_graph_solver_tb.v`)
The dual-solver testbench exercises both controllers against the triadic cascade
instance.  It enforces the legacy activity target (23), the μ-question total
(1,288 bits), the information gain (934,848 Q16), and the combined μ-total
(85,345,216 Q16) for both implementations, ensuring exact agreement with the
Python receipts.【F:hardware/synthesis_trap/thiele_graph_solver_tb.v†L129-L179】

## Synthesis Results
Running Yosys with SystemVerilog support confirms the resource profile of the
hardware oracle:

| Design | Wires | Cells |
| --- | --- | --- |
| Classical brute-force solver | 179 | 228 |
| Thiele graph solver (including reasoning core) | 918 | 1,231 |

Detailed statistics are recorded in `audit_logs/agent_hardware_verification.log`
for independent inspection.【F:audit_logs/agent_hardware_verification.log†L780-L809】【F:audit_logs/agent_hardware_verification.log†L4238-L4275】

## Reproduction Checklist
1. Install Yosys and Icarus Verilog (`apt-get install -y yosys iverilog`).
2. Run `scripts/run_the_synthesis.sh` to rebuild both designs (Yosys ≥ 0.33
   accepts the SystemVerilog sources via `read_verilog -sv`).
3. Simulate with `iverilog -g2012` and `vvp build/thiele_tb` to verify the μ-ledger
   assertions.

The autonomous solver, scripted solver, and reasoning fabric now constitute a
single, auditable hardware oracle aligned with μ-spec v2.0 and the Python VM.
