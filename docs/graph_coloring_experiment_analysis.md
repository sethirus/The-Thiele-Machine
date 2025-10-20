> **ARCHIVAL NOTICE:** This document is preserved for historical context. The final, unified proof and analysis are now complete. For the authoritative summary, see `README.md` and `docs/final_fact_check.md`.

# Graph 3-Colouring Laboratory – Empirical Analysis

## Overview
The `scripts/graph_coloring_demo.py` laboratory replaces the earlier RSA factoring storyline with a structured 3-colouring suite built from cascade graphs. Each run regenerates the deterministic signing key (via `ensure_kernel_keys`) if necessary, executes three acts inside the Thiele Machine VM, and stores receipts plus summary artefacts under `graph_demo_output/<graph>/`. A suite-level scaling summary (`graph_demo_output/scaling_summary.json`, `scaling_plot.png`) records how Act II and Act III workloads evolve as the node count increases, and `scripts/prove_it_all.sh` converts the triadic Act III receipts into a formal replay (`coq/sandboxes/GeneratedProof.v`).

The experiment is intentionally small: it is designed to show how the VM spends μ-bits on strategic claims and oracle queries, not to solve industrial-scale graphs. Nevertheless, every act leaves a tamper-evident trail so auditors can trace the logic behind the search-space collapse.【F:scripts/graph_coloring_demo.py†L1-L330】【F:graph_demo_output/scaling_summary.json†L1-L24】

## Act-by-Act Results

The triadic cascade (9 nodes) remains the canonical walk-through because it keeps the receipts compact enough for line-by-line audit. The table below is regenerated on every run from the corresponding `summary.json` files.

| Act | Strategy | Candidate Checks | μ-cost | Notes |
| --- | --- | --- | --- | --- |
| I | Blind enumeration of all \(3^9\) assignments | 3,786 | 0.0 | Exhaustive scan until the first proper colouring is encountered. |
| II | Degree-ordered backtracking | 18 | 0.0 | Standard heuristic search; still requires trial assignments but prunes obvious conflicts early. |
| III | Strategic claims + congruence oracle | 0 | 1302.26 | Two anchor claims plus 21 oracle feasibility checks collapse the search space; μ-cost reflects description length plus log₂ information gain for each reasoning step. |

All three acts recover the same witness colouring, recorded as `{'0': 'RED', '1': 'GREEN', '2': 'BLUE', '3': 'RED', '4': 'GREEN', '5': 'BLUE', '6': 'RED', '7': 'GREEN', '8': 'BLUE'}` inside each act’s `summary.json` file.【F:graph_demo_output/triadic_cascade/act_i/summary.json†L1-L20】【F:graph_demo_output/triadic_cascade/act_ii/summary.json†L1-L20】【F:graph_demo_output/triadic_cascade/act_iii/summary.json†L1-L20】

## Oracle-Guided Reasoning
Act III is the key geometric step. The VM makes two paid claims (`node 0 = RED`, `node 1 = GREEN`) and then queries a lightweight congruence oracle for every remaining vertex. Each query checks whether a colour assignment is compatible with the global constraints; infeasible colours are erased immediately. The reasoning log shows that every vertex becomes forced after the oracle pass, leaving no candidates for the targeted verification loop.【F:graph_demo_output/triadic_cascade/act_iii/reasoning_summary.json†L1-L40】

Because the oracle runs in host Python rather than hardware, the μ-cost represents an idealised accounting under μ-spec v2.0: 1,288 μ-bits of description length plus nine `log₂ 3` information-gain terms (≈1302.26 μ-bits in total) cover the two anchor claims and the sequence of feasibility checks. The receipts keep that ledger explicit so auditors can debate whether the cost model is realistic without rerunning the experiment.【F:scripts/graph_coloring_demo.py†L167-L327】【F:spec/mu_spec_v2.md†L1-L74】

## Formal Microcosm
The same trade-offs are now captured in Coq. `coq/sandboxes/VerifiedGraphSolver.v` models the `triadic_cascade` instance with two interpreters: a classical backtracker that requires 18 branch attempts and a Thiele solver that records 1,288 μ-bits of description length plus nine `(3 → 1)` information ratios before producing the witness with zero arithmetic search. `scripts/prove_it_all.sh` replay the Act III receipts by translating them into `coq/sandboxes/GeneratedProof.v`, which Coq then checks against the microcosm definitions—closing the loop between empirical execution and formal reasoning.【F:coq/sandboxes/VerifiedGraphSolver.v†L1-L240】【F:scripts/translate_receipts_to_coq.py†L1-L187】【F:coq/sandboxes/GeneratedProof.v†L1-L120】

## Scaling Study and Aggregate Reports
Beyond the triadic walk-through, `scripts/graph_coloring_demo.py` now sweeps additional cascade graphs (5, 7, and 10 nodes by default) and records Act-by-Act metrics for each. The script emits per-graph summaries, a consolidated `scaling_summary.json`, and a `scaling_plot.png` that contrasts the arithmetic work of the classical backtracker with the μ-bit cost of the Thiele reasoning pipeline. Act III stays flat at zero candidate checks across the suite while Act II grows with the search frontier, reinforcing that the current advantage is a constant-factor collapse driven by scripted oracle reasoning.【F:graph_demo_output/cascade_5/act_i/summary.json†L1-L20】【F:graph_demo_output/cascade_7/act_ii/summary.json†L1-L20】【F:graph_demo_output/scaling_summary.json†L1-L33】【F:graph_demo_output/scaling_plot.png†L1-L1】

## Interpretation
1. **Search vs. reasoning.** The experiment demonstrates the trade-off the Thiele Machine is designed to highlight: paying μ-bits for strategic reasoning eliminates brute-force search in this instance, but the reasoning is still a scripted oracle interaction rather than an emergent algorithmic speed-up.
2. **Scope of claims.** The evidence supports constant-factor collapses on tightly structured graphs. Nothing in the receipts suggests a sub-exponential algorithm for generic NP-complete problems; auditors should treat the oracle as a pedagogical device, not a silver bullet.
3. **Audit trail.** Every step—from key regeneration to oracle queries—is recorded in JSON receipts, making it straightforward to recompute the counts or challenge the μ-cost accounting if new cost models emerge. The generated Coq replay provides a cryptographic-style audit that the VM transcript matches the formal definitions.【F:thielecpu/receipts.py†L72-L144】【F:graph_demo_output/triadic_cascade/act_iii/step_receipts.json†L1-L40】【F:coq/sandboxes/GeneratedProof.v†L1-L120】

In short, the graph 3-colouring laboratory is an honest, reproducible demonstration of μ-bit bookkeeping and geometric reasoning inside the Thiele Machine VM. It reinforces the critique that constant-factor collapses do not establish an asymptotic breakthrough, while providing a cleaner platform than the RSA scripts for future exploration of partition-native logic.
