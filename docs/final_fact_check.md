# Repository Fact Check: "Plaque" Assertions vs. Current Evidence

## Scope and Methodology
- Installed the prescribed Coq toolchain and project dependencies, then inspected the repository artefacts that underpin the four "plaque" claims (Coq sandboxes, graph-colouring experiment, receipts bridge, and synthesis trap).
- Reviewed the formal developments (`ToyThieleMachine.v`, `VerifiedGraphSolver.v`, the generated `GeneratedProof.v`), the Python demo and translation scripts, JSON receipts, and Yosys logs.
- No additional modifications were made to the experimental data; the analysis relies on the artefacts committed to the repository.

## Headline Judgement

| Plaque Assertion | Repository Evidence | Verdict |
| --- | --- | --- |
| **Mathematical existence proofs (“Kitty Hawk” & “Cessna”)** | `ToyThieleMachine.v` and `VerifiedGraphSolver.v` define bespoke interpreters where Thiele-only instructions succeed and the paired classical interpreters fail; `shor_primitives/PeriodFinding.v` now proves the stated `shor_reduction` theorem, showing that an even period yields a non-trivial divisor via the Euclidean GCD.【F:coq/sandboxes/ToyThieleMachine.v†L6-L118】【F:coq/sandboxes/VerifiedGraphSolver.v†L9-L185】【F:coq/shor_primitives/PeriodFinding.v†L26-L47】 | **Supported within the sandboxes.** The separation is true for the hand-crafted instruction sets, but it does not extend to the archived universal proof. |
| **Empirical flight data** | `graph_demo_output/*/summary.json` record Act III runs with zero targeted checks after spending µ-bits on scripted oracle queries across all cascade graphs, and `shor_demo_output/analysis_report.json` logs the new three-act factorisation comparing blind trial division with µ-funded period discovery.【F:graph_demo_output/triadic_cascade/analysis_report.json†L1-L45】【F:graph_demo_output/scaling_summary.json†L1-L33】【F:shor_demo_output/analysis_report.json†L1-L39】 | **Supported as constant-factor collapses.** The receipts show the advertised trade-off, but the reasoning is host-side Z3 (or the bespoke period oracle), not an autonomous Thiele breakthrough. |
| **Formal bridge (“Ouroboros”)** | `scripts/prove_it_all.sh` regenerates the demo, `translate_receipts_to_coq.py` emits `GeneratedProof.v`, and Coq verifies that the receipts match the sandbox definition of `thiele_run`.【F:scripts/prove_it_all.sh†L1-L27】【F:scripts/translate_receipts_to_coq.py†L1-L187】【F:coq/sandboxes/GeneratedProof.v†L1-L62】 | **Supported for the triadic cascade only.** The bridge covers a single Act III run; it does not certify the general VM. |
| **Physical synthesis verdict** | Archived Yosys logs show the classical Verilog consumes 228 cells/267 wire bits while the Thiele residue latch needs five cells/106 wire bits.【F:hardware/synthesis_trap/classical_solver.log†L788-L805】【F:hardware/synthesis_trap/thiele_solver.log†L701-L733】 | **Supported as a pre-solved wrapper.** The resource gulf reflects reasoning done in software, not an on-silicon oracle. |

## What the Repository *Has* Proven

1. **Foundational microcosm ("paper airplane").** The toy eight-cell universe demonstrates a semantic separation: `ClaimLeftZero` reaches a state the classical write-one interpreter cannot, formalising a single non-Turing behaviour.【F:coq/sandboxes/ToyThieleMachine.v†L1-L94】
2. **Empirical receipts ("flight data").** For the nine-node cascade graph, the deterministic experiment records 3,786 blind assignments versus zero targeted checks after spending 23 µ-bits, and the Shor-on-Thiele demo shows two divisor checks versus zero targeted arithmetic once seven µ-bits buy the period witness—both quantify the advertised trade-off.【F:graph_demo_output/triadic_cascade/analysis_report.json†L1-L45】【F:shor_demo_output/analysis_report.json†L1-L39】
3. **Formal bridge ("Ouroboros").** `scripts/prove_it_all.sh` regenerates the Act III receipts and the generated file `python_receipt_sound` proves that the empirical run coincides with the sandbox solver, closing the loop between Python and Coq for this scenario.【F:scripts/prove_it_all.sh†L1-L27】【F:coq/sandboxes/GeneratedProof.v†L1-L55】
4. **Period reduction lemma.** `shor_primitives/PeriodFinding.v` now discharges `shor_reduction`, relying on the previously proven Euclidean lemmas to show that the period witness extracted in the demo indeed yields a divisor of \(N\).【F:coq/shor_primitives/PeriodFinding.v†L26-L47】
5. **Synthesis trap ("physical log").** Yosys reports 228 cells for the brute-force design versus five for the residue-mask latch, capturing the resource gulf between enumerating the search and latching the pre-reasoned answer.【F:hardware/synthesis_trap/classical_solver.log†L788-L805】【F:hardware/synthesis_trap/thiele_solver.log†L701-L733】

## Limitations that Keep the Thesis Incomplete

- **No universal containment proof.** The ambitious subsumption development remains archived with unresolved type mismatches; nothing in-tree derives the sandbox instructions from the historical `ThieleUniversal.v` semantics.【F:coq/verify_subsumption.sh†L1-L24】【F:archive/research/incomplete_subsumption_proof/README.md†L1-L40】
- **Oracle dependency.** Every empirical collapse depends on host-side reasoning (Z3 feasibility checks or precomputed residue masks). The repository does not exhibit a solver that reasons faster than it effectively reconstructs the original search space.【F:scripts/graph_coloring_demo.py†L39-L209】
- **Bridge scope.** `GeneratedProof.v` is regenerated for a single Act III trace. Extending the argument to other graphs or to the full VM state remains future work.【F:coq/sandboxes/GeneratedProof.v†L1-L120】

## Bottom Line

- **Demonstrated:** Carefully constructed Coq sandboxes, reproducible Python experiments, and archived synthesis logs jointly confirm that µ-bit accounting can replace brute-force search on specific graph families when reasoning is scripted in advance.
- **Not demonstrated:** An asymptotic separation, a hardware oracle that performs the reasoning, or a universal theorem that lifts the sandbox behaviour to the full Thiele Machine model.

The plaque’s rhetoric should therefore be read as a roadmap: the repository offers compelling microcosms and reproducible evidence, but it stops short of a complete, interlocking proof that Thiele Machines strictly surpass Turing Machines.
