# Independent Assessment of Repository Claims

## Methodology
- Installed the Coq toolchain and successfully type-checked the new sandboxes to confirm that the toy and "Cessna" artifacts compile without axioms (`coqc sandboxes/ToyThieleMachine.v`, `coqc sandboxes/VerifiedGraphSolver.v`).【cd6d7b†L1-L3】【79ec30†L1-L2】
- Parsed the published Yosys JSON netlists to recover the reported resource counts and attempted to replay the synthesis harness to verify tool availability.【2afd1d†L1-L15】【fdfb8b†L1-L6】
- Reviewed the graph-colouring experiment outputs and inspected the synthesis-trap staging area to check which evidence is actually present in the tree.【61e8a9†L1-L46】【da4017†L1-L2】
- Ran the maintained subsumption build to evaluate the status of the large-scale containment proof.【2f2c9f†L1-L110】

## Findings

### 1. Mathematical microcosms now exist
Both `ToyThieleMachine.v` and `VerifiedGraphSolver.v` provide mechanically checked examples where Thiele-style instructions achieve results that the paired classical interpreters cannot. The first establishes a minimal "ClaimLeftZero" instruction that reaches an otherwise unattainable target tape, while the second formalises the nine-node `triadic_cascade` instance with a classical backtracker (18 arithmetic branches) and a Thiele solver that spends 23 µ-bits to finish with zero residual search.【a04969†L1-L130】【2a964a†L1-L185】 These artifacts genuinely extend the repository beyond the original paper's promises by supplying concrete existence proofs inside Coq.

### 2. Empirical receipts now bridge into Coq
The new `scripts/translate_receipts_to_coq.py` utility converts Act III receipts into `coq/sandboxes/GeneratedProof.v`, allowing `scripts/prove_it_all.sh` to replay a fresh VM execution inside Coq after compiling `Sandbox.VerifiedGraphSolver`. This closes the earlier gap between the Python pipeline and the formal developments: the same witness recorded in JSON is now mechanically checked against the microcosm definitions.【F:scripts/translate_receipts_to_coq.py†L1-L187】【F:scripts/prove_it_all.sh†L1-L26】【F:coq/sandboxes/GeneratedProof.v†L1-L120】 Auditors can therefore treat the triadic cascade run as a single interlocking artifact spanning empirical and formal domains.

### 3. Empirical evidence shows constant-factor, not exponential, gains
The refreshed graph-colouring experiment still records 3,786 blind candidates for Act I, 18 heuristic branches for Act II, and zero brute-force checks for Act III after spending 23 µ-bits on oracle queries for the triadic cascade.【F:graph_demo_output/triadic_cascade/act_i/summary.json†L1-L20】【F:graph_demo_output/triadic_cascade/act_ii/summary.json†L1-L20】【F:graph_demo_output/triadic_cascade/act_iii/summary.json†L1-L20】 The new scaling suite extends this measurement to additional cascade graphs (5, 7, and 10 nodes), emitting `scaling_summary.json` and `scaling_plot.png` that show Act III holding at zero candidate checks while Act II grows with the instance size.【F:graph_demo_output/scaling_summary.json†L1-L33】【F:graph_demo_output/scaling_plot.png†L1-L1】 The evidence therefore supports consistent constant-factor collapses, not an asymptotic separation.

### 4. Core containment proof remains unverified
The historical subsumption development has been archived under `archive/research/incomplete_subsumption_proof/`, and `coq/verify_subsumption.sh` now reports the archival status instead of attempting to build it. The gap persists—the flagship containment argument is still incomplete—but the repository no longer presents the failing script as an active proof obligation.【F:coq/verify_subsumption.sh†L1-L40】【F:archive/research/incomplete_subsumption_proof/README.md†L1-L60】

### 5. Synthesis trap evidence is now reproducible or inspectable
The repository carries Verilog sources, JSON netlists, and the captured Yosys logs for the classical and Thiele solvers (228 cells vs. 5 cells; 267 vs. 106 wire bits).【F:hardware/synthesis_trap/classical_solver.log†L1-L40】【F:hardware/synthesis_trap/thiele_solver.log†L1-L40】 `scripts/run_the_synthesis.sh` now checks for `yosys` at startup: if the tool is present, it rebuilds the designs; otherwise, it streams the archived logs, ensuring the oracle's verdict is visible even without re-running synthesis.【F:scripts/run_the_synthesis.sh†L1-L120】

## Conclusion
The repository has undeniably advanced beyond the original paper by supplying mechanically checked microcosms and a richer empirical demo, but several statements in the recent assessment overreach. The large-scale subsumption proof remains broken, the certificate story does not yet cover the real VM receipts, the empirical evidence addresses only a fixed small graph, and the synthesis trap requires additional setup before it can act as an independent witness. Auditors should treat the new artifacts as promising progress rather than definitive proof of the broader thesis.
