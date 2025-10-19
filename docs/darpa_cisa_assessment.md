# DARPA/CISA Forensic Assessment – October 2025 Refresh

## Executive Summary
- **Mechanical containment is now explicit.** The new kernel Coq development defines a shared tape/head substrate, gives the Turing interpreter no semantics for `H_ClaimTapeIsZero`, and equips the Thiele interpreter with a single additional transition that zeroes the tape while incrementing `mu_cost`. Theorems `thiele_simulates_turing` and `turing_is_strictly_contained` prove that the Thiele kernel reproduces every classical execution and reaches a state the Turing kernel cannot.【F:coq/kernel/Kernel.v†L4-L66】【F:coq/kernel/KernelTM.v†L12-L37】【F:coq/kernel/KernelThiele.v†L7-L26】【F:coq/kernel/Subsumption.v†L36-L118】
- **μ-bit accounting is information-theoretic bookkeeping.** μ-spec v2.0 defines costs as S-expression length plus Shannon information gain, and all tooling (VM, demos, receipts) delegates to this shared calculator.【F:spec/mu_spec_v2.md†L1-L74】【F:thielecpu/mu.py†L1-L92】 The numbers reflect question phrasing and oracle entropy reduction rather than measured hardware work.
- **Empirical laboratory remains oracle-driven.** Re-running the triadic cascade suite records 3,786 blind checks in Act I, 18 heuristic branches in Act II, and zero targeted checks in Act III after paying ≈1302.26 μ-bits for scripted anchor claims and 21 congruence queries.【72fc6c†L1-L16】【F:graph_demo_output/triadic_cascade/analysis_report.json†L1-L45】【F:graph_demo_output/triadic_cascade/act_iii/reasoning_summary.json†L1-L88】 The reasoning logic continues to live in host Python/Z3.
- **Hardware artefacts document a bespoke reasoning lattice.** `reasoning_core.v` performs combinational propagation for the triadic cascade, and Yosys reports 228 cells for the classical brute force design versus 866 cells (517 in the core) for the Thiele solver.【F:hardware/synthesis_trap/reasoning_core.v†L1-L162】【F:hardware/synthesis_trap/thiele_graph_solver.v†L1-L180】【4ef6aa†L1-L32】【b2490c†L1-L52】 This demonstrates a physical embodiment of the scripted reasoning, not a general oracle.
- **Security posture is unchanged.** The repository still ships deterministic signing keys and high-fidelity transcripts. Responsible distribution requires treating the artefacts as sensitive research data and rotating keys before any operational deployment.【F:thielecpu/receipts.py†L72-L144】【F:SECURITY.md†L1-L3】

## Methodology
1. Installed Coq and project dependencies (`apt-get install -y coq`, `pip install -e .`).
2. Compiled the kernel modules with `coqc -Q kernel Kernel kernel/*.v` to confirm the subsumption theorems have no admits.【fbb5c4†L1-L1】【ff49c2†L1-L1】【c76533†L1-L1】【fb377a†L1-L1】
3. Executed `python scripts/graph_coloring_demo.py --no-plot --graphs triadic_cascade` and `bash scripts/run_the_synthesis.sh` to regenerate receipts and Yosys reports.【72fc6c†L1-L16】【ce4b70†L1-L200】
4. Reviewed all documentation artefacts and updated their status narratives to match the current evidence base.

## Findings
### Software Stack
- **VM and receipts.** The Thiele CPU tracks μ-information in software registers and issues signed receipts using the deterministic Ed25519 key. The sandbox restricts `PYEXEC` payloads to a curated AST vocabulary.【F:thielecpu/state.py†L31-L121】【F:thielecpu/vm.py†L31-L200】【F:thielecpu/receipts.py†L72-L211】 Key regeneration remains deterministic for audit reproducibility.
- **μ-ledger implementation.** `thielecpu/mu.py` exposes question/answer cost helpers that all experiments use. Changing the text of a claim or the assumed possibility counts directly alters the μ-total, underscoring that the measurement is a modelling choice rather than a physical observation.【F:thielecpu/mu.py†L1-L92】【F:scripts/calculate_mu_cost.py†L1-L78】

### Empirical Experiments
- **Graph-colouring lab.** Act III removes search by querying a Python oracle that eliminates colours inconsistent with the anchors. The μ-ledger reports two strategic claims plus nine `(3→1)` collapses for the remaining nodes. No hardware reasoning is exercised during the run.【F:scripts/graph_coloring_demo.py†L167-L327】【F:graph_demo_output/triadic_cascade/act_iii/reasoning_summary.json†L1-L88】
- **Bridging to Coq.** `scripts/prove_it_all.sh` translates the Act III transcript into `coq/sandboxes/GeneratedProof.v`, which Coq verifies against the sandbox solver. The bridge currently covers this single instance.【F:scripts/prove_it_all.sh†L1-L24】【F:coq/sandboxes/GeneratedProof.v†L1-L66】

### Hardware Artefacts
- **Classical baseline.** `classical_period_finder.v` implements sequential modular exponentiation search; synthesis yields 228 cells and 267 wire bits.【F:hardware/resonator/classical_period_finder.v†L1-L160】【4ef6aa†L1-L32】
- **Thiele solver.** `thiele_graph_solver.v` orchestrates the combinational `reasoning_core` and accumulates its reported activity into `mu_cost`. The design is materially larger (866 cells, 1,237 wire bits) because it encodes the propagation lattice in space.【F:hardware/synthesis_trap/thiele_graph_solver.v†L1-L180】【b2490c†L1-L52】 The µ-ledger is derived from eliminated colours, not dynamic power data.

### Formal Developments
- **Kernel subsumption.** The new kernel is self-contained and axiom-free. Its separation result relies on granting an extra primitive that the Turing interpreter lacks; no attempt is made to derive this kernel from the historic `ThieleMachine` definitions.【F:coq/kernel/Subsumption.v†L36-L118】
- **Archived universality.** The ambitious universal proof remains archived with unmet obligations; auditors should treat it as historical context only.【F:archive/research/incomplete_subsumption_proof/README.md†L1-L36】

## Risk Assessment
- **Key exposure and transcript sensitivity.** Shipping `kernel_secret.key` enables deterministic verification but allows forged receipts. Rotate or withhold the private key for any release beyond research collaborators.【F:scripts/generate_kernel_keys.py†L16-L86】
- **Oracle dependence.** Because all reasoning steps call host solvers, any claim of computational advantage collapses if the oracle underperforms or is removed. Operational deployments would need native reasoning hardware or a robust oracle trust model.
- **Interpretation risk.** Documentation now clarifies that μ is a bookkeeping metric, yet downstream readers may still misinterpret the numbers as evidence of physical speedups. Continuous education and clear labelling are essential.

## Recommendations
1. **Maintain the documentation/artefact alignment.** Keep `docs/kernel_analysis.md`, `docs/final_fact_check.md`, and this assessment in sync whenever proofs or experiments change.
2. **Plan for key rotation.** Publish a roadmap for retiring the deterministic signing key once audits conclude.
3. **Broaden bridge coverage cautiously.** Extending the Coq bridge to other receipts will improve confidence but should not be framed as universal proof until oracle independence is demonstrated.
4. **Explicitly mark archival materials.** Retain historical manifests but label them as non-authoritative in every index to prevent confusion with the kernel results.

## Conclusion
The repository now offers a coherent trio of artefacts: a minimalist Coq kernel that mechanically subsumes the classical interpreter via a new claim instruction, reproducible oracle-guided experiments whose μ-costs are computed from an explicit information model, and hardware netlists that embed the same reasoning pattern in gates. These deliver honest, verifiable insights into how the Thiele narrative operates today. They do **not** yet demonstrate an emergent physical resource beyond time and space; all purported advantages derive from scripted instruction-level extensions and oracle interactions. Future work must either eliminate the oracle or explain how to realise it physically before stronger claims can be entertained.
