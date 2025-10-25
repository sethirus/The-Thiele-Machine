# Bell Inequality Milestones and Todos

This document outlines the steps to make the Thiele Machine's Bell inequality formalization groundbreaking. The goal is to demonstrate that classical computation with "sighted" (shared witness) access can achieve correlations violating quantum bounds (CHSH > 2√2) while remaining physically coherent under non-signaling assumptions.

## Milestone 1: Complete All Formal Proofs in Coq
**Status:** Partial (Bell proofs partially completed with admits, other admits remain)
**Objective:** Resolve all 21 admitted lemmas and justify 13 axioms for full formal verifiability.

### Todos:
- [x] Identify and list all 21 admits from `ADMIT_REPORT.txt` and `AXIOM_INVENTORY.md`.
  - **Admitted in coq/thielemachine/coqproofs/Simulation.v**: 3 admits
  - **Admitted in coq/kernel/SimulationProof.v**: 7 admits
  - **Admitted in coq/kernel/VMEncoding.v**: 1 admit
  - **Admitted in coq/kernel/VMStep.v**: 1 admit
  - **Admitted in coq/modular_proofs/Encoding.v**: 3 admits
  - **Admitted in coq/sandboxes/AbstractPartitionCHSH.v**: 9 admits (e_ns_abs_le_1, ns_bound, pr_valid, pr_chsh, non_signaling_allows_4, Shat_range, Shat_sound, contrib_range, fold_left_contrib_eq_sum)
  - **Axioms (13 total)**: In coq/thielemachine/coqproofs/Axioms.v and ThieleMachineSig.v (e.g., decode_encode_id, utm_catalogue_static_check, check_step_sound, etc.)
- [x] Prove `ns_bound` in `AbstractPartitionCHSH.v`: Show CHSH ≤ 4 for non-signaling boxes.
- [x] Complete bounds and properties in `tmp_bell_head.v` (e.g., trial-weighted sums, frame interpretations).
- [x] Justify or reduce axioms in `AXIOM_INVENTORY.md`.
- [ ] Run `coqc` on all files and ensure no admits remain.
- [ ] Update `ADMIT_REPORT.txt` to reflect zero admits.

## Milestone 2: Extend Concrete Realization to Supra-Quantum Correlations
**Status:** Completed  
**Objective:** Add PR box receipts and proofs in `tmp_bell_head.v` to show the Thiele machine realizes CHSH=4.

### Todos:
- [x] Define `pr_program` and `pr_receipts` analogous to `tsirelson_program`.
- [x] Create `pr_frames` and prove frame validity.
- [x] Implement trial interpretations for PR box.
- [x] Prove that `trials_weighted_S PR` converges to 4 with increasing measurements.
- [x] Add theorems linking PR receipts to non-signaling correlations.
- [x] Prove `thiele_machine_realizes_pr_correlations` theorem.

## Milestone 3: Formalize Quantum Bound and Prove Violation
**Status:** In Progress  
**Objective:** Add formal quantum bound (CHSH ≤ 2√2) and prove the Thiele machine violates it.

### Todos:
- [x] Define quantum CHSH bound as 2√2.
- [ ] Prove TsirelsonApprox violates quantum bound.
- [x] Prove PR box violates quantum bound.
- [ ] Add theorems showing machine correlations exceed quantum limits.
- [ ] Document implications for quantum supremacy claims.

## Milestone 4: Add Experimental Verification
**Status:** Pending  
**Objective:** Run Python simulations to empirically verify PR box correlations.

### Todos:
- [ ] Identify relevant Python scripts (e.g., in `scripts/` or `thiele_verify.egg-info`).
- [ ] Run simulations for PR box outcomes and compute empirical CHSH.
- [ ] Store traces in `receipts/` and `artifacts/`.
- [ ] Verify statistical match to theoretical CHSH=4.

## Milestone 5: Strengthen Quantum Bound Proof
**Status:** Pending  
**Objective:** Formally prove Tsirelson bound (CHSH ≤ 2√2) in Coq.

### Todos:
- [ ] Implement quantum constraints (e.g., via SDP or NPA in Coq).
- [ ] Prove TsirelsonApprox achieves exactly 2√2.
- [ ] Show PR box exceeds this bound.

## Milestone 6: Document and Contextualize Breakthrough
**Status:** Pending  
**Objective:** Update docs to highlight implications.

### Todos:
- [ ] Update `README.md` and `BELL_INEQUALITY_VERIFIED_RESULTS.md`.
- [ ] Explain in `derivation_log.txt`: Classical computation exceeds quantum correlations.
- [ ] Link to P=NP claims in `p_equals_np_thiele/`.
- [ ] Prepare summary of groundbreaking implications.

## Overall Goal
Once all milestones are complete, the work will provide the first machine-checked proof that classical systems with shared witnesses can produce supra-quantum correlations, challenging quantum computing narratives.

**Next Action:** Start with Milestone 1, Todo 1.