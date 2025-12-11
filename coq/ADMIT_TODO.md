# Admit/TODO Audit

This file summarizes admitted proofs/axioms remaining after the recent cleanup and suggested next steps.

High severity (block formal verification):
- `thielemachine/verification/FullIsomorphism.v`
  - Several main statements remain admitted; complete proofs here are required for the formal isomorphism claim.
  - Next step: audit used lemmas and reduce dependencies on core Bridge lemmas; attempt to prove theorem by induction on `n`, using `inv_full_preservation_n`.

- `thielemachine/verification/BridgeDefinitions.v`
  - `inv_full_preservation` (critical): admit removed from setup_state, but preservation across `run1` remains admitted.
  - `inv_full_preservation_n` (multi-step preservation) depends on the above.
  - Next step: Prove `inv_full_preservation` by case analysis on CPU instructions. Use `step_fast` tactics and the small step lemmas already present. Establish per-instruction invariants as lemmas.

Medium severity:
- `thielemachine/coqproofs/SpacelandCore.v` and `SpacelandComplete.v` admit proofs. These are important domain lemmas for the Spaceland formalization.
  - Next step: refactor or decompose into smaller lemmas to make proof steps tractable; add intermediate invariants where possible.

Low severity
- Miscellaneous admits in non-core/extraction files and docs; doc edits or separate test-only modules can be handled later.

General Steps to Remove Admits:
1. Replace global admits with small, targeted lemmas. Try to reduce the scope of each admission.
2. For the bridge lemmas, follow incremental proofs: prove preserved invariants for single instruction patterns, then generalize using `run_n` rewrites.
3. Pin Coq version and clean `*.vo` build artifacts before each run.
4. Add CI build step and test harness to exercise each small lemma independently.

If you'd like, I'll:
- Attempt per-instruction proofs for `inv_full_preservation` (Start with `PC=0` / `Fetch` and `PC=1` `AddReg` cases), or
- Create an iterative list of lemmas to be written and pick one to prove now.

Which should I prioritize?