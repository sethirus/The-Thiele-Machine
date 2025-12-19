# PREREG_B: Jacobson mechanization + µ-entropy correction (scaffold)

Date (UTC): 2025-12-18

Goal
- Mechanize a baseline Jacobson-style derivation (local horizon thermodynamics ⇒ GR).
- Then modify the entropy functional S = S_area + S_µ and derive an explicit correction Δ(µ).

This is a prereg scaffold. The actual mechanized proof and entropy functional must be supplied.

## Locked inputs

- Entropy functional S_µ must be defined as a concrete formula in a single file.
- Proof must be checkable (no Admitted/admit/Axiom).

## Locked falsifiers

PASS requires:
- Baseline mechanization recovers GR.
- Modified derivation recovers GR exactly in the µ→0 limit.
- The correction family is explicit and uniquely determined by the stated assumptions.

FAIL if:
- The proof uses Admitted/admit/Axiom.
- The correction is underconstrained (“anything goes”) or collapses to renaming.

## Deliverables (required for completion)

- PROOF_B/ (mechanized baseline + modified proof)
- DELTA_FIELD_EQS.pdf (human-readable derivation of Δ)
- CONSTRAINTS_B.md (mapping Δ parameters to published experimental bounds)
