# No-Free-Insight cone (`coq/nofi/`)

This directory implements an **axiom-free abstraction pattern**:

- Put **assumptions** in a `Module Type` signature.
- Prove the theorem in a **functor** over that signature.
- Provide a concrete **kernel instance** that discharges the obligations using existing kernel lemmas.

This keeps the theorem *general* (“any system satisfying the interface”) while keeping the Coq development **0 Axiom / 0 Admitted**.

## Files

- [NoFreeInsight_Interface.v](NoFreeInsight_Interface.v)
  - Defines the `NO_FREE_INSIGHT_SYSTEM` contract.
  - No axioms; only interface fields.

- [NoFreeInsight_Theorem.v](NoFreeInsight_Theorem.v)
  - Proves the theorem as a functor `NoFreeInsight(X)`.

- [Instance_Kernel.v](Instance_Kernel.v)
  - Instantiates the interface with the kernel VM:
    - `S := VMState`
    - `Trace := list vm_instruction`
    - `run := RevelationProof.trace_run (S (length trace))`
    - `certifies := has_supra_cert` (non-zero cert address)
    - `structure_event := uses_revelation ∨ EMIT ∨ LJOIN ∨ LASSERT`

## Flagship theorem

The functor theorem is:

> `NoFreeInsight(X).no_free_insight`

And the kernel witness is obtained by instantiating `X := KernelNoFI`.

## Audit gate

Use `scripts/audit_nofi_cone.sh` to:

- run the inquisitor scanner restricted to `coq/nofi/`
- run `Print Assumptions` on the flagship theorem and fail if it pulls in any axioms
