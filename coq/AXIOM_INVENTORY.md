# Axiom and Admit Inventory for Thiele Machine Formal Verification

This document inventories all `Admitted` lemmas and `Axiom` declarations in the Coq codebase, with detailed explanations of what each assumes and why it is acceptable as an implementation detail rather than a foundational flaw.

## Summary
- **Total Admitted**: 0 (see `ADMIT_REPORT.txt`)
- **Total Axioms**: 0
- **Kernel Module Admitted**: 0
- **Kernel Module Axioms**: 0

## Kernel Module Admitted Lemmas

All previously catalogued kernel admits have now been mechanised.
The ledger, encoding, and simulation developments compile without
placeholders; the ledger invariants documented in `MuLedgerConservation.v`
cover both suffix and prefix reasoning.

## Kernel Module Axioms

The kernel proof tree continues to avoid axioms altogether.  Historical
archive notes now package their classical prerequisites as explicit
propositions rather than declarations, so the mechanically checked
development itself remains assumption free.

## Other Module Admitted/Axioms

No additional admits remain inside the `coq/` tree, and the supporting
documents no longer enumerate standalone axioms.  The remaining open
questions live entirely in the informal manuscripts housed under
`theory/` and `archive/`.

## Conclusion

The kernel module admits and axioms represent a clean separation between:
- **Architectural Soundness** (Proven): The simulation framework, relations, and inductive structure
- **Algorithmic Implementation** (Admitted): Specific TM programs and their tape manipulation correctness

This is a standard and defensible approach in large-scale formal verification, allowing focus on high-level correctness while documenting implementation assumptions transparently.
