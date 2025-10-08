# Proof of Work – Thiele Machine Subsumption

This document records the flagship claim delivered by the repository and the
artefacts that certify it.

## Statement

**Theorem (Subsumption).** Classical computation is strictly contained in
Thiele computation: `turing ⊂ thiele`.

The proof decomposes into two mechanised pillars:

1. **Containment (`coq/thielemachine/coqproofs/Simulation.v`):** a blind Thiele
   program simulates every Turing Machine.  The universal interpreter is fully
   mechanised in `coq/thieleuniversal/coqproofs/` and exports encode/decode
   witnesses together with a step-count lemma.  `Simulation.v` packages these
   pieces into `turing_contained_in_thiele`.
2. **Strictness (`coq/thielemachine/coqproofs/Separation.v`):** a sighted
   Thiele solver resolves Tseitin expander contradictions in cubic time while a
   Turing/DPLL search is axiomatically lower-bounded by `2^n` steps.  The proof
   provides constructive bounds on both runtime and μ-bit expenditure and uses a
   single, explicitly declared complexity-theoretic axiom
   (`turing_tseitin_is_exponential`).

`coq/thielemachine/coqproofs/Subsumption.v` imports both results and publishes
`thiele_formally_subsumes_turing`, the capstone theorem.

## Verification workflow

Run the canonical script to rebuild the proof from a clean checkout:

```bash
cd coq
./verify_subsumption.sh
```

The script checks for the Coq toolchain, cleans the build tree, and then
recompiles the two pillars (`Simulation.v` and `Separation.v`).  Both must
finish successfully to certify the subsumption theorem.

## Empirical corroboration

Execute the Python challenge to witness the blind-vs-sighted separation on the
canonical Tseitin instances:

```bash
python scripts/challenge.py verify receipts
```

The command verifies the signed receipts, recomputes step hashes, replays the
solver witnesses, and reports the measured μ-bit and time costs for the blind
and sighted approaches.  The data aligns with the formal bounds established in
`Separation.v`.

## Assumptions

The Coq development is entirely mechanised; the remaining foundational
assumptions are enumerated in [`coq/AXIOM_INVENTORY.md`](coq/AXIOM_INVENTORY.md).
In particular, the subsumption theorem depends only on the standard complexity
assumption that blind search on Tseitin expanders is exponential.
