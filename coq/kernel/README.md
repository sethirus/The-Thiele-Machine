# Kernel

The abstract model of the Thiele Machine, its results, and the files that tie
the small machine and the universal machine U to them.

The `Kernel` namespace spans the topical subdirectories via
`-R kernel/<subdir> Kernel` mappings in [`_CoqProject`](../_CoqProject), so
imports like `From Kernel Require Import UniversalCertificationCost` resolve
from any subdirectory.

## Subdirectory map

| Directory | Role |
|---|---|
| [`foundation/`](foundation/) | Substrates, record-carrying machines, the record axis over any base, growing and probabilistic records, cross-base granularity, recursion and undecidability, and the links from the small machine and U into these records |
| [`nfi/`](nfi/) | No Free Insight for any substrate, permanent certificates on finite machines, pricing, entropy and heat, shadow pricing, narrowing, cost frameworks |
| [`frontier/`](frontier/) | Observation policy and the window theorem, the pointer-observable criterion, the record-proliferation survey, the ecosystem game |
| [`quantum/`](quantum/) | CHSH, Tsirelson from algebra, NPA moment matrices, the integer column check, the elliptope |
| [`category/`](category/) | The algebraic Tsirelson bound from polynomial minors |
| [`reductions/`](reductions/) | Narrow models of external systems: Certificate Transparency, proof-carrying code, TPM quotes, Casper FFG, gas metering, RAM record machines |
| [`thermodynamic/`](thermodynamic/) | The two-state calorimeter protocol |

Each subdirectory has its own `README.md` describing its files.

## Dependency order

```
foundation/ (Substrate, StructuralCore, record axis)
     |
     +--> nfi/ (UniversalCertificationCost, PermanentCertification, ...)
     |        |
     |        +--> frontier/, reductions/, thermodynamic/
     |
     +--> links: EarnedCoreLinks, EarnedGenericLinks, UniversalThieleLinks,
                 UniversalInterpreterLinks (minimal/ and U into the records)

quantum/ and category/ stand on the Coq standard library and each other.
```

## Verification status

The active files build with no `Admitted.` declaration and no project-local
axiom. Named premises (`landauer_heat`, cost calibrations, cryptographic
assumptions in the external-system models) are hypotheses of the theorems that
use them, not axioms.

The assumption receipt lists every axiom behind every theorem. The only axioms
it may contain are standard-library axioms:
`FunctionalExtensionality.functional_extensionality_dep`,
`ClassicalDedekindReals.sig_forall_dec`,
`ClassicalDedekindReals.sig_not_dec`, and `Classical_Prop.classic`
(`coq/INQUISITOR_ASSUMPTIONS.json` keeps that allow list).

Reproduce with `make coq-gate` from the repo root (see [`coq/README.md`](../README.md)).

## Load-bearing exports

The top-level README's [Formal Spine](../../README.md#formal-spine) and
[Scope](../../README.md#scope) tables point into specific
files inside this tree. The source files, their imports, and the generated
dependency and assumption receipts are the authoritative record of the proof
surface. Files that are not part of the active `_CoqProject` are not included
in the kernel build.
