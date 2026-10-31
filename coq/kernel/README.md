# Kernel

The abstract model of the Thiele Machine and its results.

The `Kernel` namespace spans the topical subdirectories via
`-R kernel/<subdir> Kernel` mappings in [`_CoqProject`](../_CoqProject), so
imports like `From Kernel Require Import UniversalCertificationCost` resolve
from any subdirectory.

## Subdirectory map

| Directory | Role |
|---|---|
| [`foundation/`](foundation/) | The definition over any order (`AxCore.v`) and the member predicate (`AxThiele.v`), substrates, record-carrying machines, the record axis over any base, growing and probabilistic records, cross-base granularity, recursion and undecidability |
| [`nfi/`](nfi/) | No Free Insight for any substrate, permanent certificates on finite machines, pricing, entropy and heat, shadow pricing, narrowing, cost frameworks |
| [`frontier/`](frontier/) | Observation policy and the window theorem, the pointer-observable criterion, the record-proliferation survey, the ecosystem game |
| [`reductions/`](reductions/) | Narrow models of external systems: Certificate Transparency, proof-carrying code, TPM quotes, Casper FFG, gas metering, RAM record machines |
| [`thermodynamic/`](thermodynamic/) | The two-state calorimeter protocol |

Each subdirectory has its own `README.md` describing its files.

## Dependency order

```
foundation/AxThiele (the member predicate) and AxCore (the priced record systems)
     |
     +--> nfi/UniversalCertificationCost (the two-point instance, the toll alone)
     |
foundation/ (Substrate, StructuralCore, record axis)
     |
     +--> nfi/ (UniversalCertificationCost, PermanentCertification, ...)
              |
              +--> frontier/, reductions/, thermodynamic/
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

The top-level README's [Where things live](../../README.md#where-things-live)
list points into specific
files inside this tree. The source files, their imports, and the generated
dependency and assumption receipts are the authoritative record of the proof
surface. Files that are not part of the active `_CoqProject` are not included
in the kernel build.
