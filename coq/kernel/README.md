# Kernel

Core structural-constraint proofs, optimization bounds, and bisimulation
results for the kernel, the 51-instruction Thiele machine. **327 files, zero admits.**

The `Kernel` namespace spans the topical subdirectories via
multi-line
`-R kernel/<subdir> Kernel` mappings in [`_CoqProject`](../_CoqProject), so
imports like `From Kernel Require Import VMState` resolve from any subdirectory.

## Subdirectory map

| Directory | Files | Role |
|---|---:|---|
| [`foundation/`](foundation/) | 106 | VM model, simulation, classical/Turing fragment |
| [`mu_calculus/`](mu_calculus/) | 12 | μ initiality, cost derivation, Shannon bridges, hierarchy |
| [`nfi/`](nfi/) | 53 | No Free Insight chain: A2 substrate-independence, structural advantage |
| [`frontier/`](frontier/) | 23 | Landauer bridges, NPA minors against cost axioms, cross-link inequalities, reachable geometry, pointer observables |
| [`category/`](category/) | 5 | Categorical bridge laws and algebraic Tsirelson |
| [`quantum/`](quantum/) | 38 | CHSH, Tsirelson, NPA-PSD, Born rule, no-cloning, unitarity |
| [`curvature/`](curvature/) | 30 | Einstein, Riemann, simplicial geometry, μ-gravity, Lorentzian |
| [`thermodynamic/`](thermodynamic/) | 12 | Bekenstein, Clausius, finite-information |
| [`witness/`](witness/) | 9 | Shadow projection, blindness, witness preservation |
| [`hardware_bridge/`](hardware_bridge/) | 5 | Three-layer observable contracts, RTL correspondence, Python/OCaml agreement |
| [`aggregators/`](aggregators/) | 9 | TOE, ThieleGenesis, MasterSummary, audits |
| [`reductions/`](reductions/) | 22 | Reduction and undecidability constructions |
| [`misc/`](misc/) | 3 | Cone algebra/derivation, semantic μ-cost |

Each subdirectory has its own `README.md` describing its files, dependencies,
and load-bearing exports.

## Dependency order (typical build path)

```
foundation/ → mu_calculus/ → nfi/ → witness/
                ↓                    ↓
             quantum/         frontier/ (cross-link composites)
                ↓                    ↓
            category/         hardware_bridge/
                ↓                    ↓
          thermodynamic/      aggregators/
                ↓
            curvature/
```

## Verification status

All 327 files build with **zero `Admitted.` declarations** and **zero
project-local axioms**. Two named bridge premises are Prop-valued definitions
that theorems take as hypotheses, not axioms:

- `mu_landauer_unruh_calibrated` (a `Definition ... : Prop` in [`curvature/NoFIToEinstein.v`](curvature/NoFIToEinstein.v))
- `bsc_kami_compilation_trusted` (a `Definition ... : Prop` in [`hardware_bridge/VerilogRTLCorrespondence.v`](hardware_bridge/VerilogRTLCorrespondence.v); BSC compiler trust)

The only axioms in the assumption receipt are five standard-library axioms:
`FunctionalExtensionality.functional_extensionality_dep`,
`Eqdep.Eq_rect_eq.eq_rect_eq`, `ClassicalDedekindReals.sig_forall_dec`,
`ClassicalDedekindReals.sig_not_dec`, and `Classical_Prop.classic`.

Reproduce with `make coq-gate` from the repo root (see [`coq/README.md`](../README.md)), then
`Print Assumptions ReceiptTheorem.` to inspect the closure.

## Load-bearing exports

The top-level README's [Formal Spine](../../README.md#formal-spine) and
[Scope](../../README.md#scope) tables point into specific
files inside this tree. The source files, their imports, and the generated
dependency and assumption receipts are the authoritative record of the proof
surface. Files that are not part of the active `_CoqProject` are not included
in the kernel build.
