# Kernel

Core structural-constraint proofs, optimization bounds, and bisimulation
results for the Thiele Machine kernel. **247 files, zero admits.**

The `Kernel` namespace is preserved across the topical subdirectories via
multi-line
`-R kernel/<subdir> Kernel` mappings in [`_CoqProject`](../_CoqProject), so
existing imports `From Kernel Require Import VMState` still work unchanged.

## Subdirectory map

| Directory | Files | Role |
|---|---:|---|
| [`foundation/`](foundation/) | 64 | VM model, simulation, classical/Turing fragment |
| [`mu_calculus/`](mu_calculus/) | 12 | μ initiality, cost derivation, Shannon bridges, hierarchy |
| [`nfi/`](nfi/) | 40 | No Free Insight chain — A2 substrate-independence, structural advantage |
| [`frontier/`](frontier/) | 17 | F1, F2, F3 closure files |
| [`category/`](category/) | 5 | Categorical bridge laws and algebraic Tsirelson |
| [`quantum/`](quantum/) | 38 | CHSH, Tsirelson, NPA-PSD, Born rule, no-cloning, unitarity |
| [`curvature/`](curvature/) | 30 | Einstein, Riemann, simplicial geometry, μ-gravity, Lorentzian |
| [`thermodynamic/`](thermodynamic/) | 10 | Bekenstein, Clausius, finite-information |
| [`witness/`](witness/) | 9 | Shadow projection, blindness, witness preservation |
| [`hardware_bridge/`](hardware_bridge/) | 5 | Three-layer iso, RTL correspondence, Python/OCaml bisim |
| [`aggregators/`](aggregators/) | 9 | TOE, ThieleGenesis, MasterSummary, audits |
| [`reductions/`](reductions/) | 5 | Reduction and undecidability constructions |
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

All 247 files build with **zero `Admitted.` declarations** and **zero
project-local axioms** beyond the named bridge premises documented in the
README §"What is and isn't forced":

- `mu_landauer_unruh_calibrated` (in [`curvature/PhysicalSubstrate.v`](curvature/PhysicalSubstrate.v))
- `bsc_kami_compilation_trusted` (in [`hardware_bridge/`](hardware_bridge/) — BSC compiler trust)
- Standard Coq axioms: `ClassicalDedekindReals.sig_forall_dec`, `FunctionalExtensionality.functional_extensionality_dep`

Reproduce with `make -C coq` from the repo root, then
`Print Assumptions ReceiptTheorem.` to inspect the closure.

## Load-bearing exports

The README's [five formal claims](../../README.md#the-five-formal-claims) and
[chain of claims](../../README.md#the-chain-of-claims) point into specific
files inside this tree. The source files, their imports, and the generated
dependency and assumption receipts are the authoritative record of the proof
surface. Files that are not part of the active `_CoqProject` are not included
in the kernel build.
