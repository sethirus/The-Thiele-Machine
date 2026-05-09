# Kernel

Core structural-constraint proofs, optimization bounds, and bisimulation
results for the Thiele Machine kernel. **161 files, zero admits.**

The directory was reorganized into 12 topical subdirectories on
2026-05-09 (audit:
[`artifacts/COQ_NECESSITY_AUDIT.md`](../../artifacts/COQ_NECESSITY_AUDIT.md)).
The `Kernel` namespace is preserved across all subdirectories via multi-line
`-R kernel/<subdir> Kernel` mappings in [`_CoqProject`](../_CoqProject), so
existing imports `From Kernel Require Import VMState` still work unchanged.

## Subdirectory map

| Directory | Files | Role |
|---|---:|---|
| [`foundation/`](foundation/) | 22 | VM model, simulation, classical/Turing fragment |
| [`mu_calculus/`](mu_calculus/) | 12 | μ initiality, cost derivation, Shannon bridges, hierarchy |
| [`nfi/`](nfi/) | 25 | No Free Insight chain — A2 substrate-independence, structural advantage |
| [`frontier/`](frontier/) | 12 | F1, F2, F3 closure files (per `FRONTIER_PLAN.md`) |
| [`category/`](category/) | 5 | Categorical bridge laws and algebraic Tsirelson |
| [`quantum/`](quantum/) | 26 | CHSH, Tsirelson, NPA-PSD, Born rule, no-cloning, unitarity |
| [`curvature/`](curvature/) | 30 | Einstein, Riemann, simplicial geometry, μ-gravity, Lorentzian |
| [`thermodynamic/`](thermodynamic/) | 6 | Bekenstein, Clausius, finite-information |
| [`witness/`](witness/) | 8 | Shadow projection, blindness, witness preservation |
| [`hardware_bridge/`](hardware_bridge/) | 5 | Three-layer iso, RTL correspondence, Python/OCaml bisim |
| [`aggregators/`](aggregators/) | 7 | TOE, ThieleGenesis, MasterSummary, audits |
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

All 161 files build with **zero `Admitted.` declarations** and **zero
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
files inside this tree. The full audit, including which files are
load-bearing, support, exposition, or removal candidates, is at:

- [`artifacts/COQ_NECESSITY_AUDIT.md`](../../artifacts/COQ_NECESSITY_AUDIT.md)
- [`artifacts/coq_necessity_audit.csv`](../../artifacts/coq_necessity_audit.csv)
- [`artifacts/coq_chain_diagram.mmd`](../../artifacts/coq_chain_diagram.mmd)

## Removal candidates from the audit

Five files flagged for removal as analogy/scaffold (see audit for rationale):

- [`curvature/KernelNoether.v`](curvature/KernelNoether.v) — Z-shifts as
  bookkeeping symmetry; analogy file
- [`witness/DerivedTime.v`](witness/DerivedTime.v) — time as derived
  trace-equivalence; analogy
- [`witness/ObserverDerivation.v`](witness/ObserverDerivation.v) —
  observational-equivalence scaffold; no consumers
- [`coq/archive/ProofBedrocStrengthening.v`](../archive/ProofBedrocStrengthening.v) — already archived
- [`coq/physics/PreregSplit.v`](../physics/PreregSplit.v) — pre-registration tooling

Decision pending; nothing has been deleted.
