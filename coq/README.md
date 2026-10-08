# Coq Proofs for the Thiele Machine

This directory contains the active Coq proof tree for the Thiele Machine: the abstract model and its results, and the links that tie the small machine of [`minimal/`](../minimal/) and the universal machine U to them.

The proof gates check that the active tree builds, that no proof is admitted, and that no project-local axiom appears in any theorem's dependencies (`artifacts/print_assumptions_all_proofs.json`, written on Linux by `make assumption-receipt`).

## Build

From the repository root, with Coq 8.18 and MetaCoq 1.2.1 installed (`scripts/install_metacoq.sh` builds MetaCoq from pinned source; the vendored L modules need it):

```bash
make coq-gate     # builds the vendored undecidability modules, regenerates coq/Makefile from _CoqProject, and builds the active tree
```

`coq/_CoqProject` maps `../minimal` to the `Minimal` namespace, so the small-machine files in `minimal/` build with the tree, and `../vendor/coq-undecidability/theories` to `Undecidability`.
For a fresh source-only rebuild, see [docs/REPRODUCTION.md](../docs/REPRODUCTION.md).

## Directory structure

| Directory | Description |
|-----------|-------------|
| `kernel/` | The abstract model, its results, and the links to the small machine; see [`kernel/README.md`](kernel/README.md) |
| `test_fixtures/` | `VacuitySmoke.v`, the fixture the kernel-conversion vacuity gate checks itself against |
| top-level `AssumptionsProbeAll.v` | Generated `Print Assumptions` probe that feeds the assumption receipt |
| `INQUISITOR_ASSUMPTIONS.json` | The Inquisitor's allow list of standard-library axioms, its assumption-audit targets and its paper map |
| `axioms.txt` | The project-local axiom policy, pointing to the receipt |

The small machine itself lives outside this directory, in [`minimal/`](../minimal/): `EarnedCore.v`, `EarnedGeneric.v`, `EarnedMulti.v`, `ThieleComplete.v`, `ThieleCompleteWindow.v`, `UniversalThiele.v`, `UniversalCodes.v`, `UniversalNoCopy.v`, `EarnedPriced.v`, `PricedComplete.v`, `Presented.v` and `EarnedMultiPriced.v`, all on the Coq standard library alone.

See the `README.md` in each subdirectory for details on its contents.
