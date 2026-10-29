# Coq Proofs for the Thiele Machine

This directory contains the active Coq proof tree for the Thiele Machine: the abstract model and its results, with the small models of [`minimal/`](../minimal/).

The proof gates check that the active tree builds, that no proof is admitted, and that no project-local axiom appears in any theorem's dependencies (`artifacts/print_assumptions_all_proofs.json`, written on Linux by `make assumption-receipt`).

## Build

From the repository root, with Coq 8.18 and its standard library installed:

```bash
make coq-gate     # regenerates coq/Makefile from _CoqProject and builds the active tree
```

`coq/_CoqProject` maps `../minimal` to the `Minimal` namespace, so the files in `minimal/` build with the tree.
For a fresh source-only rebuild, see [docs/REPRODUCTION.md](../docs/REPRODUCTION.md).

## Directory structure

| Directory | Description |
|-----------|-------------|
| `kernel/` | The abstract model and its results; see [`kernel/README.md`](kernel/README.md) |
| `audit/` | Least prices, the least price for the history lift (`AxThieleLeast.v`), observation contracts and boundary results |
| `test_fixtures/` | `VacuitySmoke.v`, the fixture the kernel-conversion vacuity gate checks itself against |
| top-level `AssumptionsProbeAll.v` | Generated `Print Assumptions` probe that feeds the assumption receipt |
| `INQUISITOR_ASSUMPTIONS.json` | The Inquisitor's allow list of standard-library axioms, its assumption-audit targets and its paper map |
| `axioms.txt` | The project-local axiom policy, pointing to the receipt |

The small models live outside this directory, in [`minimal/`](../minimal/), among them `Napkin.v` (the smallest machine), `SliceCore.v`, `StepLaw.v`, `HeatOrRoom.v` and `VerifierSmall.v`, all on the Coq standard library alone.

See the `README.md` in each subdirectory for details on its contents.
