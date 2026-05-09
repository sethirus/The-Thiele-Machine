# kernel/category

Where categorical language stops being rhetoric. The morphism graph is
treated as a real category whose composition, identities, and tensor
structure are pinned to the actual graph operations.

## Files

| File | Purpose |
|---|---|
| `CategoryLaws.v` | Composition associativity, diagonal-relations-as-identities, equivalence on coupling lists |
| `CategoryBridge.v` | Pins the abstract laws to `graph_compose_morphisms` and `graph_add_identity` |
| `CategoryMonoidal.v` | Tensor / interchange law on morphism graph |
| `AlgebraicCoherence.v` | **`algebraically_coherent_tsirelson_general`** — the algebraic Tsirelson bound by `psatz Q 4` |
| `ConstantUnification.v` | Unification of stress-energy, area, and entropy constants used in calibration bridges |

## Load-bearing exports cited from the README

- `algebraically_coherent_tsirelson_general` — the `|S| ≤ 2√2` bound from NPA-1-style polynomial conditions, no Hilbert space invoked

## Imports

`foundation/`, `mu_calculus/` (for cost statements), `quantum/`
(coupling-aware lemmas).
