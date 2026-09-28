# kernel/witness

The shadow projection from full Thiele state to classical (mem, regs, pc) and
the consequence theorems. Where "the projection is lossy" stops being a
slogan.

## Files

| File | Purpose |
|---|---|
| `ShadowProjection.v` | `shadow_proj`, `strict_shadow`, **`shadow_strictly_lossy`** |
| `ThieleTraceProjection.v` | Forgetful map `VMState → ClassicalState` and the three shadow-projection theorems |
| `BlindnessRepresentation.v` | Forgetful map characterized as Turing-style blindness |
| `WitnessPreservationImpossibility.v` | No classical function can decide certification |
| `WitnessInsightGeneral.v` | Three-tier witness insight taxonomy; **`witness_insight_nonfree_general`** |
| `ObserverDerivation.v` | Physics-from-observational-equivalence support construction |
| `DerivedTime.v` | Time as a derived equivalence-class quantity |
| `InformationTopology.v` | μ-cost as routing metric over computation |

## Load-bearing exports cited from the README

- `shadow_strictly_lossy`
- `strict_shadow` projection — used by `vm_mu_not_classically_determined` in [coq/NecessityOfMuLedger.v](../../NecessityOfMuLedger.v)

## Imports

`foundation/` only. This is a thin layer right above the VM model.

`DerivedTime.v` and [`ObserverDerivation.v`](ObserverDerivation.v) provide
explanatory witness constructions alongside the load-bearing projection
results. They are support files; the theorem statements identify the claims
that depend on them.
