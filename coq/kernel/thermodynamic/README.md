# kernel/thermodynamic

Bekenstein bound, Clausius-style relations, Landauer-tier entropy, and
finite-information arguments. These are the thermodynamic primitives that the
NFI → Einstein bridge composes.

## Files

| File | Purpose |
|---|---|
| `BekensteinCalibration.v` | Bekenstein-bound calibration; PSPLIT/PNEW lemmas tied to area |
| `ClausiusFromEntropyArea.v` | Clausius-style relation from entropy/area accounting |
| `ThermoEinsteinBridge.v` | Bridge from thermodynamic relations to Einstein-form identities |
| `EntropyImpossibility.v` | Why naive entropy fails (motivates Bekenstein bound) |
| `FiniteInformation.v` | Second-law style finite-state monotonicity |
| `LocalInfoLoss.v` | Signed module-count loss (no absolute Landauer claim here) |

## Load-bearing role

These files are bridge premises rather than seed claims. They are cited
indirectly via [`curvature/NoFIToEinstein.v`](../curvature/NoFIToEinstein.v) and
[`nfi/LandauerDerivation.v`](../nfi/LandauerDerivation.v). The README §"What
is and isn't forced" is explicit that the Bekenstein/calibration layer is a
named hypothesis, not a derivation.

## Imports

`foundation/`, `mu_calculus/`, `curvature/` (for entropy-area context).
