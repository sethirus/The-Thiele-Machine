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
| `AdditionalProbes.v` | Margolus-Levitin, Lloyd, and Bekenstein-Hawking bounds, each with its substrate constants as named hypotheses |
| `BekensteinBound.v` | `bekenstein_bound`: S_bits ≤ 2π E R / (ℏ c ln 2) from the second law for a thermal region and the Unruh formula, both taken as named premises |
| `SecondLawBoltzmannWall.v` | Boltzmann's formula and the thermal-bath second law are `Prop` definitions stated as substrate premises; the attempted derivation from the µ-ledger is a real-valued scaling of `vm_mu` that cannot fix the unit-system coefficient |
| `DimensionalGapTheorem.v` | `dimensional_gap_forces_constant`: for a dimensionless integer ledger with exponential microstate count, a ledger-linear entropy of Boltzmann form has coefficient `k_B * ln base` |
| `CalorimeterProtocolTarget.v` | Definitions for the two-state calorimeter protocol |
| `CalorimeterProtocol.v` | Two-state calorimeter: bath heat is `Delta / 2` (`canonical_reset_heat_exact`); `master_equation_does_not_fix_heat_scale`; the VM's cheapest certification step charges the protocol's one mu (`vm_minimal_certification_charges_canonical_reset_mu`) |

## Load-bearing role

These files are bridge premises rather than seed claims. They are cited
indirectly via [`curvature/NoFIToEinstein.v`](../curvature/NoFIToEinstein.v) and
[`nfi/LandauerDerivation.v`](../nfi/LandauerDerivation.v). The Bekenstein and
calibration layer is a named hypothesis, not a derivation; the top-level
README's [Scope](../../../README.md#scope) table (row "Physical
interpretation") states the same.

## Imports

`foundation/`, `mu_calculus/`, `curvature/` (for entropy-area context).
