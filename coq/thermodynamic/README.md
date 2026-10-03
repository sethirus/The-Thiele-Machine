# Thermodynamic Proofs

Landauer-style counting results and the boundary between ledger units and joules; physical calibration is a premise, not a result.

## Structure

- `LandauerDerived.v` - Landauer Derived - Defines: Erasure, PhysicalErasure; Key results: num_states_pos, fan_in_pos (+15 more)
- `LandauerJoules.v` - Physical-unit calibration boundary for Landauer-style costs
- `ThermodynamicBridge.v` - Thermodynamic Bridge - Defines: MuState, Operation; Key results: mu_nonnegative, mu_additive (+12 more)

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `LandauerDerived.v` | 0 | ✅ |
| `LandauerJoules.v` | 0 | ✅ |
| `ThermodynamicBridge.v` | 0 | ✅ |

**Result:** All 3 active `.v` files are verified with 0 admits.
