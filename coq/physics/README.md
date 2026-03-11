# Physics Models

**Mission:** Physics model formalizations including wave/discrete duality and lattice geometry.

Note: `LandauerBridge.v` was archived to `archive/coq_unused/physics_landauer/` because it used a
standalone `VMConfig` type unconnected to the Thiele kernel. The proper kernel-connected Landauer
bridge is in `coq/kernel/LandauerBound.v` (Track D, D1).

## Structure

- `DiscreteModel.v` - Discrete Model - Defines: Cell; Key results: particle_count_cons, pair_update_involutive, particle_count_swap (+11 more)
- `DissipativeModel.v` - Dissipative Model - Defines: Cell; Key results: dissipative_step_energy_zero, dissipative_energy_nonincreasing, dissipative_energy_strict_when_hot (+2 more)
- `PreregSplit.v` - Prereg Split - Key results: split_tail_app, split_tail_lengths, split_tail_test_length_exact (+1 more)
- `TriangularLattice.v` - Triangular Lattice - Key results: lattice_id_coord_of_id, coord_of_id_lattice_id, coord_of_id_in_bounds (+24 more)
- `WaveModel.v` - Wave Model - Defines: WaveCell; Key results: map2_length, sum_list_app, rotate_left_length (+19 more)

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `DiscreteModel.v` | 0 | ✅ |
| `DissipativeModel.v` | 0 | ✅ |
| `PreregSplit.v` | 0 | ✅ |
| `TriangularLattice.v` | 0 | ✅ |
| `WaveModel.v` | 0 | ✅ |

**Result:** All 5 active files verified with 0 admits.
