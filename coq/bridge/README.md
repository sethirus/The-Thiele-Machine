# Bridge Embeddings

**Mission:** Embedding proofs connecting external frameworks (BoxWorld, quantum, entropy, causality) to the kernel.

## Structure

- `BoxWorld_to_Kernel.v` - Box World to Kernel - Key results: trial_bits_ok_implies_chsh_bits_ok, simulation_correctness_trials, simulation_chsh_invariance (+3 more)
- `Causal_to_Kernel.v` - Causal to Kernel - Key results: decodes_to_self
- `Entropy_to_Kernel.v` - Entropy to Kernel - Key results: decodes_to_self
- `FiniteQuantum_to_Kernel.v` - Finite Quantum to Kernel - Key results: trial_bits_ok_implies_chsh_bits_ok, simulation_correctness_trials, trial_bits_ok_all_zeros_ones (+5 more)
- `PythonMuLedgerBisimulation.v` - Python Mu Ledger Bisimulation - Defines: PythonMuLedger; Key results: discovery_charge_preserves_bisim, execution_charge_preserves_bisim, combined_charge_preserves_bisim (+4 more)
- `Randomness_to_Kernel.v` - Randomness to Kernel - Key results: decode_is_filter_payloads
- `Tomography_to_Kernel.v` - Tomography to Kernel - Key results: decodes_to_self

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `BoxWorld_to_Kernel.v` | 0 | ✅ |
| `Causal_to_Kernel.v` | 0 | ✅ |
| `Entropy_to_Kernel.v` | 0 | ✅ |
| `FiniteQuantum_to_Kernel.v` | 0 | ✅ |
| `PythonMuLedgerBisimulation.v` | 0 | ✅ |
| `Randomness_to_Kernel.v` | 0 | ✅ |
| `Tomography_to_Kernel.v` | 0 | ✅ |

**Result:** All 7 files verified with 0 admits.
