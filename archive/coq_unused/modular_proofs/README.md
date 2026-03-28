# Modular Proofs

**Mission:** Modular encoding, Minsky machine simulation, and Turing machine reduction proofs.

## Structure

- `CornerstoneThiele.v` - Cornerstone Thiele - Defines: colour, mask, mask_state (+4 more); Key results: classical_is_slow, thiele_cycles_are_small, thiele_is_fast (+2 more)
- `Encoding.v` - Encoding - Key results: BASE_ge_2, SHIFT_LEN_ge_1, BASE_pos (+13 more)
- `EncodingBounds.v` - Encoding Bounds - Key results: pow2_gt_succ, pow_pos, BASE_pos (+15 more)
- `Minsky.v` - Minsky - Defines: instr; Key results: set_nth_length, run_n_succ
- `Simulation.v` - Simulation - Key results: thiele_simulates_tm, thiele_machine_subsumes_turing_modular
- `TM_Basics.v` - TM Basics - Key results: replace_nth_length, replace_nth_Forall, tm_config_ok_digits (+7 more)
- `TM_to_Minsky.v` - TM to Minsky - Defines: TMasMinsky; Key results: encode_binary_nil, encode_binary_cons, head_symbol_from_right (+9 more)
- `ThieleInstance.v` - Thiele Instance - Key results: thiele_run_n_zero, thiele_run_n_succ, config_fits_ok (+9 more)
- `Thiele_Basics.v` - Thiele Basics - Defines: ModularThieleSemantics; Key results: mts_run_n_S, mts_run_n_one

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `CornerstoneThiele.v` | 0 | ✅ |
| `Encoding.v` | 0 | ✅ |
| `EncodingBounds.v` | 0 | ✅ |
| `Minsky.v` | 0 | ✅ |
| `Simulation.v` | 0 | ✅ |
| `TM_Basics.v` | 0 | ✅ |
| `TM_to_Minsky.v` | 0 | ✅ |
| `ThieleInstance.v` | 0 | ✅ |
| `Thiele_Basics.v` | 0 | ✅ |

**Result:** All 9 files verified with 0 admits.
