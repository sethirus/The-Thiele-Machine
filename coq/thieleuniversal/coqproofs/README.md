# Thiele Universal - Coq Proofs

**Mission:** Universal Turing Machine simulation proofs demonstrating Thiele Machine universality.

## Structure

- `CPU.v` - CPU - Defines: Instr, State; Key results: read_pc_write_pc, read_pc_write_nonpc, read_pc_write_mem (+5 more)
- `TM.v` - TM - Defines: TM; Key results: firstn_repeat, skipn_repeat, delta_rule_single (+3 more)
- `ThieleUniversal.v` - Thiele Universal - Defines: interpreter_witness; Key results: cpu_rules_fit_window, cpu_program_is_blind, thiele_universal_recap (+1 more)
- `UTM_CoreLemmas.v` - UTM Core Lemmas - Key results: length_UTM_Encode_encode_rule, flat_map_cons, nth_app_lt (+34 more)
- `UTM_Encode.v` - UTM Encode - Key results: encode_z_le_two, decode_z_abs_le_one, decode_encode_LoadConst (+10 more)
- `UTM_Program.v` - UTM Program - Key results: RULES_START_ADDR_le_TAPE_START_ADDR, nth_firstn_lt, program_instrs_length_gt_48 (+19 more)
- `UTM_Rules.v` - UTM Rules - Key results: utm_blank_lt_base, utm_rules_write_lt_base, utm_rules_move_abs_le_one

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `CPU.v` | 0 | ✅ |
| `TM.v` | 0 | ✅ |
| `ThieleUniversal.v` | 0 | ✅ |
| `UTM_CoreLemmas.v` | 0 | ✅ |
| `UTM_Encode.v` | 0 | ✅ |
| `UTM_Program.v` | 0 | ✅ |
| `UTM_Rules.v` | 0 | ✅ |

**Result:** All 7 files verified with 0 admits.
