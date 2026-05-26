# Coq Tests

**Mission:** Coq test files for verification and necessity checking.

## Structure

- `TestNecessity.v` - Test Necessity - Key results: w_decreasing_empty_FAILS, w_privileged_empty, w_privileged_sequential_REALLY_FAILS (+7 more)
- `verify_nofi_load_bearing.v` - Verify NoFI load-bearing obligations
- `verify_zero_admits.v` - verify zero admits
- `CloseoutVerification.v` - End-to-end closeout: every named claim resolves to a closed Coq proof or an explicit non-claim
- `VacuitySmoke.v` - Smoke fixture for `scripts/vacuity_gate.py`: deliberately vacuous theorems the gate must flag, real ones it must clear

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `TestNecessity.v` | 0 | ✅ |
| `verify_nofi_load_bearing.v` | 0 | ✅ |
| `verify_zero_admits.v` | 0 | ✅ |
| `CloseoutVerification.v` | 0 | ✅ |
| `VacuitySmoke.v` | 0 | ✅ (fixture; pytest `tests/test_vacuity_gate.py` enforces) |

**Result:** All 5 files verified with 0 admits.
