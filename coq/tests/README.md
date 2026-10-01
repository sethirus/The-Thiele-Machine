# Coq Tests

**Mission:** Coq test files for verification and necessity checking.

## Structure

- `TestNecessity.v` - Test Necessity - Key results: w_decreasing_empty_FAILS, w_privileged_empty, w_privileged_sequential_REALLY_FAILS (+7 more)
- `verify_nofi_load_bearing.v` - Verify NoFI load-bearing obligations
- `verify_zero_admits.v` - verify zero admits
- `CloseoutVerification.v` - End-to-end closeout: every named claim resolves to a closed Coq proof or an explicit non-claim
- `ClaimBoundaryRegression.v` - Claim-boundary regression targets
- `WFDrivenRunRegression.v` - Well-formed driven-run regression targets
- `SemanticContractRegression.v` - Inhabited execution contracts and correlator boundary cases

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `TestNecessity.v` | 0 | ✅ |
| `verify_nofi_load_bearing.v` | 0 | ✅ |
| `verify_zero_admits.v` | 0 | ✅ |
| `CloseoutVerification.v` | 0 | ✅ |
| `ClaimBoundaryRegression.v` | 0 | ✅ |
| `WFDrivenRunRegression.v` | 0 | ✅ |
| `SemanticContractRegression.v` | 0 | ✅ |

**Result:** All 7 active `.v` files are verified with 0 admits.

The vacuity-gate fixture `VacuitySmoke.v` is in `coq/test_fixtures/`; pytest `tests/test_vacuity_gate.py` enforces it.
