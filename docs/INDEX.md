# Thiele Machine Documentation

- [PT_EQUALS_NPT](PT_EQUALS_NPT.md)
- [WHY_P_VS_NP_ISNT_THE_AXIS](WHY_P_VS_NP_ISNT_THE_AXIS.md)
- [T_LEAP_MINIMAL_ISA](T_LEAP_MINIMAL_ISA.md)
- [PROOF_STATUS](PROOF_STATUS.md)
- [RECEIPT_FORMAT](RECEIPT_FORMAT.md)

## Challenge harness

Use `scripts/challenge.py` to test receipts or attempt refinements:

```
python scripts/challenge.py verify receipts
```
prints `verification succeeded` on a valid bundle.

```
python scripts/challenge.py refinement coarse_dir refined_dir
```
prints `μ monotonicity holds` unless a counterexample causes
`μ monotonicity violated`.
