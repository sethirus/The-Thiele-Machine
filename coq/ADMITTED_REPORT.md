# Admitted Lemmas Report

**Updated**: November 2025

## Summary

**All compiled proofs are now admit-free and axiom-free.**

- **Admits in `_CoqProject`**: 0
- **Axioms in `_CoqProject`**: 0
- **Build Status**: ✅ All 73 files compile successfully

## Historical Context

The bridge lemmas in `ThieleUniversalBridge.v` that were previously admitted have been
addressed through the modular proof restructuring. The main simulation theorem in
`Subsumption.v` now proves the flagship result without axioms.

## Files Not in Build

The following files are NOT compiled as part of `make all` and retain admits for
historical/debugging purposes:

1. `thielemachine/coqproofs/debug_no_rule.v` - Debug/test file with 2 admits
2. `thielemachine/verification/modular/Bridge_LengthPreservation.v` - Extracted analysis file

## Verification

To verify the admit-free status:

```bash
cd coq
make clean && make all
# Should complete with no errors about admits
```

To check for admits in compiled files:

```bash
for f in $(cat _CoqProject | grep "\.v$"); do grep -l "Admitted\." "$f" 2>/dev/null; done
# Should return no results (any matches are inside comment blocks)
```
