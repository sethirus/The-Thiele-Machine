# Axiom and admit inventory for the Thiele Machine development

_Updated December 2025._

## Summary

- **Total Axioms in compiled code (`_CoqProject`)**: 0
- **Total Admits in compiled code (`_CoqProject`)**: 0
- **Build status**:
   - `make -C coq core` ✅
   - `make -C coq bridge-timed BRIDGE_TIMEOUT=900` ✅ (up to date)
- **Audit command**: `./scripts/audit_coq_proofs.sh`

## Notes

- The active Coq tree is axiom-free and admit-free by construction; anything that was previously modeled as an axiom has been either:
  - made constructive/definitional, or
  - reframed so theorems state only what is provable without additional assumptions.

- The audit currently reports **15 opaque declarations** (not axioms). These are used to control unfolding/unification and keep proof search tractable.
  - See `./scripts/audit_coq_proofs.sh` output for the per-file breakdown.

## Main Theorems (Build Gate)

1. **`thiele_formally_subsumes_turing`** (`Subsumption.v`)
   - Proves: TM ⊂ Thiele (containment and exponential separation)
   - Status: ✅ Fully proved, no axioms

2. **`thiele_exponential_separation`** (`Separation.v`)
   - Proves: Sighted Thiele has polynomial advantage over blind TM on Tseitin families
   - Status: ✅ Fully proved

3. **`thiele_step_n_tm_correct`** (`Simulation.v`)
   - Proves: Thiele program correctly simulates TM execution
   - Status: ✅ Fully proved with `all_steps_ok` hypothesis

## Verification Commands

```bash
# Proof audit (should report 0 admits, 0 axioms)
./scripts/audit_coq_proofs.sh

# Build gates
make -C coq core
make -C coq bridge-timed BRIDGE_TIMEOUT=900
```

## BridgeDefinitions.v status

`coq/thielemachine/verification/BridgeDefinitions.v` currently contains **no** `Admitted.` proofs and no `Axiom` declarations.
