# Kernel Proofs

The core formal proofs of the Thiele Machine. These 55 files contain the fundamental theorems.

## Key Theorems

- **VMState.v, VMStep.v** - Core VM semantics
- **MuCostModel.v** - μ-cost accounting (no quantum assumptions)
- **CHSHExtraction.v** - CHSH from partitions (no quantum assumptions)
- **TsirelsonLowerBound.v** - Constructive achievability proof
- **TsirelsonUpperBound.v** - Upper bound from μ=0 constraints
- **TsirelsonUniqueness.v** - Master theorem: `tsirelson_from_pure_accounting`
- **QuantumEquivalence.v** - `quantum_foundations_complete` theorem
- **NoFreeInsight.v** - Core impossibility theorem
- **PythonBisimulation.v** - Coq VM ↔ Python VM equivalence
- **HardwareBisimulation.v** - Python VM ↔ Hardware equivalence
- **NonCircularityAudit.v** - Defense against reviewer attacks
- **MasterSummary.v** - `thiele_machine_is_complete` theorem

## Build

```bash
cd coq/kernel
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq -j$(nproc)
```

## File Count: 55
