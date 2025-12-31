# Kernel Proofs

The core formal proofs of the Thiele Machine. These files contain the fundamental theorems.

**Proof Status**: HIGH: 0, MEDIUM: 4, LOW: 4 (see `INQUISITOR_REPORT.md`)
**Architecture**: Zero global axioms - all assumptions explicitly parameterized

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

## Assumption Architecture (NEW)

All hard-to-prove mathematical results are now **explicitly parameterized** via:

- **AssumptionBundle.v** - `HardMathFacts` record bundling all assumptions
- **HardAssumptions.v** - Module Type interface for assumption contracts

**No global axioms exist** - all theorems that depend on assumptions take them as explicit parameters using Section/Context. This makes the trusted computing base (TCB) visible and prevents assumption creep.

### The Six Assumptions

1. **normalized_E_bound** - Probability theory (elementary, SHOULD be proven)
2. **valid_box_S_le_4** - Triangle inequality (elementary, SHOULD be proven)
3. **local_box_S_le_2** - Bell's CHSH inequality (16-case proof, SHOULD be proven)
4. **pr_box_no_extension** - PR box monogamy (case analysis, SHOULD be proven)
5. **symmetric_coherence_bound** - NPA hierarchy (certificate-checkable)
6. **tsirelson_from_algebraic_coherence** - Tsirelson's theorem (deep result)

Items 1-4 are **proof debt** (~850 lines, tracked in `PROOF_DEBT.md`).
Items 5-6 are acceptable conditional assumptions (deep mathematical results).

## Build

```bash
cd coq/kernel
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq -j$(nproc)
```

## Verification

```bash
# Check no global axioms
python3 ../../scripts/inquisitor.py

# Check assumption surface
coqc AssumptionBundle.v
# Print Assumptions on key theorems to verify explicit dependencies
```

## File Count: 57
