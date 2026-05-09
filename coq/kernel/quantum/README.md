# kernel/quantum

CHSH, Tsirelson, NPA-PSD, Born rule, and the rest of the quantum-tier
machinery. Reaches the quantum boundary by polynomial certificate over ℚ.
**No Hilbert space invoked in the verification step.**

## Files

### CHSH

| File | Purpose |
|---|---|
| `CHSH.v` | Trial parsing, witness counters, basic CHSH primitives |
| `CHSHExtraction.v` | Extracted-trace CHSH value computation |
| `CHSHStatisticalBridge.v` | Statistical CHSH violation; `chsh_stat_violation_not_local` |
| `CHSHCouplingBridge.v` | Categorical coupling ↔ CHSH bound |
| `BoxCHSH.v` | Box-CHSH variant with bounded |S| ≤ 4 |

### Tsirelson — the named bound

| File | Purpose |
|---|---|
| `TsirelsonGeneral.v` | General quantum Tsirelson definitions |
| `TsirelsonFromAlgebra.v` | Bridge from algebraic to general form |
| `TsirelsonUpperBound.v` | μ=0 fragment characterization, classical bound = 2 |
| `TsirelsonUniqueness.v` | Jan 2026 corrected understanding (μ=0 ⇒ S≤4 algebraically) |
| `TsirelsonQuantumModel.v` | Quantum-realizable model layer |

### NPA-PSD bridge

| File | Purpose |
|---|---|
| `QuantumPartitionPSD.v` | **`column_contractive_iff_quantum_realizable`** — biconditional |
| `NPAMomentMatrix.v` | NPA moment-matrix definitions |
| `SemidefiniteProgramming.v` | PSD primitives |
| `ConstructivePSD.v` | Quadratic-form PSD certificate over ℚ |
| `MinorConstraints.v` | The four 3×3 minor inequalities |
| `ValidCorrelation.v` | Valid-correlation predicate |

### Born rule — uniqueness from boundary conditions

| File | Purpose |
|---|---|
| `BornRule.v` | Bloch-sphere measurement probabilities; uniqueness from linearity |
| `BornRuleLinearity.v` | No-signaling ⇔ linearity (definitional) |
| `ProbabilityImpossibility.v` | Negative result: composition alone doesn't determine Born rule |

### Quantum tier supporting

| File | Purpose |
|---|---|
| `QuantumBound.v` | Certification interface for quantum-tier accounting |
| `QuantumEquivalence.v` | Zero-cost quantum tier bookkeeping |
| `EntanglementEntropy.v` | Support-level partial-trace + rank surrogate |
| `NoCloning.v` | No-cloning at the kernel state level |
| `Unitarity.v` | Reversible-evolution / purity-conservation argument |
| `Purification.v` | Purification-style reasoning over kernel states |
| `InformationCausality.v` | Record-level IC / μ comparison (bookkeeping, not physics) |

## Load-bearing exports cited from the README

- `column_contractive_iff_quantum_realizable` — chain claim
- `algebraically_coherent_tsirelson_general` (lives in [`category/`](../category/))
- `tsirelson_from_row_bounds`, `tsirelson_bound_tight`, `master_tsirelson_conditional`

## Imports

`foundation/`, `mu_calculus/`, `category/`.
