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

### Tsirelson: the named bound

| File | Purpose |
|---|---|
| `TsirelsonGeneral.v` | General quantum Tsirelson definitions |
| `TsirelsonFromAlgebra.v` | Bridge from algebraic to general form |
| `TsirelsonUpperBound.v` | μ=0 fragment characterization, classical bound = 2 |
| `TsirelsonUniqueness.v` | `Kernel.TsirelsonUniqueness.mu_zero_algebraic_bound`: μ=0 programs satisfy \|S\| ≤ 4, the algebraic maximum |
| `TsirelsonQuantumModel.v` | NPA PSD model layer |

### NPA-PSD bridge

| File | Purpose |
|---|---|
| `QuantumPartitionPSD.v` | **`column_contractive_iff_npa_psd`**: biconditional |
| `NPAMomentMatrix.v` | NPA moment-matrix definitions |
| `SemidefiniteProgramming.v` | PSD primitives |
| `ConstructivePSD.v` | Quadratic-form PSD certificate over ℚ |
| `MinorConstraints.v` | The four 3×3 minor inequalities |
| `ValidCorrelation.v` | Valid-correlation predicate |

### Born rule: uniqueness from boundary conditions

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

### Elliptope and further PSD gates

| File | Purpose |
|---|---|
| `ElliptopeCompletion.v` | The CHSH correlator quantum set as an existential completion of the zero-marginal NPA matrix; `elliptope_tsirelson`, `deterministic_strategy_elliptope`, `pr_box_not_elliptope` |
| `ElliptopeGate.v` | Decidable Z-arithmetic membership check for the elliptope, with soundness into `elliptope_realizable` (`elliptope_check_full_sound`) |
| `QuantumPartitionPSD_1AB.v` | Q_{1+AB} matrix certificates for specified correlator slots and higher moment slots; soundness only, no completeness for quantum behaviors |
| `GenRealizability.v` | A dimension-polymorphic PSD predicate (`psd_n`) and the bridge showing the 5x5 CHSH PSD as a special case |
| `TsirelsonFromIC.v` | CHSH consequence of the quadratic information-causality condition `E_I^2 + E_II^2 <= 1`; the protocol derivation and the physical principle are external premises |
| `TsirelsonFromMu.v` | A CHSH bound from two rotated-vector inequalities (`rotated_correlator_bounds`), supplied independently of the VM cost schedule |

### Measurement and Holevo

| File | Purpose |
|---|---|
| `HonestMeasurementImpliesNPA.v` | The converse-direction statement from `HonestMeasurementSystem` to `npa_psd`; the full statement is open in the literature and the file documents the obstruction |
| `PRBoxIsDishonest.v` | A deterministic PR-box realization is free, solves the 2-to-1 RAC protocol, and signals (`prbox_resource_signals`) |
| `OperatorAlgebra.v` | Finite-dimensional real matrix machinery for the Holevo bound; the spectral interface is a parameter |
| `HolevoDimensional.v` | A classical dimensional bound shaped like Holevo: `log_2 n` yes/no questions for `n` outcomes |
| `HolevoTwoQubit.v` | Holevo's bound at d = 2: `chi <= ln 2` for binary ensembles of real 2x2 density matrices |
| `HolevoGeneralD.v` | Holevo's bound at general finite dimension: `chi <= ln d` for binary ensembles of real d x d density matrices, with the spectral interface as a hypothesis |

## Load-bearing exports cited from the README

- `column_contractive_iff_npa_psd`: chain claim
- `algebraically_coherent_tsirelson_general` (lives in [`category/`](../category/))
- `tsirelson_from_row_bounds`, `tsirelson_rational_lower_witness`, `master_tsirelson_conditional`

## Imports

`foundation/`, `mu_calculus/`, `category/`, `nfi/`, `curvature/`.
