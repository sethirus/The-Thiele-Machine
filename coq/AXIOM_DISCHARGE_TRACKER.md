# Axiom Discharge Tracker

**Goal:** Eliminate all axioms with real, compiling proofs.

**Status:** IN PROGRESS

---

## Summary

| Category | Total | Discharged | Remaining |
|----------|-------|------------|-----------|
| Physical Constants | 20 | 0 | 20 |
| Type/Interface Axioms | 14 | 0 | 14 |
| Mathematical Theorems | 15 | 0 | 15 |
| Domain-Specific Claims | 19 | 0 | 19 |
| **TOTAL** | **68** | **0** | **68** |

---

## Category 1: Physical Constants

These can be replaced with concrete definitions using Coq's real number library.

### kernel/TsirelsonBoundProof.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `sqrt2 : R` | PENDING | Use `sqrt 2` from Reals |
| `sqrt2_squared : sqrt2 * sqrt2 = 2` | PENDING | Prove via `sqrt_sqrt` |
| `sqrt2_positive : sqrt2 > 0` | PENDING | Prove via `sqrt_lt_R0` |
| `sqrt2_bounds : 1.4 < sqrt2 < 1.5` | PENDING | Derive from sqrt properties |
| `grothendieck_constant : R` | PENDING | Define concrete value ~1.782 |
| `grothendieck_value : 1.7 < grothendieck_constant < 1.8` | PENDING | Prove from definition |

### kernel/ConstantUnification.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `tau_mu : R` | PENDING | Define concrete value |
| `d_mu : R` | PENDING | Define concrete value |
| `k_B : R` | PENDING | Define as 1/100 (normalized) |
| `T : R` | PENDING | Define as 1 (normalized) |
| `tau_mu_pos : tau_mu > 0` | PENDING | Prove from definition |
| `d_mu_pos : d_mu > 0` | PENDING | Prove from definition |
| `k_B_pos : k_B > 0` | PENDING | Prove from definition |
| `T_pos : T > 0` | PENDING | Prove from definition |

### physics_exploration/HolographicGravity.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `G : R` | PENDING | Define normalized value |
| `G_positive : G > 0` | PENDING | Prove from definition |

### physics_exploration/EmergentSpacetime.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `d_mu : R` | PENDING | Define normalized value |
| `d_mu_positive : d_mu > 0` | PENDING | Prove from definition |

### physics_exploration/ParticleMasses.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `m_electron : R` | PENDING | Define normalized value |
| `m_muon : R` | PENDING | Define normalized value |
| `m_proton : R` | PENDING | Define normalized value |
| `masses_positive` | PENDING | Prove from definitions |

### physics_exploration/PlanckDerivation.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `k_B_value : k_B = / 100` | PENDING | Already a value axiom - define k_B directly |
| `T_value : T = 1` | PENDING | Already a value axiom - define T directly |

---

## Category 2: Type/Interface Axioms

### kernel/QuantumBoundComplete.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `VMState : Type` | PENDING | Import from VMState.v |
| `vm_instruction : Type` | PENDING | Import from VMState.v |
| `Box : Type` | PENDING | Import from BoxCHSH.v |
| `box_apply : Box -> nat -> nat -> nat -> nat -> Q` | PENDING | Import from BoxCHSH.v |
| `non_negative : Box -> Prop` | PENDING | Import from BoxCHSH.v |
| `normalized : Box -> Prop` | PENDING | Import from BoxCHSH.v |
| `box_from_trace : ...` | PENDING | Import or define |
| `mu_cost_of_instr : ...` | PENDING | Import from MuCostModel.v |
| `BoxCHSH_S : Box -> Q` | PENDING | Import from BoxCHSH.v |
| `BoxCHSH_E : Box -> nat -> nat -> Q` | PENDING | Import from BoxCHSH.v |
| `is_ljoin : vm_instruction -> Prop` | PENDING | Define from instr type |
| `is_reveal : vm_instruction -> Prop` | PENDING | Define from instr type |
| `is_lassert : vm_instruction -> Prop` | PENDING | Define from instr type |

---

## Category 3: Mathematical Theorems

### kernel/MinorConstraints.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `Fine_theorem` | PENDING | Prove via LP duality |
| `Gram_PSD` | PENDING | Prove via matrix theory |
| `local_box_satisfies_minors` | PENDING | Prove from factorization |

### kernel/SemidefiniteProgramming.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `PSD_diagonal_nonneg` | PENDING | Prove from PSD definition |
| `schur_2x2_criterion` | PENDING | Prove via determinant |
| `PSD_cauchy_schwarz` | PENDING | Prove from PSD definition |
| `PSD_principal_minors_nonneg` | PENDING | Prove from PSD definition |
| `PSD_off_diagonal_bound` | PENDING | Prove from Cauchy-Schwarz |

### kernel/TsirelsonBoundDirect.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `quadratic_constraint_minimum` | PENDING | Prove via calculus/nra |
| `f_bound_max` | PENDING | Prove via calculus |
| `tsirelson_bound_symmetric` | PENDING | Prove from NPA structure |
| `tsirelson_bound_symmetric_lower` | PENDING | Prove from NPA structure |
| `reduction_to_symmetric_stmt` | PENDING | Prove from optimization |
| `reduction_to_symmetric` | PENDING | Prove from optimization |

### kernel/TsirelsonBoundComplete.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `optimal_satisfies_constraint_axiom` | PENDING | Prove from NPA |
| `chsh_squared_bound_from_constraint_axiom` | PENDING | Prove algebraically |

### kernel/TsirelsonBoundProof2.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `chsh_bound_from_psd` | PENDING | Prove from PSD properties |
| `chsh_bound_from_psd_axiom` | PENDING | Duplicate - remove |

### kernel/TsirelsonBoundTDD.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `optimal_is_psd_axiom` | PENDING | Prove from quantum structure |

### kernel/TsirelsonBoundVerification.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `test_config_111_minor3_negative_axiom` | PENDING | Compute and verify |
| `config_111_0_not_psd_axiom` | PENDING | Compute and verify |

---

## Category 4: Domain-Specific Claims

### kernel/TsirelsonBoundProof.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `quantum_CHSH_bound` | PENDING | Prove from NPA hierarchy |
| `optimal_is_quantum_realizable` | PENDING | Prove from quantum theory |
| `optimal_achieves_tsirelson` | PENDING | Prove from optimization |
| `classical_CHSH_bound` | PENDING | Prove from Fine's theorem |
| `grothendieck_inequality` | PENDING | Deep math - may keep as axiom |

### kernel/QuantumBoundComplete.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `mu_zero_preserves_factorizable` | PENDING | Prove from instruction semantics |
| `mu_positive_enables_nonfactorizable` | PENDING | Prove from instruction semantics |
| `nonfactorizable_is_quantum_realizable` | PENDING | Physics axiom - justify |
| `mu_positive_enables_tsirelson` | PENDING | Prove from above |
| `mu_zero_classical_bound` | PENDING | Prove from factorization |
| `mu_positive_exceeds_classical` | PENDING | Prove existence witness |

### kernel/NPAMomentMatrix.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `quantum_realizable_implies_normalized` | PENDING | Prove from quantum axioms |

### kernel/QuantumBound.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `quantum_admissible_implies_no_supra_cert` | PENDING | Prove from bounds |

### kernel/TsirelsonUniqueness.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `mu_zero_classical_bound` | PENDING | Duplicate - consolidate |

### kernel/MuInformationTheoreticBounds.v
| Axiom | Status | Notes |
|-------|--------|-------|
| `partition_claim_information_bound` | PENDING | Prove from counting |
| `state_space_reduction_bound` | PENDING | Prove from log properties |
| `mu_zero_classical_characterization` | PENDING | Prove from instruction analysis |
| `mu_positive_quantum_characterization` | PENDING | Prove from instruction analysis |

---

## Discharge Progress Log

### 2026-02-02
- Created this tracking document
- Identified 68 axioms across 4 categories
- Starting systematic discharge

---

## Notes

1. **Priority Order:**
   - Physical constants (easy wins)
   - Type imports (structural fixes)
   - Mathematical theorems (need careful proofs)
   - Domain-specific (hardest, may need design changes)

2. **Compilation Requirement:**
   - Every change must compile with `coqc`
   - Run full build after each file is fixed
   - No `Admitted` allowed as replacement

3. **Acceptable Remaining Axioms:**
   - `functional_extensionality` (standard Coq)
   - `propositional_extensionality` (standard Coq)
   - Truly external physics facts with citations
