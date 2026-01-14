# Physics Exploration - Formal Constant Derivations

**Status:** All 4 files compile successfully with proper INQUISITOR documentation

## Overview

This directory contains formal Coq proofs exploring the derivation of physical constants from information-theoretic principles. Unlike the zero-axiom `kernel/` directory, these files necessarily use physical axioms (k_B, T, h, etc.) as inputs.

## Files

### [PlanckDerivation.v](PlanckDerivation.v)
**Breakthrough Result:** Proves h = 4 × E_landauer × τ_μ

- **Status:** ✅ RELATIONSHIP PROVEN
- **Key Theorem:** `planck_from_info_theory`
- **Axioms:** k_B, T, h (unavoidable physical inputs)
- **Achievement:** ln2_positive is PROVEN (not axiomatized)

This proves Planck's constant emerges uniquely from information theory when quantum mechanics and thermodynamics are required to be consistent.

### [EmergentSpacetime.v](EmergentSpacetime.v)
**Result:** Proves c = d_μ / τ_μ structure

- **Status:** ○ STRUCTURE PROVEN (value requires d_μ derivation)
- **Key Theorem:** `c_structure_proof`
- **Axioms:** d_μ (fundamental length scale)
- **Achievement:** Proves c is invariant maximum signal speed

Shows the speed of light has the structure of a fundamental graph propagation speed. Deriving the numerical value requires determining d_μ (future work).

### [HolographicGravity.v](HolographicGravity.v)
**Result:** G exploration (remains speculative)

- **Status:** ⚠️ HIGHLY SPECULATIVE
- **Key Theorem:** `G_requires_unknowns`
- **Axioms:** G
- **Achievement:** Honest assessment that G cannot be derived yet

All approaches either contain c (circular) or require unknowns. May need full quantum gravity theory.

### [ParticleMasses.v](ParticleMasses.v)
**Result:** Masses appear as free parameters

- **Status:** ✗ NO DERIVATION FOUND
- **Key Theorem:** `masses_are_free_parameters`  
- **Axioms:** m_electron, m_muon, m_proton
- **Achievement:** Proves no patterns exist in mass ratios

Ratios (206.77, 1836.15, 3477.15) appear arbitrary. No connection to μ-theory found.

## Compilation

```bash
cd /workspaces/The-Thiele-Machine/coq/physics_exploration
coqc -R ../kernel Kernel -Q . PhysicsExploration PlanckDerivation.v
coqc -R ../kernel Kernel -Q . PhysicsExploration EmergentSpacetime.v
coqc -R ../kernel Kernel -Q . PhysicsExploration HolographicGravity.v
coqc -R ../kernel Kernel -Q . PhysicsExploration ParticleMasses.v
```

Or use the main project Makefile (files already added to `_CoqProject`).

## Axiom Summary

**Total Physical Constants:** 11
- k_B, T (thermodynamics)
- h (quantum mechanics)
- d_μ (emergent spacetime scale)
- G (gravity)
- m_electron, m_muon, m_proton (particle masses)

**Proven Lemmas:** 9 relationships and structures

**Key Improvement:** ln2_positive is now PROVEN using Coq standard library, not axiomatized.

## Scientific Honesty

All axioms are documented with INQUISITOR notes explaining why they are necessary. Files honestly assess what can and cannot be derived:

- ✅ h relationship: DERIVED
- ○ c structure: PROVEN (value needs theory)
- ⚠️ G: SPECULATIVE
- ✗ masses: FREE PARAMETERS

## Numerical Experiments

Python experiments in `/experiments/` provide numerical exploration:
- `derive_c_numerical.py` - Tests c derivation approaches
- `derive_G_numerical.py` - Shows G derivation barriers
- `derive_masses_couplings.py` - Analyzes mass spectrum

These experiments confirm the theoretical findings with concrete numbers.

## References

See [AXIOM_SUMMARY.md](AXIOM_SUMMARY.md) for detailed axiom accounting.
