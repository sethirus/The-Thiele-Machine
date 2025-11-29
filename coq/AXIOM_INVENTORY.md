# Axiom and Admit Inventory for the Thiele Machine Development

_Updated November 2025 - Complete audit and proof discharge._

## Summary

| Metric | Status |
|--------|--------|
| **Total Axioms in compiled code** | 0 ✅ |
| **Total Admits in compiled code** | 0 ✅ |
| **Total Coq files** | 85 |
| **Build status** | All files compile successfully |

## Verification

```bash
# Comprehensive audit
bash scripts/find_admits.sh

# Build all proofs
cd coq && make clean && make -j4
```

## Main Theorems (All Fully Proved)

### 1. Subsumption Theorem
**File**: `kernel/Subsumption.v`
- `thiele_simulates_turing`: Any TM can be simulated by a Thiele machine
- `turing_is_strictly_contained`: TM ⊊ Thiele (strict containment)

### 2. Exponential Separation
**File**: `thielemachine/coqproofs/Separation.v`
- `thiele_exponential_separation`: Sighted Thiele has polynomial advantage on Tseitin families

### 3. μ-Conservation
**File**: `kernel/MuLedgerConservation.v`
- `mu_conservation`: μ-bits are conserved during computation

### 4. Efficient Discovery
**File**: `thielemachine/coqproofs/EfficientDiscovery.v`
- `efficient_discovery_sound`: Partition discovery is polynomial-time and correct
- `discovery_profitable`: Discovery pays off on structured problems

### 5. Bridge Verification
**File**: `thielemachine/verification/ThieleUniversalBridge.v`
- `concrete_trace_0_19`: Universal machine executes correctly

## File Categories

### Kernel (12 files)
Core subsumption proofs and VM semantics.

### ThieleUniversal (7 files)
Universal Thiele machine definitions and CPU model.

### ThieleMachine (28 files)
Main machine proofs including separation, Bell inequalities, bisimulation.

### Verification (4 files)
Bridge verification with computational reflection.

### Modular Proofs (8 files)
Modular proof components for TM basics, encoding, Minsky machines.

### Physics Models (3 files)
Discrete, dissipative, and wave physics models.

### Thiele Manifold (4 files)
Manifold definitions and physics isomorphisms.

### Other (19 files)
CatNet, self-reference, spacetime, Shor primitives, etc.

## Historical Note

Previous versions contained axioms for:
- Bridge lemmas in ThieleUniversalBridge.v
- Import issues with rules_fit
- EfficientDiscovery.v specification axioms

All have been discharged or converted to concrete proofs as of November 2025.
