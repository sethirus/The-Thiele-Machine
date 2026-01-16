# Coq Proofs for the Thiele Machine

This directory contains **262 Coq proof files (~55,097 lines)** organized into logical modules.

**Status:** ✅ All files compile (261/262 .vo generated) | ✅ Zero Admitted anywhere | ✅ 52 axioms (see AXIOMS.md for full justification)

## Build

```bash
# From repository root:
make              # Build all 262 Coq proofs

# Or from coq/ directory:
cd coq
make -j4          # Build with 4 parallel jobs

# Clean and rebuild:
make clean
make -j4

# Analyze axioms:
../scripts/analyze_axioms.sh
```

## Directory Structure

| Directory | Files | Description |
|-----------|-------|-------------|
| `kernel/` | 54 | Core kernel proofs (Tsirelson, quantum foundations, bisimulation) |
| `kernel_toe/` | 6 | Theory of Everything cone (no-go theorems) |
| `thielemachine/` | 98 | Main Thiele Machine proofs (Bell, verification, deliverables) |
| `thieleuniversal/` | 7 | Universal Turing Machine proofs |
| `modular_proofs/` | 7 | Modular encoding and simulation proofs |
| `physics/` | 5 | Physics models (Landauer bridge, wave/discrete) |
| `bridge/` | 6 | Physics embeddings (BoxWorld, Quantum, Entropy) |
| `nofi/` | 5 | No-Free-Insight abstraction |
| `catnet/` | 1 | Categorical network proofs |
| `isomorphism/` | 1 | Universe isomorphism |
| `sandboxes/` | 3 | Experimental proofs |
| `self_reference/` | 1 | Self-reference exploration |
| `spacetime/` | 1 | Spacetime proofs |
| `spacetime_projection/` | 1 | Spacetime projection |
| `thiele_manifold/` | 4 | Thiele manifold physics |
| `shor_primitives/` | 3 | Shor algorithm primitives |
| `project_cerberus/` | 1 | Cerberus project |
| `test_vscoq/` | 1 | VSCoq tests |

## Key Theorems

### Core Results (in `kernel/`)

1. **`local_box_CHSH_bound`** (MinorConstraints.v)
   - The classical bound 2 proven for factorizable correlations (μ=0)
   - Key insight: Minor constraints ⟺ Factorizable ⟺ Classical bound
   - Proven: μ=0 (factorizable operations only) → CHSH ≤ 2 (classical bound)
   - Note: Quantum bound (2√2) requires μ>0 operations (LJOIN, REVEAL, LASSERT)

2. **`mu_is_initial_monotone`** (MuInitiality.v)
   - μ is THE unique canonical cost functional (Initiality Theorem)
   - Any instruction-consistent monotone cost starting at 0 must equal μ

3. **`quantum_foundations_complete`** (QuantumEquivalence.v)
   - QM = total μ=0 tier (derived, not assumed)
   - Hierarchy: Classical ⊂ Quantum ⊂ Supra-quantum = cost tiers

4. **`non_circularity_verified`** (NonCircularityAudit.v)
   - Defense against "smuggled quantum structure" attack
   - 2√2 appears only as derived optimum, not encoded constraint

### Verification Chain

```
┌─────────────────────────────────────────────────────────────┐
│                    VERIFICATION CHAIN                       │
├─────────────────────────────────────────────────────────────┤
│  Coq VM (VMState, VMStep)                                   │
│      ↕ PythonBisimulation.v                                │
│  Python VM (thielecpu/vm.py)                               │
│      ↕ HardwareBisimulation.v                              │
│  Hardware (thielecpu/hardware/*.v)                         │
└─────────────────────────────────────────────────────────────┘
```

## Validation

```bash
# Run inquisitor to check for axioms/admits
python scripts/inquisitor.py --strict --coq-root coq

# Expected result: PASS (zero axioms, zero admits)
```

## Each Directory Has a README

See the `README.md` in each subdirectory for details on its contents.
