# Coq Proofs for the Thiele Machine

This directory contains **206 Coq proof files** organized into logical modules.

## Build

```bash
# From repository root:
./scripts/build_coq.sh        # Build all 206 proofs
./scripts/build_coq.sh --clean  # Clean and rebuild

# Or manually:
cd coq
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq -j$(nproc)
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

1. **`tsirelson_from_pure_accounting`** (TsirelsonUniqueness.v)
   - The Tsirelson bound 2√2 emerges from pure μ-accounting
   - Combines achievability (lower bound) and constraints (upper bound)

2. **`quantum_foundations_complete`** (QuantumEquivalence.v)
   - QM = μ=0 tier (derived, not assumed)
   - Hierarchy: Classical ⊂ Quantum ⊂ Supra-quantum = cost tiers

3. **`thiele_machine_is_complete`** (MasterSummary.v)
   - Master theorem combining all key results
   - Verification chain: Coq ↔ Python ↔ Hardware

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
