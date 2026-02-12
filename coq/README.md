# Coq Proofs for the Thiele Machine

This directory contains **285 Coq proof files (~78,500 lines)** organized into logical modules.

**Status:** ✅ All 285 files compile cleanly | ✅ **ZERO admitted proofs** | ✅ **ZERO axioms in active code** | ✅ [Full Audit Report](../INQUISITOR_REPORT.md)

## Build

```bash
# From repository root:
make              # Build all 285 Coq proofs

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
| `kernel/` | 97 | Core kernel proofs (Structural constraints, optimization bounds, bisimulation) |
| `kernel_toe/` | 6 | Theory of Everything cone (no-go theorems) |
| `thielemachine/` | 98 | Main Thiele Machine proofs (Bell, verification, deliverables) |
| `thieleuniversal/` | 7 | Universal Turing Machine proofs |
| `modular_proofs/` | 9 | Modular encoding and simulation proofs |
| `physics/` | 5 | Physics models (Landauer bridge, wave/discrete) |
| `bridge/` | 7 | Embeddings (BoxWorld, Linear Algebra, Entropy) |
| `nofi/` | 5 | No-Free-Insight abstraction |
| `catnet/` | 1 | Categorical network proofs |
| `isomorphism/` | 1 | Universe isomorphism |
| `sandboxes/` | 3 | Experimental proofs |
| `self_reference/` | 1 | Self-reference exploration |
| `spacetime/` | 1 | Spacetime proofs |
| `spacetime_projection/` | 1 | Spacetime projection |
| `thiele_manifold/` | 4 | Thiele manifold physics |
| `shor_primitives/` | 4 | Shor algorithm primitives |
| `project_cerberus/` | 1 | Cerberus project |
| `test_vscoq/` | 1 | VSCoq tests |
| `physics_exploration/` | 6 | Physics exploration proofs |
| `quantum_derivation/` | 9 | Quantum derivation proofs |
| `theory/` | 13 | Theory proofs |
| `thermodynamic/` | 2 | Thermodynamic proofs |
| `tests/` | 2 | Coq test files |

## Key Theorems

### Core Results (in `kernel/`)

1. **`local_box_CHSH_bound`** (MinorConstraints.v)
   - The factorizable bound 2 proven for correlations with no structural cost (μ=0)
   - Key insight: Minor constraints ⟺ Factorizable ⟺ Unitary bound
   - Proven: μ=0 (factorizable operations only) → CHSH ≤ 2
   - Note: Algebraic bound (2√2) requires μ>0 operations (LJOIN, REVEAL, LASSERT)

2. **`mu_is_initial_monotone`** (MuInitiality.v)
   - μ is THE unique canonical cost functional (Initiality Theorem)
   - Any instruction-consistent monotone cost starting at 0 must equal μ

3. **`quantum_foundations_complete`** (QuantumEquivalence.v)
   - Coherent Correlations = cost-free execution tier (derived, not assumed)
   - Hierarchy: Factorizable ⊂ Coherent ⊂ Structural = cost tiers

4. **`non_circularity_verified`** (NonCircularityAudit.v)
   - Defense against "smuggled constraint" attack
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

## Proof Audit (2026-02-06)

**Audit Result: ✅ PASS**

```bash
# Run inquisitor to check for axioms/admits
python scripts/inquisitor.py --strict --coq-root coq
```

**Findings:**
- ✅ **ZERO admitted proofs** in active codebase (all proofs complete)
- ✅ **ZERO custom axioms** in production code (kernel/, nofi/, thielemachine/)
- ✅ All 78 axioms confined to `archive/` (exploratory/historical code)
- ✅ Active code uses only standard mathematical axioms:
  - `FunctionalExtensionality` (standard Coq library)
  - `ClassicalDedekindReals.sig_forall_dec` (classical decidability for reals)
- ✅ Clean compilation of all 285 files
- 2 HIGH findings (intentional): `reversible_info_cost = 0` (mathematically required)

**Key Theorem Dependencies:**
- `local_box_CHSH_bound`: Standard axioms only (functional extensionality, classical decidability)
- Tsirelson bounds: Derived from algebraic coherence, no custom axioms
- μ-cost theorems: Complete proofs, no admits

See [Full Audit Report](../INQUISITOR_REPORT.md) for detailed analysis.

## Each Directory Has a README

See the `README.md` in each subdirectory for details on its contents.
