# Coq Proofs for the Thiele Machine

This directory contains **272 Coq proof files (~92,858 lines)** organized into logical modules.

**Status:** ✅ All 272 files compile cleanly | ✅ **ZERO admitted proofs** | ✅ **ZERO axioms in active code** | ✅ [Full Audit Report](../INQUISITOR_REPORT.md)

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
| `kernel/` | 127 | Core kernel proofs (VMState, VMStep, NoFreeInsight, mu-accounting, quantum bounds) |
| `kami_hw/` | 10 | Kami hardware spec and refinement proofs |
| `thielemachine/` | 85 | Main Thiele Machine proofs (Bell, verification, deliverables) |
| `thieleuniversal/` | 17 | Universal Turing Machine simulation proofs |
| `modular_proofs/` | 9 | Modular encoding and simulation proofs |
| `physics/` | 6 | Physics models (Landauer bridge, wave/discrete) |
| `nofi/` | 5 | No-Free-Insight abstraction |
| `thiele_manifold/` | 4 | Thiele manifold physics and isomorphism bridge |
| `tests/` | 3 | Coq test files |
| `thermodynamic/` | 2 | Thermodynamic bridge proofs |
| `spacetime/` | 1 | Spacetime proofs |
| `self_reference/` | 1 | Self-reference exploration |

**Archived** (in `archive/coq_unused/`): `bridge/`, `catnet/`, `isomorphism/`, `kernel_toe/`,
`physics_exploration/`, `project_cerberus/`, `quantum_derivation/`, `self_reference/`,
`shor_primitives/`, `spacetime_projection/`, `test_vscoq/`, `theory/`.
The `thiele_prime/` machine line was merged into `kernel/PrimeAxiom.v` (the prime axiom
now holds for the full 38-opcode kernel VM).

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

### Prime Axiom (kernel/PrimeAxiom.v)

The prime axiom — `vm_certified = true` implies `vm_mu > 0` — holds for the
full kernel VM. The witness is part of machine state (`vm_witness`), not
reconstructed post-hoc. See `kernel/PrimeAxiom.v` for the proof.

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

## Proof Audit (2026-03-10)

**Audit Result: ✅ PASS**

```bash
# Run inquisitor to check for axioms/admits
python scripts/inquisitor.py
```

**Findings:**
- ✅ **ZERO admitted proofs** in active codebase (all proofs complete)
- ✅ **ZERO custom axioms** in production code (kernel/, nofi/, thielemachine/)
- ✅ Active code uses only standard mathematical axioms:
  - `FunctionalExtensionality` (standard Coq library)
  - `ClassicalDedekindReals.sig_forall_dec` (classical decidability for reals)
- ✅ Clean compilation of all 272 files
- 2 HIGH findings (intentional): `reversible_info_cost = 0` (mathematically required)

**Key Theorem Dependencies:**
- `local_box_CHSH_bound`: Standard axioms only (functional extensionality, classical decidability)
- Tsirelson bounds: Derived from algebraic coherence, no custom axioms
- μ-cost theorems: Complete proofs, no admits

See [Full Audit Report](../INQUISITOR_REPORT.md) for detailed analysis.

## Each Directory Has a README

See the `README.md` in each subdirectory for details on its contents.
