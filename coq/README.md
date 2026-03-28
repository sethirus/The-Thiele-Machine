# Coq Proofs for the Thiele Machine

This directory contains the active Coq proof tree for the Thiele Machine.

Documentation note: this README is an overview of the proof tree, not the authoritative claim-status document. For current claim boundaries and audit results, see `../INQUISITOR_REPORT.md` and `../CATEGORICAL_EXTENSION_PLAN.md`.

**Status:** ✅ Active proof tree compiles cleanly | ✅ **ZERO admitted proofs** in active code | ✅ **ZERO project-local axioms** in the active audited tree | ✅ [Full Audit Report](../INQUISITOR_REPORT.md)

## Build

```bash
# From repository root:
make              # Build the active Coq proof tree

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

| Directory | Description |
|-----------|-------------|
| `kernel/` | Core kernel proofs (VMState, VMStep, NoFreeInsight, μ-accounting, CHSH / bounds work) |
| `kami_hw/` | Kami hardware spec, extraction, and refinement-facing proofs |
| `thielemachine/` | Main Thiele Machine proofs and verification layers |
| `thieleuniversal/` | Universal Turing Machine simulation proofs |
| `modular_proofs/` | Modular encoding and simulation proofs |
| `physics/` | Physics-model formalizations and embeddings |
| `nofi/` | No-Free-Insight abstraction layer |
| `thiele_manifold/` | Manifold / bridge work |
| `tests/` | Coq-side test files |
| `thermodynamic/` | Thermodynamic bridge proofs |
| `spacetime/` | 1 | Spacetime proofs |
| `self_reference/` | 1 | Self-reference exploration |

**Archived** (in `archive/coq_unused/`): `bridge/`, `catnet/`, `isomorphism/`, `kernel_toe/`,
`physics_exploration/`, `project_cerberus/`, `quantum_derivation/`, `self_reference/`,
`shor_primitives/`, `spacetime_projection/`, `test_vscoq/`, `theory/`.
The `thiele_prime/` machine line was merged into `kernel/PrimeAxiom.v` (the prime axiom
now holds for the full 40-opcode kernel VM).

## Key Theorems

### Core Results (in `kernel/`)

1. **`local_box_CHSH_bound`** (MinorConstraints.v)
   - The factorizable bound 2 proven for correlations with no structural cost (μ=0)
   - Key insight: Minor constraints ⟺ Factorizable ⟺ Unitary bound
   - Proven: factorizable correlations imply CHSH ≤ 2
   - Boundary: the separate trace-level theorem for arbitrary μ=0 runs is only the algebraic bound `|S| <= 4`
   - Note: stronger Tsirelson-related results live elsewhere in the proof tree and should be distinguished from the executable CHSH experiment path

2. **`mu_is_initial_monotone`** (MuInitiality.v)
   - μ is THE unique canonical cost functional (Initiality Theorem)
   - Any instruction-consistent monotone cost starting at 0 must equal μ

3. **Quantum-related bridge files**
   - The proof tree contains multiple quantum-related derivation and bridge files
   - These are formal proof artifacts inside the repository, not by themselves evidence that the executable machine is a physical quantum device

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

## Proof Audit

The active proof tree is audited with the inquisitor:

```bash
# From repository root
python scripts/inquisitor.py
```

Current status is reflected in [Full Audit Report](../INQUISITOR_REPORT.md). The checked-in report is the authoritative snapshot for exact counts and findings.

## Each Directory Has a README

See the `README.md` in each subdirectory for details on its contents.
