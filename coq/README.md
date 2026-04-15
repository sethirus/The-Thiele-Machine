# Coq Proofs for the Thiele Machine

This directory contains the active Coq proof tree for the Thiele Machine.

Documentation note: this README is an overview of the proof tree, not the authoritative claim-status document. For current claim boundaries and audit results, see `../INQUISITOR_REPORT.md`.

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
```

## Directory Structure

| Directory | Description |
|-----------|-------------|
| `kernel/` | Core kernel proofs (VMState, VMStep, NoFreeInsight, μ-accounting, CHSH / bounds work) |
| `kami_hw/` | Kami hardware spec, extraction, and refinement-facing proofs |
| `thielemachine/` | Main Thiele Machine proofs and verification layers |
| `physics/` | Physics-model formalizations and embeddings |
| `nofi/` | No-Free-Insight abstraction layer |
| `thiele_manifold/` | Manifold / bridge work |
| `tests/` | Coq-side test files |
| `thermodynamic/` | Thermodynamic bridge proofs |
| `spacetime/` | Spacetime proofs (1 file) |
| `self_reference/` | Self-reference exploration (9 files) |

See the `README.md` in each subdirectory for details on its contents.
