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
| top-level `NecessityOfMuLedger.v` | Strict classical projection cannot recover μ/certification receipts |
| top-level `ReceiptTheorem.v` | The twelve-line lift of the projection-collision into the impossibility theorem |
| top-level `VerifierModel.v` + `VerifierImpossibility.v` | Verifier records (`BareVerifier`, soundness, completeness, cheapness) and the bare-setting impossibility for μ-sensitive claims |
| top-level `VerifierEscape_{Substrate,Hardness,Interaction}.v` | Three structurally distinct escapes — each a closed Coq theorem with a concrete verifier — that clear the impossibility |
| top-level `VerifierExhaustiveness.v` | Factorisation impossibility: no sound complete verifier on the μ-sensitive claim is a function of the classical projection alone |
| top-level `MuCodingTheorem.v` | Tight two-sided cert-payload bound (Chaitin-style) for the canonical `mu_eq_k_claim` family |
| top-level `IntrinsicLevelHierarchy.v` | State-side level hierarchy ("every certifying trace requires ≥ k cert-events"), companion to the trace-side `MuHierarchyTheorem` in `kernel/mu_calculus/` |
| top-level `MuDirectSum.v` | Direct-sum theorem under cert-disjoint independence + amortisation counterexample under weaker independence |
| `kernel/` | Core kernel proofs (VMState, VMStep, NoFreeInsight, μ-accounting, necessity/minimality, CHSH / bounds work) |
| `kami_hw/` | Kami hardware spec, extraction, and refinement-facing proofs |
| `thielemachine/` | Main Thiele Machine proofs and verification layers |
| `physics/` | Physics-model formalizations and embeddings |
| `nofi/` | No-Free-Insight abstraction layer |
| `thiele_manifold/` | Manifold / bridge work |
| `tests/` | Coq-side test files (includes `VacuitySmoke.v`, the fixture the kernel-conversion vacuity gate checks itself against) |
| `thermodynamic/` | Thermodynamic bridge proofs |
| `spacetime/` | Spacetime proofs (1 file) |
| `self_reference/` | Self-reference exploration (9 files) |

See the `README.md` in each subdirectory for details on its contents.
