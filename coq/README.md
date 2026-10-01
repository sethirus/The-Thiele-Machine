# Coq Proofs for the Thiele Machine

This directory contains the active Coq proof tree for the Thiele Machine.

**Status:** ✅ Active proof tree builds in the CI `coq-gate` | ✅ **ZERO admitted proofs** in active code | ✅ **ZERO project-local axioms** in the active audited tree | ✅ proof-hygiene checks pass

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

The table names the principal proof surfaces; each directory README names its principal files.

| Directory | Description |
|-----------|-------------|
| top-level `NecessityOfMuLedger.v` | Strict classical projection cannot recover μ/certification receipts |
| top-level `ReceiptTheorem.v` | The twelve-line lift of the projection-collision into the impossibility theorem |
| top-level `VerifierModel.v` + `VerifierImpossibility.v` | Verifier records (`BareVerifier`, soundness, completeness, cheapness) and the bare-setting impossibility for μ-sensitive claims |
| top-level `VerifierEscape_{Substrate,Hardness,Interaction}.v` | Three structurally distinct escapes from the impossibility; the hardness escape (`commitment_contract_verifier`) is conditional on the commitment-bit contract `CommitmentBitContract` |
| top-level `VerifierExhaustiveness.v` | Factorisation impossibility: no sound complete verifier on the μ-sensitive claim is a function of the classical projection alone |
| top-level `MuCodingTheorem.v` | Two-sided cert-payload bound for single-instruction certifiers of `vm_mu = k` from the clean start (`mu_eq_k_claim`), under the pricing policy `cert_priced_eq` |
| top-level `IntrinsicLevelHierarchy.v` | State-side level hierarchy ("every certifying trace requires ≥ k cert-events"), companion to the trace-side `MuHierarchyTheorem` in `kernel/mu_calculus/` |
| top-level `MuDirectSum.v` | Direct-sum theorem under cert-disjoint independence + amortisation counterexample under weaker independence |
| `kernel/` | Core kernel proofs (VMState, VMStep, NoFreeInsight, μ-accounting, necessity/minimality, CHSH / bounds work) |
| `kami_hw/` | Kami hardware spec, extraction, and refinement-facing proofs |
| `thielemachine/` | Main Thiele Machine proofs and verification layers |
| `physics/` | Physics-model formalizations and embeddings |
| `nofi/` | No-Free-Insight abstraction layer |
| `thiele_manifold/` | Manifold / bridge work |
| `tests/` | Coq-side test files (7 files) |
| `test_fixtures/` | `VacuitySmoke.v`, the fixture the kernel-conversion vacuity gate checks itself against |
| `thermodynamic/` | Thermodynamic bridge proofs |
| `spacetime/` | Spacetime proofs (1 file) |
| `self_reference/` | Self-reference exploration (9 files) |

See the `README.md` in each subdirectory for details on its contents.
