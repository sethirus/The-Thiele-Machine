# Coq Proofs for the Thiele Machine

This directory contains the active Coq proof tree for the Thiele Machine.

**Status:** ✅ Active proof tree builds in the CI `coq-gate` | ✅ **ZERO admitted proofs** in active code | ✅ **ZERO project-local axioms** in the active audited tree | ✅ proof-hygiene checks pass

## Build

From the repository root, with the vendored libraries on `COQPATH`:

```bash
export COQPATH="$PWD/vendor/bbv/src:$PWD/vendor/kami"
make -C vendor/bbv
make -C vendor/kami
make coq-gate     # regenerates coq/Makefile from _CoqProject and builds the active tree
```

`coq/_CoqProject` also maps `../minimal` to the `Minimal` namespace, so `minimal/EarnedCore.v` builds with the tree.
For a fresh source-only rebuild, see [docs/REPRODUCTION.md](../docs/REPRODUCTION.md).

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
| top-level `PhysicsConditionalClosure.v` | VM accounting results and a conditional Tsirelson theorem from a full PSD completion (`A_QM` is a section premise) |
| top-level `ThieleMachineComplete.v` | One-file copy of the kernel's 51 instructions and their definitions; `tests/test_standalone_kernel_agreement.py` checks it against the kernel text |
| top-level `Extraction.v` | Extraction of the kernel step to OCaml (`build/thiele_core.ml`, the extracted runner) |
| top-level `AssumptionsProbe.v`, `AssumptionsProbeAll.v` | `Print Assumptions` probes; `AssumptionsProbeAll.v` is generated and feeds the assumption receipt |
| `kernel/` | Core kernel proofs (VMState, VMStep, NoFreeInsight, μ-accounting, necessity/minimality, CHSH / bounds work) |
| `kami_hw/` | The CPU and loader in Kami, their extraction, and refinement against the kernel |
| `thielemachine/` | A small executable machine model with receipts, and its process category |
| `physics/` | Physics-model formalizations and embeddings |
| `nofi/` | No-Free-Insight abstraction layer |
| `thiele_manifold/` | Manifold / bridge work |
| `tests/` | Coq-side test files (7 files) |
| `test_fixtures/` | `VacuitySmoke.v`, the fixture the kernel-conversion vacuity gate checks itself against |
| `thermodynamic/` | Thermodynamic bridge proofs |
| `spacetime/` | Spacetime proofs (1 file) |
| `self_reference/` | Self-reference and trust-transfer models (9 files) |

See the `README.md` in each subdirectory for details on its contents.
