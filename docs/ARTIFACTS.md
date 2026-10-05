# Generated artifacts and evidence

The repository distinguishes source, reproducible evidence, and disposable build output. A committed artifact is maintained only when this document names its generator and consumer.

## Retained evidence

The following records are generated from the checked source and are retained because CI, release review, or reproducibility checks consume them:

| Surface | Generator | Consumer or purpose |
| --- | --- | --- |
| `INQUISITOR_REPORT.md` | `python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md` | Proof-audit result and CI upload |
| `artifacts/print_assumptions_all_proofs.*` | `scripts/check_assumption_receipt.py` and `scripts/generate_assumption_receipt.sh` | Assumption receipt and diff gate |
| `artifacts/proof_dependency_*.json` and `.mmd` | `scripts/generate_proof_dependency_dag.py` | Proof connectivity and audit visualization |
| `artifacts/proof_gate/` | `scripts/proof_gate_reproducible.sh` | Reproducible proof-gate metadata |
| `artifacts/vacuity_audit.json` | `make vacuity-audit` | Kernel-conversion vacuity verdicts for the targets in `scripts/vacuity_targets.json` |
| `monograph/*.pdf` and generated plaintext | `monograph/build_monograph.sh` | Publication outputs and text review |

The exact command and current source inputs for each surface belong in the generating script or its workflow step. A generated file must not be edited by hand; regenerate it and review the resulting diff. The receipts, the dependency graph and the proof-gate records are regenerated on Linux, where CI builds the proofs.

## Disposable output

`build/` (except the probe builder in `build/probe/`), Coq object files (`*.vo`, `*.glob`, `*.vok`, `*.vos`, and `*.aux`), and temporary probe logs are build products. They may be created locally or in CI and are removed by the clean targets or the workflow checkout. They are not a second source tree.

## Scope of retained records

Only generated records named in the table above belong to the maintained evidence surface. Working-session snapshots, duplicated probes, source patches, compiled objects, and intermediate logs are excluded from the repository's assurance record. Scope is defined by `docs/ASSURANCE.md` and `docs/REPRODUCTION.md`, together with the active generators and their workflow consumers.
