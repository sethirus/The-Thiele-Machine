# Generated artifacts and evidence

The repository distinguishes source, reproducible evidence, and disposable build output. A committed artifact is current only when this document names its generator and consumer.

## Retained evidence

The following records are generated from the checked source and are retained because CI, release review, or reproducibility checks consume them:

| Surface | Generator | Consumer or purpose |
| --- | --- | --- |
| Generated proof-audit output | `python3 scripts/inquisitor.py` | Proof-audit result and CI upload |
| `artifacts/print_assumptions_all_proofs.*` | `scripts/check_assumption_receipt.py` and `scripts/generate_assumption_receipt.sh` | Assumption receipt and diff gate |
| `artifacts/proof_dependency_*.json` and `.mmd` | `scripts/generate_proof_dependency_dag.py` | Proof connectivity and audit visualization |
| `artifacts/proof_gate/` | `scripts/proof_gate_reproducible.sh` | Reproducible proof-gate metadata |
| `artifacts/final_claim_audit/` | `scripts/repo_audit_trail.sh` (with claim JSONs from `scripts/generate_master_summary_artifacts.py`) | Claim-to-evidence inventory and source-status snapshot |
| `artifacts/rtl_pipeline_manifest.json` | `scripts/generate_rtl_pipeline_manifest.py` | Generated RTL provenance check |
| `artifacts/rtl_text_transform_audit.json` | `scripts/audit_rtl_text_transforms.py` | RTL transformation integrity check |
| `artifacts/synthesis_gate/` | synthesis gate scripts | Repeated synthesis comparison |
| `monograph/*.pdf` and generated plaintext | `monograph/build_monograph.sh` | Publication outputs and text review |

The exact command and current source inputs for each surface belong in the generating script or its workflow step. A generated file must not be edited by hand; regenerate it and review the resulting diff.

## Disposable output

`build/`, Coq object files (`*.vo`, `*.glob`, `*.vok`, `*.vos`, and `*.aux`), temporary probe logs, simulator output, and FPGA intermediate files are build products. They may be created locally or in CI and are removed by the clean targets or the workflow checkout. They are not a second source tree.

## Scope of retained records

Only generated records named in the table above belong to the maintained evidence surface. Working-session snapshots, duplicated probes, source patches, compiled objects, and intermediate logs are excluded from the repository's assurance record. Current scope is defined by `docs/ASSURANCE.md`, `docs/REPRODUCTION.md`, and `docs/VM_CONTRACTS.md`, together with the active generators and their workflow consumers.
