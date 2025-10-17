# Thiele Machine Minimal Artifact Inventory

## 1. Executive Summary (BLUF)
- **Goal:** deliver a branch containing only the reproducible Bell-thesis artifact, its proof obligations, and the receipts required for external audit.
- **Status:** every directory listed below was manually inspected under Linux after installing Coq 8.18.0 and the editable Python stack (`pip install -e .`). Canonical orchestrators (`demonstrate_isomorphism.py`, `attempt.py`) and verification tooling (`scripts/challenge.py`, `scripts/verify_truth.sh`, `verify_bell.sh`) all execute successfully in this environment.
- **Next actions:** remove the assets flagged in §4, trim optional material in §5, and rerun the validation checklist in §6 before declaring the branch ready for publication.

## 2. Hardened Environment Baseline
| Step | Command(s) executed | Outcome |
| --- | --- | --- |
| System prep | `sudo apt-get update`, `sudo apt-get install -y coq` | Installs Coq 8.18.0 required by Act V/VI proof replay. |
| Python toolchain | `pip install -e .` | Provides full scientific stack (NumPy/SciPy, Astropy+Healpy, python-sat extras, Z3, Cryptography, Playwright optional extras). |
| Canonical runs | `python demonstrate_isomorphism.py`, `python attempt.py` | Both scripts complete the six-act thesis narrative, regenerate receipts, and call the Coq proof harness without modification. |
| Verification harness | `python scripts/challenge.py verify receipts`, `./scripts/verify_truth.sh examples/tsirelson_step_receipts.json`, `./verify_bell.sh` | μ-bit verification and Coq replay succeed; transcripts captured under `audit_logs/`. |
| Optional demos | Representative runs recorded in `audit_logs/` (e.g., `demo_structure.log`, `demo_rsa.log`, `demo_tensorflow.log`). | Document current behaviour prior to removal/triage. |

## 3. Essential Retained Set (Keep)
| Path | Role in minimal artifact | Notes |
| --- | --- | --- |
| `demonstrate_isomorphism.py`, `attempt.py` | Canonical orchestrators referenced in README; regenerate ledger and transcripts. | Keep unchanged; README must explain dependency surface after pruning. |
| `BELL_INEQUALITY_VERIFIED_RESULTS.md`, `README.md`, `docs/demonstrate_isomorphism_report.md` | Primary documentation and ledger narrative. | Trim README to match slim layout once pruning complete. |
| `thielecpu/` (core modules), `tools/receipts.py`, `kernel_public.key` | Virtual machine with AST-sandboxed PYEXEC, compression-based μ-bit accounting, and Ed25519-signed receipts. | Drop unused subpackages only after confirming orchestrators/tests do not import them; keep the public verification key while ignoring the secret. |
| `scripts/challenge.py`, `scripts/verify_truth.sh`, `scripts/verify_thiele_machine.py`, `scripts/verify_receipt.py` | Verification automation invoked by canonical run and audits. | Maintain Linux-compatible shebangs/path handling. |
| `coq/thielemachine/coqproofs/`, `_CoqProject`, `coq/Makefile` | Mechanised containment proofs for Act V/VI. | Remove unrelated Coq sandboxes while ensuring scripts still build. |
| `artifacts/` (Act VI receipts, `MANIFEST.sha256`), `receipts/tsirelson_step_receipts.json` | Integrity evidence and μ-bit ledger inputs. | Regenerate manifest after pruning. |
| `data/planck_sample.fits`, `data/generate_planck_sample.py`, `data/README.md` | Deterministic cosmological input and provenance. | Keep minimal sample; document path if relocating. |
| Governance files (`LICENSE`, `NOTICE`, `CITATION.cff`, `AGENTS.md`) | Legal and contributor guidance. | Update AGENTS instructions if workflow changes. |

## 4. Remove Entirely (Drop)
| Path / Pattern | Rationale |
| --- | --- |
| `demos/`, `apps/`, `catnet/`, `models/`, `demos/*` receipts (`demo_output/`, `structure_discovery_output/`, `rsa_demo_output/`, `shape_of_truth_out/`) | Optional showcase material; not part of minimal Bell artifact and drives dependency bloat (Playwright, TensorFlow, etc.). |
| `experiments/`, `ablation_*`, `bell_locality_analysis/`, `structure_discovery_receipt.json`, `chsh_mu_bits_law_receipt.json` | Secondary studies and ablation outputs; preserve only canonical Tsirelson receipts. |
| `documents/`, `archive/`, `COMPUTATIONAL_PRICED_SIGHT_*`, `DECLARATION_OF_INDEPENDENCE.md`, marketing one-pagers | Narrative collateral; remove to keep focus on reproducible science. |
| Release packaging (`The-Thiele-Machine-v1.0.2.tar.gz.asc`, old tarballs), `security_log.json` | Historical release artefacts; recompute manifests after pruning. |
| Node/TypeSpec stack (`package.json`, `package-lock.json`, `node_modules/`) | Legacy tooling no longer required once demos are removed. |
| Legacy paradox/CatNet assets (`paradox*`, `thiele_native_factor.py`, `temp_rsa_main.smt2`) | Unused by canonical run; delete alongside demos. |

## 5. Retain Conditionally / Trim
| Path | Required action before release |
| --- | --- |
| `attempt.py` | Keep only if README continues to advertise extended thesis orchestration; otherwise remove and update docs accordingly. |
| `scripts/` (misc.) | Audit individual scripts (release automation, bug hunter). Keep only those referenced in documentation or audits; document static-analysis exceptions in `docs/static_analysis_triage.md`. |
| `tests/` | Reduce to smoke tests covering `thielecpu`, receipts, and verification harness. Remove demo-specific suites once directories are deleted. |
| `coq/` non-core modules | Delete unused sandboxes (`p_equals_np_thiele`, `project_cerberus`, tmp files) after confirming no scripts reference them. |
| `artifacts/` ancillary files | After pruning, regenerate `MANIFEST.sha256` and remove checksums for deleted entries. |
| `data/` extras (e.g., Base64 mirrors) | Keep a single canonical FITS file; drop redundant encodings once README references remaining asset. |
| `spec/` | Retain `receipt.schema.json` if leveraged by verifiers; remove other spec drafts unless cited. |

## 6. Post-Curation Validation Checklist
Execute the following commands in a clean clone after pruning to confirm no regressions:
1. `pip install -e .`
2. `python demonstrate_isomorphism.py --act-vi offline --cmb-file data/planck_sample.fits`
3. `python scripts/challenge.py verify receipts`
4. `./scripts/verify_truth.sh receipts/tsirelson_step_receipts.json`
5. (Optional) `python attempt.py` if the script remains in scope.
6. `sha256sum --check artifacts/MANIFEST.sha256`
7. `pytest tests` (limited smoke suite) or targeted `python -m pytest tests/test_core_*` once trimmed.

Record the stdout/stderr for each run into `audit_logs/` (already present) to maintain an auditable trail for reviewers.

## 7. Evidence & References
- Execution transcripts captured in `audit_logs/` (e.g., `demonstrate_isomorphism.log`, `verify_truth.log`, `attempt.log`).
- Dependency provenance documented via editable install; see `pyproject.toml` optional extras for demos if any are retained temporarily.
- Static-analysis findings and mitigations tracked in `docs/static_analysis_triage.md`.

This curated roadmap keeps the Thiele Machine artifact understandable at a glance while anchoring every keep/remove decision to direct inspection and successful runs in the hardened Linux environment.
