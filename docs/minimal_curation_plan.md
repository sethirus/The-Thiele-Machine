# Thiele Machine Minimal Artifact Inventory

## 1. Executive Summary (BLUF)
- **Goal:** deliver a branch containing the reproducible Thiele Machine thesis artifact—Acts I–VI orchestrators, the `thielecpu/` implementation, Coq proofs, and signed receipts—with the Bell verification preserved as the Act VI capstone rather than the sole focus.
- **Status:** every directory listed below was manually inspected under Linux after installing Coq 8.18.0 and the editable Python stack (`pip install -e .`). Canonical orchestrators (`demonstrate_isomorphism.py`, `attempt.py`) drive the full Thiele Machine pipeline, regenerating μ-bit ledgers and transcripts, while the verification tooling (`scripts/challenge.py`, `scripts/verify_truth.sh`, `verify_bell.sh`) confirms both the virtual machine behaviour and the Bell finale.
- **Next actions:** reorganize the assets flagged in §4, trim optional material in §5, and rerun the validation checklist in §6 before declaring the branch ready for publication. Nonessential analytics and narrative collateral should be removed so the repository only ships documentation needed to run and audit the core artifact.

## 2. Hardened Environment Baseline
| Step | Command(s) executed | Outcome |
| --- | --- | --- |
| System prep | `sudo apt-get update`, `sudo apt-get install -y coq` | Installs Coq 8.18.0 required by Act V/VI proof replay. |
| Python toolchain | `pip install -e .` | Provides full scientific stack (NumPy/SciPy, Astropy+Healpy, python-sat extras, Z3, Cryptography, Playwright optional extras). |
| Canonical runs | `python demonstrate_isomorphism.py`, `python attempt.py` | Both scripts complete the six-act thesis narrative, regenerate receipts, and call the Coq proof harness without modification. |
| Verification harness | `python scripts/challenge.py verify receipts`, `./scripts/verify_truth.sh examples/tsirelson_step_receipts.json`, `./verify_bell.sh` | μ-bit verification, Thiele CPU receipts, and the Bell Act VI replay all succeed; transcripts captured under `audit_logs/`. |
| Optional demos | Representative runs recorded in `audit_logs/` (e.g., `demo_structure.log`, `demo_rsa.log`, `demo_tensorflow.log`). | Document current behaviour prior to removal/triage. |

## 3. Essential Retained Set (Keep)
| Path | Role in minimal artifact | Notes |
| --- | --- | --- |
| `demonstrate_isomorphism.py`, `attempt.py` | Canonical orchestrators referenced in README; regenerate ledger and transcripts. | Keep unchanged; README must explain dependency surface after pruning. |
| `BELL_INEQUALITY_VERIFIED_RESULTS.md`, `README.md`, `docs/demonstrate_isomorphism_report.md` | Thesis documentation: Acts I–V cover the Thiele Machine construction; Act VI records the Bell inequality audit. | Trim README to match slim layout once pruning complete. |
| `thielecpu/` (core modules), `tools/receipts.py`, `kernel_public.key` | Virtual machine with AST-sandboxed PYEXEC, compression-based μ-bit accounting, and Ed25519-signed receipts. | Drop unused subpackages only after confirming orchestrators/tests do not import them; keep the public verification key while ignoring the secret. |
| `scripts/challenge.py`, `scripts/verify_truth.sh`, `scripts/verify_thiele_machine.py`, `scripts/verify_receipt.py` | Verification automation invoked by canonical run and audits. | Maintain Linux-compatible shebangs/path handling. |
| `coq/thielemachine/coqproofs/`, `_CoqProject`, `coq/Makefile` | Mechanised containment proofs for Act V/VI. | Remove unrelated Coq sandboxes while ensuring scripts still build. |
| `artifacts/` (Act VI receipts, `MANIFEST.sha256`), `receipts/tsirelson_step_receipts.json` | Integrity evidence and μ-bit ledger inputs. | Regenerate manifest after pruning. |
| `data/planck_sample.fits`, `data/generate_planck_sample.py`, `data/README.md` | Deterministic cosmological input and provenance. | Keep minimal sample; document path if relocating. |
| Governance files (`LICENSE`, `NOTICE`, `CITATION.cff`, `AGENTS.md`) | Legal and contributor guidance. | Update AGENTS instructions if workflow changes. |

The Bell receipts remain in scope because they certify the Act VI physics claim, but the curated set is centred on the Thiele Machine itself: the `thielecpu/` virtual machine, the orchestrators that drive Acts I–V, and the mechanised containment proofs. Act VI should be treated as the finale that validates the pipeline rather than the justification for retaining the rest of the repository.

## 4. Reorganize Outputs and Redundant Artifacts

### 4.0 Remove Only Regenerable Build Products
| Path / Pattern | Rationale |
| --- | --- |
| `demo_output/`, `structure_discovery_output/`, `graph_demo_output/`, archived `rsa_demo_output/`, `shape_of_truth_out/` | Bulky, reproducible logs and receipts; capture hashes in `audit_logs/` then delete or relocate the outputs. |
| `experiments/` cache files (`*.npz`, `*.pkl`, `*.csv`) without provenance | Delete intermediate blobs to reduce footprint while keeping the code and notebooks. |
| Release packaging duplicates (unpacked tarballs, extra signatures) | Retain one signed release under `archive/releases/` and remove remaining duplicates. |
| Generated dependency trees (`node_modules/`, `.mypy_cache/`, `__pycache__/`) | Delete transient caches after ensuring instructions exist to rebuild them. |
| Build scratch files (`security_log.json`, stray `.log`/`.tmp` without retention value) | Remove once the ability to regenerate them is documented. |

### 4.1 Relocate to Archive (Do Not Delete)
| Path / Pattern | Destination | Rationale |
| --- | --- | --- |
| `demos/`, `apps/`, `catnet/`, `models/` | `archive/showcase/{demos,apps,catnet,models}/` | Keep optional showcases accessible without expanding the minimal runtime surface. |
| `experiments/` notebooks, `ablation_*` analyses, `bell_locality_analysis/` | `archive/research/` | Maintain exploratory research artifacts in a predictable location. |
| `structure_discovery_receipt.json`, `chsh_mu_bits_law_receipt.json`, other non-Act-VI receipts | `archive/receipts/` | Keep historical receipts while limiting the canonical ledger to Act VI. |
| Node/TypeSpec manifests (`package.json`, `package-lock.json`, TypeSpec specs) | `archive/tooling/node/` | Retain tooling metadata even after removing generated dependencies. |
| Legacy paradox/CatNet source (`paradox.v`, `paradox_model.py`, `paradox_module_*.smt2`, `thiele_native_factor.py`, `temp_rsa_main.smt2`) | `archive/research/paradox/` | Document theoretical explorations without shipping them in the minimal artifact. |

## 5. Retain Conditionally / Trim
| Path | Required action before release |
| --- | --- |
| `attempt.py` | Keep in the primary tree but clarify in README whether it is optional; relocate to `archive/orchestrators/` only if the documentation no longer references it. |
| `scripts/` (misc.) | Keep verification essentials in `scripts/`; move lesser-used utilities to `archive/scripts/` with a short index under version control. |
| `tests/` | Maintain core smoke tests in `tests/` and relocate demo-specific suites to `archive/tests/` so they remain runnable without bloating CI. |
| `coq/` non-core modules | Move unused sandboxes (`p_equals_np_thiele`, `project_cerberus`, tmp files) under `archive/coq/` and document their status. |
| `artifacts/` ancillary files | After relocating historical receipts to `archive/receipts/`, regenerate `MANIFEST.sha256` to describe the remaining canonical set. |
| `data/` extras (e.g., Base64 mirrors) | Keep a single canonical FITS file in `data/`; relocate auxiliary encodings to `archive/data/` with provenance notes. |
| `spec/` | Retain `receipt.schema.json` in-tree; move draft specifications into `archive/spec/` and cross-link them from the README if relevant. |

## 6. Post-Curation Validation Checklist
Execute the following commands in a clean clone after reorganizing to confirm no regressions:
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


This curated roadmap keeps the Thiele Machine artifact understandable at a glance while anchoring every keep/relocate/remove decision to direct inspection and successful runs in the hardened Linux environment.
