# DARPA Field Assessment — Thiele Machine Hardening Sprint v1.0

## Bottom Line Up Front (BLUF)
- **Decision:** **GO (WITH OBSERVATION)** — Every gating verification step completes on a clean Ubuntu 24.04 container: the hardened verifier compiles Coq proof obligations, the canonical thesis rerun regenerates receipts, and Coq replay discharges the ledger. The only open observation is the cosmology data source falling back to the bundled Planck patch because the archived FITS sample fails integrity checks.【F:audit_logs/verify_thiele_machine.log†L1-L25】【F:audit_logs/demonstrate_isomorphism.log†L1-L23】【F:audit_logs/demonstrate_isomorphism.log†L479-L485】【F:audit_logs/verify_truth.log†L1-L1】
- **Delta from prior milestone:** The Ed25519 kernel keypair has been regenerated to the correct 32-byte format and all receipts re-signed, eliminating the prior Coq replay blocker. PYEXEC now executes through an AST whitelist and μ-bit charges derive from zlib-compressed byte length, bringing the runtime in line with the DARPA security critique.【F:thielecpu/receipts.py†L22-L197】【F:thielecpu/vm.py†L174-L247】
- **Next gate:** Restore a verified Planck FITS sample (or document a deterministic surrogate) and finish migrating legacy list-based receipts so the challenge harness runs warning-free. No additional code changes are required for the core thesis artifact.【F:audit_logs/demonstrate_isomorphism.log†L479-L485】【F:audit_logs/challenge_verify.log†L1-L5】

## Program Alignment and Decision Gates
- **BAA/TA mapping:**
  - *TA1 – Foundational Verification:* `scripts/verify_thiele_machine.py` now auto-discovers `coqc`, compiles the concrete proof bundle, and validates hardware artefacts headlessly.【F:audit_logs/verify_thiele_machine.log†L1-L25】
  - *TA2 – Operational Witness Generation:* `demonstrate_isomorphism.py` regenerates the six-act Bell thesis, reissues signed receipts, and documents the Planck fallback with a precise SMT proof transcript.【F:audit_logs/demonstrate_isomorphism.log†L421-L501】
  - *TA3 – Transition Readiness:* `attempt.py` still serves as the deep-dive orchestrator, emitting sealed hashes and a JSON summary for auditors reviewing the philosophical engine.【F:audit_logs/attempt.log†L752-L784】
- **Go/No-Go KPPs:**

| KPP | Threshold | Objective | Current Status | Evidence |
| --- | --- | --- | --- | --- |
| Automated specification verification | Manual replay | Headless replay including Coq | **Met** — verifier completes without operator edits | 【F:audit_logs/verify_thiele_machine.log†L1-L25】 |
| Bell thesis rerun | 1 narrated run | Repeatable reruns with logged artefacts | **Met with observation** — run completes but flags the Planck fallback | 【F:audit_logs/demonstrate_isomorphism.log†L421-L501】 |
| Receipt integrity | Signatures present | Ed25519 validation with zero μ-bit debt | **Met** — canonical receipts verify; only legacy file is skipped | 【F:audit_logs/challenge_verify.log†L1-L5】 |
| Coq receipt replay | Manual script | Headless `verify_truth.sh` | **Met** — receipts replay cleanly after key rotation | 【F:audit_logs/verify_truth.log†L1-L1】 |
| Demo suite stability | Opportunistic runs | Non-interactive automation with logging | **Met (core demos)** — CHSH and RSA demos execute under sandboxed VM | 【F:audit_logs/demonstrate_isomorphism.log†L421-L485】 |

- **Phase criteria:**
  - *Phase I – Cross-platform bring-up:* Ubuntu 24.04 + Python 3.12 + Coq 8.18.0 installed via documented commands. **Status:** Met.【F:audit_logs/verify_thiele_machine.log†L1-L13】
  - *Phase II – Receipt integrity:* Ed25519 signatures validated; legacy receipts queued for migration. **Status:** Met with observation.【F:audit_logs/challenge_verify.log†L1-L5】
  - *Phase III – Demo hardening:* AST sandbox and compression-based μ-bit accounting active; RSA demo emits partition receipts. **Status:** Met.【F:thielecpu/vm.py†L174-L247】【F:demos/rsa_partition_demo.py†L31-L188】
  - *Phase IV – Programmatics:* This report, refreshed audit logs, and FORMAL_GUARANTEES enumerate the TCB. **Status:** Met.【F:FORMAL_GUARANTEES.md†L1-L61】

## Test & Evaluation Summary
- **Environment:** Ubuntu 24.04 container, Python 3.12.10 via `pip install -e .`, Coq 8.18.0 from Ubuntu packages. Tool versions are recorded at the start of the thesis run for auditability.【F:audit_logs/demonstrate_isomorphism.log†L8-L21】
- **Datasets & controls:** The canonical Planck FITS sample currently fails verification, triggering the bundled deterministic patch; witness generation and SMT proofs complete regardless.【F:audit_logs/demonstrate_isomorphism.log†L479-L485】
- **Acceptance test outcomes:**
  1. `python scripts/verify_thiele_machine.py` — **Pass**.【F:audit_logs/verify_thiele_machine.log†L1-L25】
  2. `python demonstrate_isomorphism.py` — **Pass with Planck fallback logged**.【F:audit_logs/demonstrate_isomorphism.log†L421-L485】
  3. `python attempt.py` — **Pass**, emitting sealed transcript hashes.【F:audit_logs/attempt.log†L752-L784】
  4. `python scripts/challenge.py verify receipts` — **Pass with warning** (legacy schema skipped).【F:audit_logs/challenge_verify.log†L1-L5】
  5. `./scripts/verify_truth.sh examples/tsirelson_step_receipts.json` — **Pass** after key rotation.【F:audit_logs/verify_truth.log†L1-L1】
- **Compute envelope:** Full verification completes in under five minutes on four vCPUs; Coq compile totals ≈4.7s and Act VI remains dominated by Z3 solves (~30s).【F:audit_logs/verify_thiele_machine.log†L9-L24】【F:audit_logs/demonstrate_isomorphism.log†L421-L485】
- **Red-team hooks:** The AST whitelist blocks dynamic imports and method calls outside an approved surface; remaining findings are triaged in `docs/static_analysis_triage.md`.【F:thielecpu/vm.py†L174-L247】【F:docs/static_analysis_triage.md†L1-L11】
- **Independent replay artefacts:** Fresh logs for every script reside in `audit_logs/`, including the successful Coq replay and the Planck fallback transcript.【F:audit_logs/verify_truth.log†L1-L1】【F:audit_logs/demonstrate_isomorphism.log†L421-L485】

## Execution and Verification Log
| Command | Result | Evidence |
| --- | --- | --- |
| `python scripts/verify_thiele_machine.py` | ✅ Completed; Coq bundles compiled headlessly | 【F:audit_logs/verify_thiele_machine.log†L1-L25】 |
| `python demonstrate_isomorphism.py` | ✅ Completed; Planck dataset fell back to canonical patch | 【F:audit_logs/demonstrate_isomorphism.log†L421-L485】 |
| `python attempt.py` | ✅ Completed; sealed transcript hashes recorded | 【F:audit_logs/attempt.log†L752-L784】 |
| `python scripts/challenge.py verify receipts` | ⚠️ Completed with legacy-format warning | 【F:audit_logs/challenge_verify.log†L1-L5】 |
| `./scripts/verify_truth.sh examples/tsirelson_step_receipts.json` | ✅ Coq replay discharged | 【F:audit_logs/verify_truth.log†L1-L1】 |

## Architecture and Implementation Deep Dive
- **Virtual Machine & ISA:** PYEXEC now routes through `safe_execute`, which parses the payload into an AST, walks it with `SafeNodeVisitor`, and executes it under a constrained global scope; μ-bit charges are measured by compressing the canonical payload as a Kolmogorov proxy.【F:thielecpu/vm.py†L174-L247】
- **Receipt pipeline:** Runtime instrumentation ensures Ed25519 signatures over canonical JSON snapshots, lazily generating keys if missing and exposing verification helpers for auditors.【F:thielecpu/receipts.py†L22-L197】
- **Formal bridge:** FORMAL_GUARANTEES and Coq `Axioms.v` make the axiomatic surface explicit, matching the receipts consumed by `verify_truth.sh`.【F:FORMAL_GUARANTEES.md†L1-L61】【F:coq/thielemachine/Axioms.v†L1-L12】
- **Demonstrations:** The RSA partition demo now emits receipts for each partition, reinforcing the partition-native narrative; CHSH demo executes entirely under the sandboxed interpreter.【F:demos/rsa_partition_demo.py†L31-L188】【F:audit_logs/demonstrate_isomorphism.log†L421-L485】

## Transition and Adoption Outlook
- **Target users:** Government verification labs and academic cryptographers evaluating ledgers for scientific computation.
- **Mission thread:** Deploy the VM + receipt verifier in controlled analysis environments for Bell-thesis reproduction and receipt validation.
- **Integration (90-day) plan:**
  1. Refresh the Planck FITS sample and rerun the thesis log to remove the fallback observation.【F:audit_logs/demonstrate_isomorphism.log†L479-L485】
  2. Migrate legacy receipts via `scripts/migrate_legacy_receipts.py` and revalidate with the challenge harness.【F:audit_logs/challenge_verify.log†L1-L5】
  3. Containerize the hardened workflow (Dockerfile provided) and publish the refreshed audit logs with FORMAL_GUARANTEES for external labs.【F:Dockerfile†L1-L58】【F:FORMAL_GUARANTEES.md†L1-L61】
  4. Establish a key-rotation SOP using `scripts/generate_kernel_keys.py` and `scripts/resign_receipts.py` for future releases.【F:thielecpu/receipts.py†L49-L101】【F:scripts/resign_receipts.py†L1-L92】
- **Sustainment:** Maintain quarterly reruns of the verification suite, rotate audit logs per release, and record dependency updates in a forthcoming `CHANGELOG.md`.

## Programmatics Snapshot
- **Milestones:**
  - M1: Cross-platform automation (met).
  - M2: Receipt hardening and sandboxed runtime (met).
  - M3: Dataset refresh and legacy receipt migration (open observation).
- **Cost/Schedule:** Work remains self-funded; the outstanding effort centres on data curation and log maintenance.
- **CDRL status:** This report plus refreshed audit logs satisfy the status-reporting deliverable; SBOM automation remains backlog.

## Risk Register
| ID | Risk | P | I | Mitigation | Status |
| --- | --- | --- | --- | --- | --- |
| R1 | Planck FITS archive remains unreadable, forcing fallback | M | M | Regenerate FITS from source tooling or ship verified surrogate with checksum | Open |
| R2 | Legacy receipts still in list-based schema | M | L | Batch convert via `scripts/migrate_legacy_receipts.py` and retire deprecated files | Planned |
| R3 | Optional demos rely on Playwright/browser extras | L | L | Keep `[demos]` extra documented and separate from core pipeline | Mitigated |
| R4 | AST whitelist may block future scientific payloads | L | M | Provide scoped opcode extensions vetted through security review | Accepted |

## Security, Compliance, and Assurance
- **Cryptography:** Receipts use Ed25519 signatures stored outside the repo; verification relies on the regenerated 32-byte public key.【F:thielecpu/receipts.py†L49-L101】
- **Supply chain:** Dependencies are pinned in `pyproject.toml`; Coq is sourced from Ubuntu repositories and recorded in the thesis transcript.【F:pyproject.toml†L1-L157】【F:audit_logs/demonstrate_isomorphism.log†L8-L21】
- **Static analysis:** Outstanding `eval` exemptions are catalogued for auditors in `docs/static_analysis_triage.md`.【F:docs/static_analysis_triage.md†L1-L11】
- **Data handling:** Cosmological inputs contain no PII; the fallback demonstrates graceful degradation when integrity checks fail.【F:audit_logs/demonstrate_isomorphism.log†L479-L485】

## Development Environment & Root Cause Update
- **Origin:** Windows + VS Code with Copilot assistance originally introduced hard-coded Coq paths and permissive PYEXEC scaffolding.
- **Current state:** Hardened Linux workflow with PATH-discovered toolchain, AST-sandboxed runtime, and Ed25519 receipts; residual cleanup is limited to data refresh and receipt migration.【F:thielecpu/vm.py†L174-L247】【F:thielecpu/receipts.py†L49-L197】

## Data Rights, Licensing, and Export
- **Licensing:** Apache-2.0; third-party dependencies retain upstream licensing captured in `pyproject.toml`.【F:LICENSE†L1-L203】【F:pyproject.toml†L1-L157】
- **Distribution:** Suitable for Distribution Statement A pending sponsor review; no controlled technical data identified.
- **Export control:** No ITAR/EAR triggers observed; Planck data is public domain.【F:artifacts/MANIFEST.sha256†L1-L60】

## Ethics & Responsible AI Considerations
- **Misuse risk:** Ledger transparency, Ed25519 signatures, and Coq replay deter covert tampering; remaining action is data provenance hardening.【F:thielecpu/receipts.py†L49-L197】【F:audit_logs/demonstrate_isomorphism.log†L479-L485】
- **Bias/Data:** Synthetic CHSH data and curated Planck subsets avoid human subjects; any bias stems from dataset selection and is documented in receipts.【F:audit_logs/demonstrate_isomorphism.log†L421-L485】
- **Red-team posture:** Recommend independent red-team once the Planck archive and legacy receipt migration complete.
