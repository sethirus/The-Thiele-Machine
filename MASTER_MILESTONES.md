# Master Milestones: No‑Free‑Insight → Derived Structure → Prediction

Date: 2025‑12‑16

This repo’s north star is **3‑layer isomorphism** (Coq ↔ extracted runner ↔ Python VM ↔ RTL) and an “inquisitor” standard: **no `Admitted.`, no `admit.`, no `Axiom`.**

The flagship goal is an inevitability theorem of the form:

> **Auditably-correct explanations with bounded observers + local composition** force an **explanatory conservation law** (“no free insight”).
> From that law we derive a **quantitative limit** (Tsirelson-like bound) and ship **one sharp divergence prediction**.

---

## Ground Rules (non‑negotiable)

- **No proof holes:** no `Admitted.`, no `admit.`, no `Axiom` in active Coq tree.
- **Receipt-defined observables only:** theorems quantify over what can be decoded from receipts/observations.
- **Single-source semantics:** kernel step semantics and state projection are authoritative (see `AGENTS.md`).
- **Every milestone ends with an executable gate:** Coq build + focused pytest(s) + inquisitor.

Core gates (fast):
- `make -C coq core`
- `pytest -q tests/test_partition_isomorphism_minimal.py`
- `pytest -q tests/test_rtl_compute_isomorphism.py`
- `python scripts/inquisitor.py`

Closed-work command (single-shot):
- `make closed_work`

---

## Shared Spine (build once, reuse for all C-modules)

Acceptance criteria:
- [x] Coq: `coq/kernel/ReceiptCore.v` defines a generic receipt channel + decoder predicate.
- [x] Python: `verifier/receipt_protocol.py` provides common trust/sig + PASS/FAIL artifact writer.
- [x] Schema: `artifacts/schema/verification.schema.json` is the single verification schema for all C modules.
- [x] Runner: `scripts/closed_work.py` runs `C_randomness`, `C_tomography`, `C_entropy`, `C_causal` and fails if any fail.

Non-negotiable falsifier pattern (every C-module ships these 3 tests):
- [x] Forge test: attempt to manufacture receipts without canonical channel/opcode/path.
- [x] Underpay test: attempt to obtain the claim while paying fewer μ/info bits than required.
- [x] Bypass test: attempt to route around the channel (unreceipted dataset/file/log) and confirm rejection or UNCERTIFIED.

---

## Execution Checklist (live)

Legend: `[ ]` pending, `[x]` complete.

### Gates
- [x] `make -C coq core`
- [x] `pytest -q tests/test_partition_isomorphism_minimal.py`
- [x] `pytest -q tests/test_rtl_compute_isomorphism.py`
- [x] `python scripts/inquisitor.py`

---

## Deliverable A — No Free Insight (general, not CHSH)

### A0. Scope
Prove a theorem that **does not mention Bell/CHSH**. It only talks about:
- what observers can read (evidence channel),
- what claims mean (predicates over execution/receipts),
- what it means to “strengthen a claim”,
- and how μ / information ledger moves.

### A1. Definitions (Coq)
Acceptance criteria:
- [x] A **general observation interface** for evidence extraction is defined.
- [x] A **Certified** notion is defined from kernel semantics (no error + claim holds).
- [x] A **Strengthening** relation `P_strong ▷ P_weak` is defined (strict, nontrivial).
- [x] **Non-forgeability** (evidence is step‑generated; PYEXEC cannot counterfeit) is formalized.
- [x] A **semantic** notion of **Structure‑Addition Event** is defined as the minimal class of steps that increases distinguishability (not “these opcodes” by fiat).

Primary locations:
- `coq/nofi/NoFreeInsight_Interface.v`
- `coq/nofi/NoFreeInsight_Theorem.v`
- Kernel instance: `coq/nofi/Instance_Kernel.v`

### A2. Theorem (Coq): No Free Insight — General Form
Target statement shape:

> If a run certifies `P_strong` and `P_strong ▷ P_weak` (relative to the observer/evidence channel), then the trace contains a structure-addition event and pays a corresponding μ/μ_info increase.

Acceptance criteria:
- [x] The theorem is fully proven in Coq with no axioms/admitted.
- [x] The theorem is instantiated to the kernel model.
- [x] A focused Python test demonstrates the corresponding runtime phenomenon for at least one instance predicate.

---

## Deliverable B — Tsirelson as a theorem of admissibility (not policy)

### B0. Scope
We want a **literal inequality on CHSH** to follow from an admissibility/resource principle, not from a runtime “gate we chose”.

Important clarification:
- Kernel traces are deterministic; a *literal* CHSH ≤ bound for traces requires a **trace → induced measurement model** (distributional semantics) or a restricted trace generator class that cannot emit arbitrary `CHSH_TRIAL` streams.

### B1. Define an admissible generator class
Acceptance criteria:
- [x] A finite, exact, receipt-defined generator class is specified (syntactic + semantic).

We already have a box-level literal theorem for an admissible class (local ∪ TsirelsonApprox) in:
- `coq/thielemachine/coqproofs/QuantumAdmissibilityTsirelson.v`

- [x] Box-level literal theorem shipped (local ∪ TsirelsonApprox ⇒ CHSH ≤ 5657/2000).

Next step is to **connect generators (programs/traces) → induced boxes/receipts**.

### B2. Prove: Admissible ⇒ structure ⇒ CHSH ≤ bound
Acceptance criteria:
- [x] `admissible_generator(tr)` implies the induced distribution has the required factorization/locality structure.
- [x] That structure implies `CHSH ≤ bound` by exact rational inequality (no reals required).

### B3. Tightness + quantitative boundary
Acceptance criteria:
- [x] Exhibit an admissible family that approaches the bound from below (tightness / near‑optimality).
- [x] Prove: supra-bound behavior implies non‑admissible and yields a **quantitative μ lower bound** `Δμ_info ≥ f(ε)`.

---

## Deliverable C — One divergence prediction (sharp + testable)

We will ship **C2 first** (operational divergence) because it is fully realizable inside the repo’s semantics and yields a sharp falsifier harness.

### C2 (primary): “Science/AI can’t cheat anymore” divergence
Claim:
- Any pipeline claiming improved predictive power / stronger evaluation / stronger compression must carry an explicit, checkable structure/revelation certificate; otherwise it is vulnerable to a specific class of undetectable “free insight” failures.

Acceptance criteria:
- [x] A Coq predicate family instantiating NoFI (A) is defined (not CHSH-specific).
- [x] Python harness: forged improvement without certificate.
- [x] Python harness: certified version requires structure-addition + μ_info cost.
- [x] Python harness: verifier rejects uncertified improvements.

Suggested location:
- `tests/test_nofi_prediction_pipeline.py` (new)
- Reuse kernel/VM certification primitives (`REVEAL`/`LASSERT`/`LJOIN` etc.)

### C1 (stretch): physics divergence
Goal:
- Define a **receipt-defined** mapping from a physical/bench experiment → an audited claim.
- Provide a verifier that **rejects supra-performance claims** unless accompanied by explicit disclosure/calibration artifacts.

Acceptance criteria (C1 is “real” once these are executable):

#### C1.1 Receipt schema + run directory contract
- [x] Define a minimal on-disk run layout (`run_dir/`) and the required artifacts.
- [x] Define a signed receipt format for those artifacts (TRS-1.0 file manifest is acceptable).
- [x] Document which fields are observation-relevant (metric, baseline, epsilon, disclosure bits).

#### C1.2 Verifier (receipt-only)
- [x] Implement a verifier that:
	- reads only receipt + files named by receipt,
	- validates signature via trust manifest,
	- enforces: claimed improvement above baseline requires explicit disclosure/calibration evidence.

#### C1.3 Falsifier harness (pytest)
- [x] Add tests that demonstrate:
	- forged improvement without calibration/disclosure is rejected,
	- insufficient disclosure bits is rejected,
	- certified + sufficient disclosure passes,
	- non-improvement claims can pass without disclosure.

#### C1.4 External mapping (protocol pick)
- [ ] Pick one concrete protocol (e.g. Bell optics calibration run, metrology, spectroscopy, etc.).
- [ ] Specify the exact mapping from raw data → metric and the calibration parameters that must be disclosed.

#### C1.5 Cross-layer gate (optional but preferred)
- [ ] Add a gate that can replay the claim verification deterministically from artifacts.

Status:
- C1.1–C1.3 are repo-internal and should be executable now.
- C1.4–C1.5 become meaningful once we select a physical protocol.

---

## C-RAND — Device-independent certified randomness

Goal: You can’t claim “fresh unpredictable bits” unless you either:
- pay explicit μ/info revelation for nonlocality, or
- accept `ERR` / `UNCERTIFIED`.

Acceptance criteria:
- [x] Verifier: `verifier/check_randomness.py` outputs `(min_entropy_lower_bound, extracted_bits, certification_status)` from receipts.
- [x] Closed-work: `make closed_work` produces `C_randomness/verification.json` + signed receipt.
- [x] Falsifiers: forge / underpay / bypass tests exist and pass.

---

## Flagship Track — External Confrontation Theorem (DI randomness first)

This is the missing bridge between “serious framework” and “outsiders are forced to react.”

Target shape (the fight):

> Under an explicit, receipts-only operational constraint **C(K)** (bounded observer / bounded structure-addition / bounded μ-information),
> the system proves a quantitative bound **B(K)** on an outsider-accepted metric **M**.
> Standard theory predicts strictly beyond **B(K)** under the “same” operational setup.

We will do this first in the fastest-to-loud domain: **device-independent randomness**.

### D0. Scope lock (choose one flagship)
Acceptance criteria:
- [x] Flagship is fixed to **DI randomness** until D4 is complete.
- [x] All other domains remain gated/maintained but are not allowed to absorb milestone time.

### D1. Protocol transcript (receipts-only)
Deliverable:
- [x] Implement `decode_rng_transcript(receipts) -> transcript`.

Acceptance criteria:
- [x] Transcript is derived only from receipts (no stdout/log parsing).
- [x] Transcript is stable/canonical (deterministic ordering + schema).
- [x] Add a bounded falsifier test: compiled VM program → receipts → transcript round-trip.

Suggested location:
- `tools/rng_transcript.py` (new)

### D2. Outsider-accepted security metric
Deliverable:
- [x] Implement `rng_metric(transcript) -> (Hmin_lower_bound, epsilon)`.

Acceptance criteria:
- [x] Metric is conservative and explicitly defined (no hidden assumptions).
- [x] Metric is computed from transcript only.
- [x] Add tests showing monotonicity under disclosure/μ where appropriate.

Suggested location:
- `tools/rng_metric.py` (new)

### D3. Admissibility/resource constraint in Coq (no holes)
Deliverable:
- [x] Define `Admissible(K)` capturing the operational constraint, e.g.:
	- total μ-information ≤ K
	- structure-addition steps (REVEAL/cert setters) bounded by K
	- receipts-only observation model

Acceptance criteria:
- [x] Coq statement is axiom-free / admitted-free.
- [x] Constraint matches what the Python VM and receipts can actually report.

Suggested location:
- `coq/thielemachine/verification/RandomnessNoFI.v` (new)

### D4. Quantitative bound theorem (the mic-drop)
Deliverable:
- [x] Prove: `Admissible(K) -> rng_metric(transcript) <= f(K)`.

Acceptance criteria:
- [x] Theorem is machine-checked in Coq (no holes).
- [x] The bound is quantitative and nontrivial (strictly constraining certified randomness).
- [x] Python falsifier harness tries to violate the bound (bounded search) and fails.

### D5. Conflict chart (external-facing confrontation artifact)
Deliverable:
- [x] Script that generates a curve/summary comparing:
	- repo-measured/derived `f(K)` envelope, vs.
	- a reference curve from standard DI randomness theory (documented inputs)

Acceptance criteria:
- [x] Output is written as an artifact under `artifacts/closed_work/<stamp>/`.
- [x] `make closed_work` includes this chart generation step.
- [x] The comparison is explicit enough that a reader can disagree on assumptions (and still reproduce the numbers).

---

## C-TOMO — Tomography / estimation as priced knowledge

Goal: Estimation precision is a paid-for refinement: tighter ε requires more trials or explicit revelation.

Acceptance criteria:
- [x] Verifier: `verifier/check_tomography.py` verifies estimate-within-ε given trials and enforces a cost rule.
- [x] Closed-work: `make closed_work` produces `C_tomography/verification.json` + signed receipt.
- [x] Falsifiers: forge / underpay / bypass tests exist and pass.

---

## C-ENTROPY — Coarse-graining made explicit and enforced

Goal: Entropy is underdetermined without an explicit coarse-graining; entropy claims must declare coarse-graining in-trace.

Acceptance criteria:
- [x] Verifier: `verifier/check_entropy2.py` rejects entropy without declared coarse-graining and checks consistency.
- [x] Closed-work: `make closed_work` produces `C_entropy/verification.json` + signed receipt.
- [x] Falsifiers: forge / underpay / bypass tests exist and pass.

---

## C-CAUSAL — Causal inference as “no free causal explanation”

Goal: If you claim a causal model strictly stronger than observational equivalence class supports, the trace must declare the extra assumptions (structure-addition).

Acceptance criteria:
- [x] Verifier: `verifier/check_causal.py` rejects unique-DAG claims unless interventions/disclosure are present.
- [x] Closed-work: `make closed_work` produces `C_causal/verification.json` + signed receipt.
- [x] Falsifiers: forge / underpay / bypass tests exist and pass.

---

## Single completion criterion (closed work)

`make closed_work` must produce, for each module:
- `C_randomness/verification.json` + signed receipt
- `C_tomography/verification.json` + signed receipt
- `C_entropy/verification.json` + signed receipt
- `C_causal/verification.json` + signed receipt

…and each verification contains:
- PASS/FAIL (or PASS/UNCERTIFIED/FAIL)
- explicit falsifier attempts and outcomes
- declared structure additions (if any)
- μ/info accounting summary

---

## Phase Map (for the ‘flagship run’ narrative)

INIT → DISCOVER → CLASSIFY → DECOMPOSE → EXECUTE → MERGE → VERIFY → SUCCESS

We keep this as the canonical story for demos/visualizations, but proofs are the source of truth.

---

## Current status (as of 2025‑12‑16)

- Kernel certification boundary strengthened: quantum-admissible traces can’t certify *any* CHSH claim.
- Box-level literal theorem shipped: admissible class ⇒ CHSH ≤ 5657/2000.
- Coq core builds; focused gates pass; inquisitor OK.

---

## Definition of done (project)

Done means:
1) Deliverable A (general NoFI) proven and instantiated.
2) Deliverable B (admissibility ⇒ literal quantitative bound) proven, tightness shown, and supra-bound implies quantitative μ lower bound.
3) Deliverable C2 divergence implemented with a falsifier harness and end-to-end cross-layer gate(s).
