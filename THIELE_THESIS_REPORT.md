# The Thiele Machine — Thesis-level Verification & Investigation Report

Version: 1.0
Date: 2025-10-10

Purpose
-------

This document is the canonical verification plan and thesis-level report for the
Thiele Machine project. It defines the central formal claim, the assumptions
required, and a comprehensive experimental, proof-audit, and replication
program to determine the *real* accuracy, scope, and limitations of the
project's conclusions. The goal is a reproducible and independently verifiable
accounting that demonstrates whether the formal and empirical claims hold under
scrutiny.

Audience
--------

Formal-methods researchers, empirical replicators, hardware implementers,
security reviewers, journal reviewers, and funding/oversight bodies.

Executive summary
-----------------

- Formal claim: The repository formalises a model called the Thiele Machine and
  provides a mechanised separation proof (Coq) showing a family of instances for
  which Thiele programs have strictly lower information cost and the classical
  Turing search must pay exponential time under stated axioms. See
  `coq/thielemachine/coqproofs/Separation.v` and `coq/AXIOM_INVENTORY.md`.
 - Empirical evidence: Python VM (`thielecpu/vm.py`) emits signed step receipts.
   The canonical thesis run is `demonstrate_isomorphism.py` (six‑act Bell demonstration) which
   regenerates the narrated ledger and the canonical receipts used for Coq replay. The broader
   universal orchestrator `attempt.py` runs additional experiments and benchmarks and produces
   extra artifacts in `shape_of_truth_out/` and `archive/`.

Sighted / Blind (terminology)
-----------------------------
To avoid ambiguity, we define the two technical modes used throughout this report:

* Sighted — a model that has access to an audited geometric/information ledger; sighted resource bounds are expressed in Coq by `thiele_sighted_steps` and `thiele_mu_cost`.
* Blind — the formal baseline that performs DPLL/CH-style blind search; its cost is expressed in Coq by `turing_blind_steps`.

Toolchain snapshot (pin versions)
---------------------------------
Record toolchain versions as part of the verification envelope; these are the versions used for the canonical runs and preferred for audits:

- Coq: 8.18.x
- Z3: 4.8.x
- Python: 3.12.x (3.11+ supported)
- cvc5: optional (used for some corroboration checks)
- Verification required: (A) Coq mechanised proof audit; (B) receipt replay and
  cryptographic verification; (C) independent empirical replication of the
  claimed resource scaling; (D) hardware/Verilog equivalence testing if
  hardware claims are pursued.

How to use this document
------------------------

Follow the three-pillar program below: Proof audit, Empirical validation,
Hardware & Systems alignment. Each pillar contains a reproducible checklist,
measurement protocols, acceptance criteria, and a list of artifacts to examine.

Pillar 0 — Preconditions and safe-guards
----------------------------------------

Before any experiments or proof reviews, record the following and make these
artifacts public to the auditors:

1. Toolchain snapshot: Python executable path, `z3` version, `coqc` version,
   OS release, CPU, and RAM. Use `gather_toolchain_versions()` in
   `demonstrate_isomorphism.py` or the `scripts/toolchain_snapshot.sh` helper
   (if present).
2. Deterministic environment: set `TZ=UTC`, `LC_ALL=C`, `LANG=C`,
   `PYTHONHASHSEED=0` and capture the full environment in an archived file.

   For reproducible runs, export these variables before invoking the canonical demonstration:

   ```bash
   export TZ=UTC LC_ALL=C LANG=C PYTHONHASHSEED=0
   ```
3. Cryptographic keys: document whether the receipts are signed with a demo
   key or a secret key; publish the public verification key; ensure HMAC/Ed25519
   keys are plumbed through environment variables and not hard-coded in tests.

μ-cost (one-sentence definition)
--------------------------------
`μ` denotes the ledger-measured information cost (an MDL-style description length) consumed to perceive and record geometric structure; the Coq axiom `mu_lower_bound` formalises the link between concrete receipt accounting and abstract μ-cost used in the proofs.

Pillar 1 — Proof audit (Coq)
---------------------------

Objective: Confirm that the separation theorems are mechanised correctly given
the stated axioms; ensure the axioms are explicit and theorems do not
implicitly rely on unstated assumptions.

Artifacts to inspect
- `coq/AXIOM_INVENTORY.md` — the list of axioms and their provenance.
- `coq/thielemachine/coqproofs/Separation.v` — the strictness proof.
- `coq/thielemachine/coqproofs/ThieleMachine.v` — machine semantics.
- Any `*.v` files referenced by `Separation.v` (simulation, containment lemmas).

Verification steps
1. Reproduce the Coq build on a fresh container: `./coq/verify_subsumption.sh`.
2. Work through the proof dependencies: find any `Admitted` or `Axiom` that
   materially affect the final separation theorem.
3. For each axiom in `coq/AXIOM_INVENTORY.md`, document:
   - Source (reference to literature or empirical grounding).
   - Strength: conservative vs controversial. Mark axioms that assert
     'blind SAT hardness' or complexity-theoretic lower bounds — list them
     separately as they are the most delicate.
4. Re-run `coqc` invocations with `-verbose` and `-list-plugins` where
   appropriate; capture timings and memory use for each proof file.
5. Map Coq obligations to runtime receipts: for each critical lemma derive the
   expected VM step receipts that the proof requires; confirm a one-to-one
   mapping and include the exact proof term locations.
6. Use the repository's experiment and replication helpers to exercise the
   proof-to-runtime bridge: `experiments/lab_notebook_template.csv`,
   `experiments/analysis_notebook.ipynb`, `experiments/run_analysis.py`, and
   the `replication/` Docker replication kit.

Audit checklist and acceptance criteria
- No `Admitted` statements in the separation-critical path.
- Axioms are explicitly enumerated and labelled in the inventory with
  recommended references or optional alternative axioms where possible.
- Proofs compile in a fresh container using released Coq and standard libs.

Pillar 2 — Receipt replay and cryptographic verification
-------------------------------------------------------

Objective: Demonstrate that the runtime traces (step receipts) faithfully
represent the VM executions that the Coq proofs reason about.

Artifacts to inspect
- `thielecpu/receipts.py` — receipt assembly and signing.
- `shape_of_truth_out/` and `artifacts/` receipts and `step_receipts.json`.
- Receipt verification harness: `scripts/challenge.py` and related tooling.

Reproducible checklist
1. Run `python3 demonstrate_isomorphism.py` to generate canonical receipts in `out/` (or the
   default output directory). If you need the broader set of experiments and extra traces, you may instead run `python attempt.py`.
2. Run `python scripts/challenge.py verify receipts`.
   - Confirm each receipt verifies the HMAC/Ed25519 signature against the
     published public key.
   - Confirm that the replay checker accepts the receipts against the Coq
     oracle (when applicable) or the VM semantics checker.
3. For each StepReceipt record the tuple: (step id, instruction, pre/post
   state snapshot, observation, signature). Store as CSV for further analysis.

Acceptance criteria
- All signatures verify against the published public keys.
- The replay checker must not require any hidden state beyond the receipt
  payload and the public key.

Pillar 3 — Empirical scaling experiments & statistical validation
----------------------------------------------------------------

Objective: Determine whether the empirical runtime and the μ-bit accounting
match the formal claim about exponential classical-time cost vs
polynomial-information Thiele programs on the target instance families.

Instance families
- Tseitin formulas on expanders (primary hard family used in proofs).
- Paradox/paradoxical constructions used in paper and `attempt.py`.
- CHSH/Tsirelson small experiments (for demonstration of concept).

Measurement plan
1. For each family, run the blind classical solver (reference SAT/DPLL) and
   the Thiele program on a sequence of instance sizes N ∈ {n0, n1, ..., nk}.
2. Collect per-run:
   - wall-clock time (median of repeated runs), CPU-time, memory footprint.
   - VM μ-bit accounting (`mu_operational`, `mu_information`).
   - number of receipts produced and sizes of certificates on disk.
   - solver-specific diagnostics (conflicts, propagations) where available.
3. Repeat experiments with varying random seeds and compute 95% confidence
   intervals on timings.
4. Fit scaling models: linear, polynomial, exponential. Use likelihood ratio
   tests and AIC/BIC to evaluate model fit. For each solver, estimate the
   asymptotic scaling exponent and confidence intervals.

Safety limits and experimental controls
- Enforce `THIELE_MAX_COMBINATIONS` to avoid runaway brute force.
- Use identical hardware and container snapshots; collect `dmesg` and OS
  counters to catch noisy runs. Run each configuration at least 5 times and
  report medians and IQRs.

Statistical acceptance criteria
- The separation claim is supported if, over the target instance family,
  empirical fits show polynomial scaling for Thiele program cost in explicit
  metrics while the blind solver scaling is consistent with exponential
  increases (better-than-polynomial rejection with p < 0.05).
- Report effect sizes, confidence intervals for exponents, and raw data to
  allow independent re-analysis.

Pillar 4 — Hardware & Verilog alignment
--------------------------------------

Objective: Show behavioural parity between the Python VM semantics and the
Verilog hardware implementation (RTL). Provide testbenches and equivalence
evidence for safety-critical instructions.

Artifacts
- `thielecpu/hardware/*.v` — Verilog sources and testbenches.
- `thielecpu/hardware/test_hardware.py` — simulation harness.

Verification steps
1. For a set of representative micro-programs, run the VM and dump
   instruction-level traces and I/O vectors.
2. Simulate the Verilog (Icarus/Verilator) using the same vectors and
   compare outputs cycle-by-cycle. Use Yosys-based formal equivalence checks
   if available for combinational blocks.
3. For any mismatch, file an artefact-specific reproducible test-case and
   produce a minimal counterexample.

Acceptance criteria
- Behavioral equivalence for the canonical instruction set on representative
  workloads within a reasonable timing/latency tolerance (for synchronous
  blocks) and exact match for functional outputs.

Pillar 5 — Security, ethical, and disclosure controls
----------------------------------------------------

Objective: Ensure responsible handling of potent capabilities (e.g., RSA
cryptanalysis) and provide an audit trail for responsible-use interventions.

Requirements
1. Logging (we added a configurable monitor) — enable by default in release
   builds and provide redaction controls for sensitive fields.
2. Responsible-use notice: available, not printed by default on import, but
   explicitly displayable via `display_security_warning()`.
3. Operational policy document: require reviewers to document intended use and
   sign a short responsible-use statement (stored in the logs) before running
   production-scale experiments.

Ethical acceptance criteria
- No public release of non-redacted factorization outputs unless an
  institutional review and risk mitigation plan are in place. Any request to
  run large-scale factoring experiments must include a documented responsible
  use plan.

Appendix A — Evidence matrix (quick map)
----------------------------------------

- Formal proof: `coq/thielemachine/coqproofs/Separation.v`
- Axioms: `coq/AXIOM_INVENTORY.md`
- VM: `thielecpu/vm.py`
- Receipts: `thielecpu/receipts.py` and sample receipts in `artifacts/`
 -- Orchestration: `demonstrate_isomorphism.py` (canonical thesis run) and `attempt.py` (full universal orchestrator)
    - Ledger & manifest: `BELL_INEQUALITY_VERIFIED_RESULTS.md` is regenerated by the canonical run; its hashes are sealed in `artifacts/MANIFEST.sha256` and are authoritative for auditors.
    - CHSH/Tsirelson claim: classical bounds are certified as **UNSAT** with QF_LIA certificates, and the Tsirelson witness is constructed and checked as a **SAT**/QF_LRA certificate; solver artifacts are persisted for replay.
    - Key Coq lemmas to inspect directly: `local_CHSH_bound`, `TsirelsonApprox_not_local`, `concrete_receipts_sound`, `recorded_frames_sound` (search these names in `coq/thielemachine/coqproofs/`).
   - `local_CHSH_bound` — see `coq/thielemachine/coqproofs/BellInequality.v` (lemma begins near L701 in the current tree; line numbers may drift — grep by lemma name)
   - `TsirelsonApprox_not_local` — see `coq/thielemachine/coqproofs/BellInequality.v` (lemma begins near L993; line numbers may drift — grep by lemma name)
   - `concrete_receipts_sound` — see `coq/thielemachine/coqproofs/BellInequality.v` (bridge lemma, begins near L1116; line numbers may drift — grep by lemma name)
      - `recorded_frames_sound` — generated by `scripts/verify_truth.sh` into `coq/tmp_verify_truth.v` (the script emits a lemma `recorded_frames_sound` that applies `concrete_receipts_sound` — see `scripts/verify_truth.sh` and `scripts/verify_truth.py` for the generation template)
- Tests: `tests/` (unit tests and the new security monitor tests)
- Hardware RTL: `thielecpu/hardware/`

Appendix B — Minimal reproducible checklist (short)
--------------------------------------------------

1. Clone repository and build a deterministic environment (this repo's
   `pyproject.toml` lists python deps). Use a pinned container or a provided
   dev-image if available.
2. Before running the canonical script, set the deterministic export environment so the run, receipts, and manifests are reproducible:

```bash
export TZ=UTC LC_ALL=C LANG=C PYTHONHASHSEED=0
export THIELE_SEED=0    # canonical RNG seed used by the demonstration
export FORCE_DETERMINISTIC=1
```

3. Run: `python3 demonstrate_isomorphism.py` to produce the canonical thesis receipts and artifacts.
   If you need to run the broader universal orchestrator (extra demos/benchmarks), run `python attempt.py`.
3. Run: `python scripts/challenge.py verify receipts` to verify receipts.
4. Build Coq proofs: `cd coq && ./verify_subsumption.sh`.
5. Run empirical experiments: `python scripts/generate_tseitin_data.py` with
   controlled `THIELE_MAX_COMBINATIONS` and record outputs.
6. Run the headless analysis to generate scaling diagnostics: `python3 experiments/run_analysis.py`.

Artifact is the Argument

The canonical artefact bundle (definitions, mechanised proofs, deterministic runs that emit signed receipts, and the release manifest) together constitute the complete argument for the claim. Any rebuttal must identify a specific element of this bundle that fails (a concrete axiom, a receipt mismatch, a Coq lemma error, or an incorrect environment snapshot) and provide a minimal reproducible counterexample. This report and the accompanying artefacts are designed to make such disputes precise and mechanically checkable.

Appendix C — Open questions and recommended future experiments
------------------------------------------------------------

- Quantify the robustness of separation to model changes: what happens if
  axioms in `coq/AXIOM_INVENTORY.md` are weakened or replaced?
- Independent replication: provide a replication kit with hardware
  simulation images and a data package for the Tseitin benchmarks.
- Sensitivity analysis on the μ-bit accounting: varying cost assignments and
  checking whether the separation still manifests.

Acknowledgements
----------------

This verification plan builds on the code, proofs, and manuscripts available
in this repository and was composed to be auditable, reproducible, and
actionable by an independent team.
