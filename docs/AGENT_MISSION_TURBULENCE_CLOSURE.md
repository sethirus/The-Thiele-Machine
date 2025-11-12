# Agent Mission: NUSD Turbulence Closure v1 (Epoch Shot)

## Mission Overview

Using the Thiele/NUSD engine and the turbulence benchmarks already in this repository, the agent must discover and document a compact, symbolic turbulence closure law (`NUSD_Turbulence_Closure_v1`) that meets the following headline goals:

1. Works across multiple direct numerical simulation (DNS) datasets (at minimum the existing isotropic1024 and channel-flow traces plus the synthetic cascade suites).
2. Beats or matches standard closures (Smagorinsky-type, autoregressive baselines, and at least one small neural-network model) on both predictive accuracy (spectra, flux, RMSE) and `μ_total` cost (model plus residual).
3. Presents the final law as small, human-readable symbolic equations—no opaque neural nets.
4. Is reproducible end-to-end via `make turbulence-closure-v1` followed by the receipt verifier `python3 tools/verify_turbulence_closure_v1_receipt.py artifacts/turbulence_closure_v1_receipt.jsonl`.

The deliverable is a single law-level artifact that turns the turbulence pipeline into the "oh no, this thing really sees structure" demonstration.

---

## Phase 1 – Extend the Playground from Energy to Closure

### Objective
Move from scalar energy dynamics to subgrid/energy-transfer closures that are useful to turbulence researchers.

### Tasks
1. **Define Observables**
   - For each DNS dataset (isotropic1024, channel centerline, etc.), compute or load:
     - Resolved energy at the target scale or grid point, `E`.
     - Resolved velocity gradients or strain rates at the same location.
     - A subgrid target quantity, e.g. filtered energy flux `Π` or a stress component `τ_ij`.
   - Store the derived series under `public_data/jhtdb/...` with metadata (grid size, Reynolds number, domain, SHA-256 hash).
   - Extend `docs/NUSD_Turbulence_Benchmark.md` with a "Closure observables" section documenting the new fields.

2. **Baselines**
   - Implement the following baseline solvers for each series:
     - Blind encoder (`n·b + log₂(1 + b)` for `μ_question`, residual-driven `μ_answer`).
     - Smagorinsky-style closure (e.g. `τ ~ C_s Δ² |S| S_ij`) with coefficients fitted via least squares and encoded via MDL.
     - Autoregressive baselines (AR(1), AR(2)) on `Π` or `τ_ij`.
     - Optional tiny neural-network baseline (e.g. two-layer MLP) with the weights' MDL contributing to `μ_question`.
   - Capture baseline metrics in `docs/NUSD_Turbulence_Closure_Baselines.md` as tuples: (`μ_question`, `μ_answer`, `μ_total`, RMSE, spectrum/flux error).

3. **Benchmark Specification**
   - Update `docs/NUSD_Turbulence_Benchmark.md` to define the closure task, datasets, hashes, metrics, and acceptance thresholds.
   - Document the explicit training/validation split so held-out bundles are tested without re-fitting.

---

## Phase 2 – Define the Sighted Closure Hypothesis Space

### Objective
Enable the Thiele structural modeler to explore a rich yet controlled symbolic space of closure laws.

### Tasks
1. **Symbolic Form**
   - Extend the structural modeler with inputs such as `E`, local strain invariants like `|S|` or `S_ij S_ij`, characteristic length scale `Δ`, and optional neighbor values.
   - Limit operators to addition, subtraction, multiplication, division by constants, integer powers, and at most one bounded non-linearity (e.g. square root, absolute value, or logarithm).
   - Target outputs include subgrid flux `Π` or stress components `τ_ij`.

2. **NUSD Costing**
   - For every candidate law compute:
     - `μ_question` as the MDL of the symbolic expression (S-expression length plus quantised coefficients).
     - `μ_answer` as the logarithmic residual cost aggregated over all datasets.
     - `μ_total = μ_question + μ_answer - ε`, using the current calibration.

3. **Search Strategy**
   - Implement `tools/discover_turbulence_closure_v1.py` to explore the symbolic space (enumeration, randomised search, greedy MDL pruning, etc.).
   - Maintain a Pareto frontier over (`μ_total`, RMSE, spectrum/flux error).
   - Stop when improvements fall below thresholds or resource limits are hit.
   - Ensure all evaluations run through the NUSD accounting pipeline so the discovery is intrinsically "Sighted".

---

## Phase 3 – Lock in `NUSD_Turbulence_Closure_v1`

### Objective
Select a compact, interpretable closure that performs consistently across all flows.

### Tasks
1. **Law Selection Criteria**
   - Choose a law with:
     - `μ_question ≤ 64` bits (approximate upper bound).
     - `μ_total` at least 10× smaller than the blind baseline for each dataset.
     - Competitive or superior performance relative to Smagorinsky, AR, and NN baselines on both `μ_total` and predictive metrics.
     - Physically interpretable structure (e.g. cascade-like exponents).
      - Documented performance on a hold-out set, including at least one physically recognised diagnostic (e.g. energy spectrum slope or flux error).

2. **Freeze the Law**
   - Export the chosen law to `tools/turbulence_closure_v1.py` as executable code.
   - Document it in `docs/NUSD_Turbulence_Closure_v1.md` with equations, coefficients, interpretations, and a per-dataset results table.

---

## Phase 4 – Receipts, Reproduction, and Outreach

### Objective
Package the closure discovery so third parties can reproduce it end-to-end.

### Tasks
1. **Receipts and Verification**
   - Implement `tools/make_turbulence_closure_v1_receipt.py` and the companion verifier `tools/verify_turbulence_closure_v1_receipt.py`.
   - Add a `make turbulence-closure-v1` target that regenerates data (or downloads it), re-fits the law, writes the hash-chained receipt, and runs the verifier.

2. **One-Pager**
   - Create `docs/NUSD_Turbulence_Closure_OnePager.md` summarising:
     - The discovered law in plain language and equations.
     - Comparative `μ_total` and error metrics versus Smagorinsky and NN baselines.
     - Reproduction steps (`git clone`, `cd`, `make turbulence-closure-v1`).

---

## Phase 5 – Acceptance Criteria

The mission is complete when the following are all true:

1. `NUSD_Turbulence_Closure_v1.md` presents a single law with:
   - `μ_question ≤ 64` bits,
   - `μ_total` at least an order of magnitude below the blind baseline across all datasets,
   - `μ_total` competitive with or better than Smagorinsky and NN baselines,
   - Predictive errors (RMSE, flux/spectrum deviation) comparable to or better than the baselines.

2. The pipeline is reproducible via:
   ```bash
   make turbulence-closure-v1
   python3 tools/verify_turbulence_closure_v1_receipt.py \
       artifacts/turbulence_closure_v1_receipt.jsonl
   ```

3. A turbulence or ML practitioner can understand the law and its evidence by reading `NUSD_Turbulence_Closure_v1.md` and `NUSD_Turbulence_Closure_OnePager.md` without diving into the codebase.

---

## Notes for Agents
- Favour physically meaningful candidate terms to keep the law interpretable.
- Track all μ-ledger numbers carefully; every comparison in the documentation must be reproducible by the verifier.
- When in doubt, bias toward smaller symbolic structures even if it means a tiny increase in residual error—the mission emphasises compactness and clarity.
