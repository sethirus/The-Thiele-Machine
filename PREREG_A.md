# PREREG_A: µ-term Landauer-class bound (public data only)

Date (UTC): 2025-12-18

Goal
- Produce and test a parameter-free lower bound on erasure work of the form:
  - ⟨W⟩/kT ≥ (information removed in nats) + extra_term_over_kT(µ, protocol)
  - extra_term_over_kT = 0 in the reversible/ideal limit; >0 otherwise.

Scope
- Uses digitized numeric points from published experimental curves.
- Does NOT download or redistribute paper PDFs.

## Locked data sources

Datasets are represented as CSV files in DATA_A/ with provenance fields.

Locked source identifiers (human labels only; no paper text embedded):
- JunGavrilovBechhoefer2014_arXiv1408.5089
- ProesmansEhrichBechhoefer2020_arXiv2006.03242

Optional (coefficient-only rows):
- ProesmansEhrichBechhoefer2020_arXiv2006.03242_SI

## Locked ingestion schema

Each DATA_A/*.csv row must include:
- paper_id, figure_id, dataset_id
- value_kind (one of: work_over_kT | a_coeff)
- tau_unit (one of: s | D_tau_over_Var)
- tau_s (cycle time; units determined by tau_unit)
- work_over_kT (dimensionless; meaning depends on value_kind)
- work_err_over_kT (dimensionless; may be empty)
- info_bits_removed (bits)

Notes:
- If value_kind=work_over_kT: work_over_kT is ⟨W⟩/kT and tau_unit must not be 'none'.
- If value_kind=a_coeff: work_over_kT stores the dimensionless coefficient a in (W-ln2)/kT = a * Var/(D*tau).

Unit-gated tightening (fail-closed):
- Tightening is *unit-gated*: the finite-time tightening term is only claimed when `tau_unit = D_tau_over_Var`.
- For `tau_unit in {s, tau_over_tau0}`, the run remains evaluable and checks the baseline Landauer inequality, but treats the tightening term as not applicable (i.e., µ-bound is set to Landauer for these rows).
- Any `tau_unit` outside the locked allowlist (s | tau_over_tau0 | D_tau_over_Var | none) is rejected during ingestion (run FAIL).

## Locked split / tuning policy

Two allowed modes (chosen at init time and bound into MANIFEST_A.json):
- fit_none (default): no fitting; all points are test.
- fit_global_on_one_dataset: fit exactly one global multiplicative scale constant on one dataset_id, then evaluate on all others.

No dataset-specific tuning is allowed.

## Locked model surface

The prereg harness treats these as the locked “theory code”:
- physics/landauer/mu_models.py

Changing these files after init invalidates prereg unless a new output root is used.

## Primary metrics (PASS/FAIL)

Let bound µLB be computed by tools/prereg_a_landauer.py.

PASS requires both:
- Violation rate on holdout ≤ 5% outside stated error bars.
- Tightness: µLB strictly tighter than Landauer (µLB > Landauer by more than the effective ε) on ≥ 20% of holdout points.

Reporting requirements:
- The harness must report per-series metrics keyed by `(paper_id, figure_id, dataset_id, curve_id, tau_unit)`.
- It must also report `tighten_fraction_applicable_units`, which is the tighten fraction restricted to the tightening-applicable unit subset (`tau_unit=D_tau_over_Var`).

FAIL if:
- Any prereg guard fails (manifest/tool hash mismatch, missing receipts).
- Tightness only occurs in the calibration dataset (if using fit_global_on_one_dataset).

## Outputs (locked order)

1) benchmarks/mu_landauer_a/MANIFEST_A.json
2) benchmarks/mu_landauer_a/DATA_A_INDEX.json
3) benchmarks/mu_landauer_a/analysis_A.json

Note: all commands accept `--root ...` to run in a non-default output folder.

## One-command execution

- python tools/prereg_a_landauer.py init
- python tools/prereg_a_landauer.py ingest
- python tools/prereg_a_landauer.py analyze

## A0 calibration anchor (Jun vs Proesmans sanity)

Canonical A0 run folder:
- benchmarks/prereg_a_jun_proesmans_A0/

Expected behavior (must hold in `analysis_A.json`):
- Jun (`tau_unit = s`) is evaluable but does not tighten (tighten_fraction = 0.0 for Jun series).
- Proesmans (`tau_unit = D_tau_over_Var`) tightens (tighten_fraction = 1.0 for Proesmans series).
- All series have violation_fraction ≈ 0.0.

Reproduction (manifest-bound):
- python tools/prereg_a_landauer.py --root benchmarks/prereg_a_jun_proesmans_A0 init --sources JunGavrilovBechhoefer2014_arXiv1408.5089 ProesmansEhrichBechhoefer2020_arXiv2006.03242
- python tools/prereg_a_landauer.py --root benchmarks/prereg_a_jun_proesmans_A0 ingest --data-dir DATA_A
- python tools/prereg_a_landauer.py --root benchmarks/prereg_a_jun_proesmans_A0 analyze --data-dir DATA_A

Interpretation note:
- The global `tighten_fraction` can be diluted by non-applicable rows; use `metrics.applicability.tighten_fraction_applicable_units` to read tightening performance restricted to `tau_unit = D_tau_over_Var`.
