# REPORT_1: μ predicts SAT difficulty (Z3)

This report is generated from the preregistered pipeline described in [PREREG.md](../../PREREG.md).

## Artifacts

- Instances: [benchmarks/mu_sat_difficulty/instances/](instances/)
- Frozen metadata: [benchmarks/mu_sat_difficulty/instances/meta.jsonl](instances/meta.jsonl)
- μ predictions (solver-free): [benchmarks/mu_sat_difficulty/predictions.jsonl](predictions.jsonl)
- Z3 runtimes: [benchmarks/mu_sat_difficulty/z3_results.csv](z3_results.csv)
- Metrics summary: [benchmarks/mu_sat_difficulty/analysis.json](analysis.json)
- Plot: [benchmarks/mu_sat_difficulty/fig_mu_vs_runtime.png](fig_mu_vs_runtime.png)

## Reproduction

- `python tools/mu_sat_difficulty_scale.py run --no-solve`

Staged:
- `python tools/mu_sat_difficulty_scale.py generate`
- `python tools/mu_sat_difficulty_scale.py predict --no-solve`
- `python tools/mu_sat_difficulty_scale.py solve --timeout 10`
- `python tools/mu_sat_difficulty_scale.py analyze`

## Current run summary (smoke test)

The current committed artifacts are from a *small* sanity run (16 instances; sizes 15/20; 2 seeds; timeout 5s; hard threshold 0.2s). Results are in [benchmarks/mu_sat_difficulty/analysis.json](analysis.json).

Notes:
- Because this is intentionally tiny, the prereg PASS thresholds are not expected to hold yet.
- The pipeline enforces **NO_SOLVE** during μ extraction by forbidding importing `z3` in the prediction stage.
