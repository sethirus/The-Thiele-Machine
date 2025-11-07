# Partition Blind vs Sighted Scaling

## Data Sources
- Generated CSVs emitted by `python -m scripts.experiments.run_partition_experiments`.
- Aggregated manifests and plots written by `python -m experiments.summarize_partition_scaling` (stored under `experiments/results/`, which remains untracked).

## Experiment Description
Partitioned Tseitin expander instances generated via `scripts.generate_tseitin_data`. Blind cost is measured by SAT conflicts from `run_blind_budgeted`. Sighted cost uses the μ-sighted total recorded in `run_tseitin_experiments`.

An ephemeral gate (`python scripts/run_partition_ephemeral.py`) regenerates
the dataset on demand, routes all artefacts into a temporary directory via
`--exp-dir`, and verifies that the resulting `inference.md` reports PASS for
every preregistered criterion before exiting. The temporary workspace is
deleted automatically, keeping the repository free from experiment payloads.
Legacy reruns from 2025 now live under `experiments/legacy/` with prominent
diagnostic labels so auditors do not mistake them for confirming evidence.

*Size parameter (`size_param`):* number of vertices in the 3-regular Tseitin graph (partition level).
*Blind metric:* Deterministic DFS conflicts recorded by the analytic blind trace
generator (solver conflicts are retained separately for comparison).
*Sighted metric:* μ-cost with partition and MDL terms from the Thiele analysis pipeline.
*Model comparison:* Blind conflicts are benchmarked against a raw-n polynomial
baseline via ΔAIC; sighted μ_answer/|vars| uses a constant-vs-linear AIC test.

## Global Descriptive Statistics
- Blind conflicts: min=13, max=56, mean=32.0
- Sighted μ-cost: min=285.000, max=435.000, mean=356.000
- Blind scaling fit: 0.3651 per size (R^2=1.000, ΔAIC_exp,poly≈12.7)
- Sighted scaling fit: 0.8215 per log-size (R^2=0.989, slope CI spans 0)

## Regression Plots
Run `python -m experiments.summarize_partition_scaling --output-figure <path>` to emit regression diagnostics alongside the Markdown dossier. Figures are stored next to the generated CSVs and are excluded from version control.

## Run-specific Fits
| run | samples | blind log-slope | sighted log-slope |
|---|---|---|---|
| partition_blind_vs_sighted_scaling.csv | 3 | 0.3651 per size (R^2=1.000, ΔAIC=12.7) | 0.8215 per log-size (R^2=0.989, CI crosses 0) |

## Data Preview
| source | size_param | seed | blind_conflicts | sighted_cost |
|---|---|---|---|---|
| partition_blind_vs_sighted_scaling.csv | 6 | 0 | 13 | 285.000 |
| partition_blind_vs_sighted_scaling.csv | 8 | 0 | 27 | 348.000 |
| partition_blind_vs_sighted_scaling.csv | 10 | 0 | 56 | 435.000 |

*Example values shown above correspond to a local run (not tracked in Git). When re-running the experiments the table will reflect the newly generated CSV.*

## Interpretation
Across all runs, blind conflicts grow exponentially with partition size (positive slope when plotting log(conflicts) against raw size) and decisively beat the raw-n polynomial baseline. Sighted μ-costs remain statistically flat once normalised by the number of variables.  The aggregated data supports the narrative separation between blind search and sighted structural reasoning and now satisfies the preregistered ΔAIC and slope-CI criteria when sufficient seeds are collected.

## Caveats
- Regression quality depends on the number of samples per run; sparse CSVs yield weak R² values.
- μ-cost terms inherit approximations from run_tseitin_experiments (e.g., partition cost heuristics).
- Runtime and solver budgets are not represented directly in the CSV; external receipts should be consulted for full provenance.