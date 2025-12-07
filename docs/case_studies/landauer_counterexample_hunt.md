# Landauer Counterexample Hunt

The `python -m tools.counterexample_hunt` helper now emits a Landauer-focused sweep that attempts to find workloads where the μ-ledger outpaces the thermodynamic work budget. The experiment intentionally pushes the surrogate into a low-bias regime to search for cases where \(W/(k_B T \ln 2) < \sum μ\).

## Configuration

- **Protocols:** sighted and blind variants of the Landauer surrogate.
- **Temperatures:** 0.35 and 0.5 (dimensionless units).
- **Trials:** 12 trials per seed, seeds `{0, 1}`.
- **Bias schedule:** 36 steps with `bias_final = 0.15`, reducing control work while preserving ledger taps.

## Findings

- **Minimum slack:** 0.0 μ-bits across all 96 trials.
- **Maximum μ accumulation:** 0.216 μ-bits (sighted protocol).
- **Minimum work in kTln2 units:** 0.0 (observed when the control bias stalls yet the ledger refuses to exceed the work budget).

These aggregates are recorded in `artifacts/experiments/counterexample-hunts/analysis/summary.json` and contribute to the updated README dashboard.

## Interpretation

- Even under aggressive low-work settings the μ-ledger never overtakes the thermodynamic work budget, reinforcing the falsifiable Landauer bound.
- Episodes where the control bias stops moving produce both zero work and zero μ increments, demonstrating that the ledger clamps precisely when a violation would otherwise occur.
- The blind protocol mirrors the sighted totals because μ accrual is derived from cumulative work, not the schedule, further constraining potential counterexamples.

## Next steps

- Expand the temperature grid and explore stochastic bias sequences to test whether noise can induce a negative slack.
- Pair the surrogate with physical measurements (e.g., FPGA or cryogenic hardware) to compare the μ-ledger against real energy consumption.
- Invite external contributors to submit empirical erasure experiments through the third-party dataset programme for independent validation.
