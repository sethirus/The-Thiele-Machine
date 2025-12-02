# Thiele Machine Experiment Inference Report
Problem: tseitin
Timestamp: 1764639258

## Pre-registered Decision Criteria
- Blind fits exp better than poly by ΔAIC ≥ 10: FAIL
- Sighted μ_answer/|vars| slope 95% CI contains 0: PASS
- Ratio slope > 0 and monotonic in ≥90% of bootstrap: PASS
- Spearman ρ(μ_blind, runtime) ≥ 0.6 (p < 0.01): FAIL

## Blind Reasoning Scaling
- Raw blind μ (mean conflicts): [np.float64(68.0), np.float64(196.0)]
- Best-fit exponential: slope=0.529 [0.000, 0.529]
- AIC_exp = -117.7, AIC_poly = inf
- ΔAIC(exp, poly) = N/A
- Exponential model loses

## Sighted Reasoning Scaling (μ_answer per variable)
- Slope = 0.000 [0.000, 0.000]
- CI crosses 0
- AIC_const = inf, AIC_linear = inf
- Linear model fits best

## Answer μ per Variable
- μ_answer / num_vars: [np.float64(1.0), np.float64(1.0)]
- Slope of normalized μ_answer: 0.000000

## Cost Ratio Analysis
- Ratio slope = 4.3889 per vertex
- Ratio slope CI = [0.0000, 64.0000]
- Raw ratios (pre-smoothing): [7.555555555555555, 16.333333333333332]
- Monotone in 100.0% of bootstrap samples

## Runtime Correlation
- Spearman ρ(μ_blind, runtime) = -1.000 (p = nan)

## Threats to Validity
### Internal Validity
- **Solver Invariance**: Experiments use a single SAT solver (Kissat). Alternative solvers might exhibit different scaling behavior.
- **Random Seed Effects**: Limited seed sampling (0-9) may not capture full variability in problem generation.
- **Budget Sensitivity**: Fixed time budgets may not be optimal for all problem sizes; larger budgets could reveal different asymptotics.

### External Validity
- **Tseitin Family Specificity**: Results may not generalize beyond Tseitin constraint satisfaction problems.
- **Partition Strategy**: The specific partition algorithm may not be optimal for all problem structures.
- **Hardware Variability**: Runtime measurements depend on specific hardware; results may vary across systems.

### Construct Validity
- **μ Cost Metric**: The μ_spec v2.0 cost function may not perfectly capture computational complexity.
- **Exponential Fit Quality**: AIC comparisons assume model adequacy; poor fits could lead to incorrect conclusions.
- **Bootstrap Reliability**: Statistical inference relies on bootstrap resampling; small sample sizes may reduce precision.

## Conclusion
Only 2 of 4 criteria passed (missing 2). The evidence packet should be treated as diagnostic until new runs satisfy all pre-registered checks.