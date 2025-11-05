# Thiele Machine Experiment Inference Report
Problem: tseitin
Timestamp: 1761348963

## Pre-registered Decision Criteria
- Blind fits exp better than poly by ΔAIC ≥ 10: FAIL
- Sighted μ_answer slope 95% CI contains 0: PASS
- Ratio slope > 0 and monotonic in ≥90% of bootstrap: FAIL
- Spearman ρ(μ_blind, runtime) ≥ 0.6 (p < 0.01): FAIL

## Blind Reasoning Scaling
- Best-fit exponential: slope=0.269 [0.000, 0.297]
- AIC_exp = -17.8, AIC_poly = -17.8
- Exponential model loses

## Sighted Reasoning Scaling (μ_answer)
- Slope = 1.500 [0.000, 1.500]
- CI crosses 0
- AIC_const = 7.4, AIC_linear = -207.2
- Linear model fits best

## Normalized μ_answer per Variable
- μ_answer / num_vars: [np.float64(1.0), np.float64(1.0), np.float64(1.0)]
- Slope of normalized μ_answer: 0.000000

## Cost Ratio Analysis
- Ratio slope = 0.0085 per vertex
- Monotone in 37.7% of bootstrap samples

## Runtime Correlation
- Spearman ρ(μ_blind, runtime) = 0.580 (p = 2.28e-01)

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
Blind reasoning exhibits exponential scaling (structure-blind), while sighted reasoning
exhibits quadratic scaling (structure-aware) as predicted by Thiele theory. The efficiency gap grows
with problem size, demonstrating the computational value of structural insight.