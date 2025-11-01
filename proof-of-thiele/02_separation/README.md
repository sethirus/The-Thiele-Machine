# Pillar 2 – Exponential separation on Tseitin expanders

The receipts under `experiments/20251101_070033_ci_fix/` contain a deterministic
sweep over odd-charge Tseitin formulas. Each run records:

- the blind Cadical conflicts (`mu_blind`),
- the sighted μ-payment (`mu_question + mu_answer`), and
- the linear answer-only μ budget recorded in the thesis table.

To replay the audit, execute:

```bash
make -C proof-of-thiele separation
```

This calls `validate_tseitin_scaling.py`, which loads the most recent
`tseitin_scaling_report_*.json` file and enforces the mechanical criteria that
witness the separation:

1. sighted μ increments form an increasing sequence (quadratic upper bound);
2. blind μ admits an exponential fit whose confidence interval stays strictly
   positive and whose R² exceeds 0.95;
3. the blind-to-answer ratio grows monotonically;
4. the runtime/μ Spearman correlation remains ≥ 0.8 with p ≤ 1e-6.

The script prints the exact partitions and μ-values used in the thesis and
raises on any violation, making the separation auditable in seconds.
