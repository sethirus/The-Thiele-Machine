# Honest Tseitin Benchmark

Generated: 2025-09-18T13:21:39Z
Git commit: 7d5195690e8eb66a38a1b665c8a45578aae25134

| n | seed | edges | baseline status | baseline s | baseline μ | checked | thiele status | thiele s | thiele μ | time/μ (s) | runtime ratio |
|---|------|-------|-----------------|------------|------------|---------|---------------|----------|----------|------------|--------------|
| 6 | 0 | 9 | unsat | 0.001219 | 0 | 512 | unsat | 0.000073 | 12 | 0.000006 | 16.75 |
| 6 | 1 | 9 | unsat | 0.001642 | 0 | 512 | unsat | 0.000028 | 11 | 0.000003 | 58.67 |
| 6 | 2 | 9 | unsat | 0.001274 | 0 | 512 | unsat | 0.000024 | 14 | 0.000002 | 52.95 |
| 8 | 0 | 12 | unsat | 0.011765 | 0 | 4096 | unsat | 0.000044 | 21 | 0.000002 | 266.20 |
| 8 | 1 | 12 | unsat | 0.011267 | 0 | 4096 | unsat | 0.000057 | 14 | 0.000004 | 195.95 |
| 8 | 2 | 12 | unsat | 0.013069 | 0 | 4096 | unsat | 0.000066 | 23 | 0.000003 | 196.63 |
| 10 | 0 | 15 | unsat | 0.108016 | 0 | 32768 | unsat | 0.000108 | 21 | 0.000005 | 1003.58 |
| 10 | 1 | 15 | unsat | 0.102571 | 0 | 32768 | unsat | 0.000071 | 25 | 0.000003 | 1439.57 |
| 10 | 2 | 15 | unsat | 0.095398 | 0 | 32768 | unsat | 0.000077 | 23 | 0.000003 | 1239.33 |

## Summary

Instances: 9
Average runtime – baseline: 0.038469s, Thiele: 0.000061s
Median runtime – baseline: 0.011765s, Thiele: 0.000066s
Average runtime ratio (baseline/thiele): 496.62
Average μ-discovery (Thiele): 18.22
Median μ-discovery (Thiele): 21.00
Average time saved per μ-bit: 0.001738s

Baseline exhaustive search accumulates zero μ because it never learns a structure; the Thiele-style solver pays a finite μ-discovery cost equal to its GF(2) row operations while shrinking runtime exponentially.
