# Thiele Machine One-Hour Deliverable

## Real Question
Can the Thiele Machine recover integer-factor witnesses while reducing brute-force search work via structural (congruence) pruning?

## Real Result
- **N=3233**: recovered witness `53 × 61 = 3233`
  - blind checks: `52` -> structural checks: `17` (reduction `67.3%`)
  - candidate space: `55` -> `18` (reduction `67.3%`), structural μ-cost `144.0`
- **N=10403**: recovered witness `101 × 103 = 10403`
  - blind checks: `100` -> structural checks: `33` (reduction `67.0%`)
  - candidate space: `100` -> `33` (reduction `67.0%`), structural μ-cost `144.0`

## Why This Matters
- This is not a slide claim: the system produced concrete factor witnesses and audit artifacts.
- The run demonstrates a practical pattern: spend explicit structural μ-bits to shrink arithmetic search.
- The same execution stack is formally gated (`make proof-undeniable`) for Coq/Python/RTL alignment.

## What This Is / Is Not
- **Is:** a reproducible, verified structural-pruning engine that can cut search work on concrete instances.
- **Is not:** a proof of polynomial-time factoring or a break of production RSA cryptosystems.

## Reproduce
```bash
make proof-undeniable
python3 scripts/rsa_partition_demo.py --moduli 3233 10403 --analysis-bits 256 512 1024
python3 scripts/generate_impact_deliverable.py
```

Source artifact: `rsa_demo_output/analysis_report.json`
