# SQL Case Study

The SQL microbenchmarks form the highest-contrast slice of the cross-domain counterexample hunt. They stress test the sighted/blind separation by introducing schema-aware joins that explode combinatorially when structure is hidden.

## Dataset

- **Source:** Synthetic SQL workloads generated alongside the compression and LDPC domains via `python -m tools.counterexample_hunt`.
- **Protocols:** sighted, blind, destroyed (control).
- **Ledger location:** `proofpack/cross_domain/{sighted,blind,destroyed}/cross_domain_steps.jsonl` inside `artifacts/experiments/counterexample-hunts/`.

## Observed metrics

- **Average runtime ratio (blind/sighted):** 7.989×.
- **Mean blind runtime:** 85.29 units across all domains; sighted runs average 14.23 units.
- **Modules per trial:** 14; each module appends a new join or predicate.

The domain ratio and global means are recorded in `artifacts/experiments/counterexample-hunts/analysis/summary.json`.

## Methodology

1. Each sighted trial receives oracle access to the canonical schema partitions and therefore accrues μ at a flat rate even as module depth rises.
2. Blind trials must rediscover the same partitions through exponential exploration. Destroyed controls randomise module assignments to demonstrate that structure, not hyperparameter luck, drives the gap.
3. Runtime ratios are computed by pairing blind and sighted cumulative runtimes per `(domain, seed, trial_id)` and averaging within the SQL subset.

## Interpretation

- SQL shows the sharpest separation: the blind solver spends nearly 8× more runtime to answer the same canonical queries, satisfying the falsifiable prediction for deep compositions.
- The high gap further validates the updated `tools.falsifiability_analysis` heuristic: it now prioritises the most informative proofpack instead of the earlier shallow slice that left the dashboard exposed.
- Because the sighted ledger maintains μ totals around 3.4 bits, any future dataset that pushes blind runs below a 1× ratio would constitute a serious counterexample.

## Next steps

- Apply the pipeline to community-provided SQL benchmarks (e.g., TPC-H, IMDB subsets) once available through the external dataset programme.
- Capture ΔAIC and slope diagnostic plots inside the proofpack to quantify how exponentials dominate over polynomials for the blind solver.
- Explore adaptive hints: gradually revealing schema fragments should map out the phase transition between sighted and blind performance.
