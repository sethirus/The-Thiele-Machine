# Partition Collapse Regression

This document records the results of running `experiments/partition_collapse_test.py` to confirm the blind-mode fallback when partitions offer no advantage.

## Command

```
python3 experiments/partition_collapse_test.py --help
```

## Observed Behavior

* The test suite generated 24 adversarial or structure-free instances.
* One case (`fully_connected_n8`) showed the sighted solver **slower** than the blind solver, demonstrating that discovery cost is charged and trivial partitions are used when structure is absent.
* Four uniform-random or highly symmetric cases produced only negligible advantage (<20%), consistent with collapsing toward the blind baseline.
* Aggregate ratios spanned `0.492×`–`130.745×` (blind/sighted), with falsification evidence logged in `experiments/claude_tests/partition_collapse_results.json`.

## Artifacts

* Raw results: `experiments/claude_tests/partition_collapse_results.json`
* Console run: see terminal transcript in this pull request notes.

These artifacts can be re-generated at any time by re-running the command above; no manual fixtures are required.
