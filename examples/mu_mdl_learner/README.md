# µ-MDL Learner

Toy structural learner over the extracted Thiele VM. Tries to discover the
period of a bit stream by issuing LASSERT calls and measuring µ paid.

The period-k predicate is encoded as a SAT formula
(`x_i ↔ x_{i+k}` for each i), with the stream itself supplied as the
satisfying assignment. LASSERT charges `hw_flen * 8 + (delta + 1)` µ on
every probe, success or failure.

## Files

| File | What it is |
|---|---|
| `streams.py` | Labeled bit-stream generator. |
| `encoding.py` | Build the period-k LASSERT program. |
| `brute_force.py` | Ascending-scan learner. |
| `compositional.py` | History-biased learner with divisor refinement. |
| `mdl.py` | Bits-of-description scoring. |
| `eval.py` | Eval harness with random baseline. |
| `m1_sanity.py` ... `m5_generalize.py` | Runnable drivers. |

## Run

From the repo root:

```bash
python3 -m examples.mu_mdl_learner.m1_sanity
python3 -m examples.mu_mdl_learner.m2_eval
python3 -m examples.mu_mdl_learner.m3_mdl
python3 -m examples.mu_mdl_learner.m4_curriculum
python3 -m examples.mu_mdl_learner.m5_generalize
```

Each driver prints its own results table.

## Note on the substrate

Periodicity needs negative literals in CNF. The OCaml-extracted
runner's `word32_to_signed` uses a direct `Extract Constant` directive
(in `coq/Extraction.v`) for the two's-complement conversion; the
default `Z.of_nat` extraction path would stack-overflow on
wrap-around values like `4294967295` (DIMACS `-1`). Regression test in
`tests/test_lassert_negative_literals.py`. Rebuild the runner with
`make ocaml-runner` if you change the extraction.
