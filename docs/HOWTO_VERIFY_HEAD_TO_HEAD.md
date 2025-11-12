# Verifying the turbulence head-to-head receipt

This guide explains how to reproduce and audit the turbulence sighted-vs-blind
comparison that underpins the Phase 2 "Head-to-Head" challenge.

## Prerequisites

* Python 3.10 or newer with the repository's dependencies installed (`pip install -r requirements.txt`).
* The calibration dataset `mu_bit_correlation_data.json` (included at the repo root).
* Optional but recommended: the Coq/Yosys toolchain from the Phase 1 setup if you
  intend to run the wider proofpack pipeline.

## Regenerating the receipt

```
make headtohead
```

This target synthesises the shared turbulence dataset, runs both the sighted
(AR(1) law inference) and blind (per-sample encoding) solvers, emits the
append-only receipt `artifacts/turbulence_head_to_head.jsonl`, and immediately
replays the verification script against the freshly generated artifact.

The make target passes the default parameters:

* `seed = 314159`
* `samples = 96`
* `grid = 32`
* `temperature = 300 K`
* `blind_bits_per_sample = 16`

You can override these by invoking the generator script directly:

```
python3 tools/make_turbulence_head_to_head.py --seed 123 --samples 128 --blind-bits-per-sample 12
python3 tools/verify_turbulence_head_to_head.py artifacts/turbulence_head_to_head.jsonl
```

## What the verifier checks

The verifier recomputes every invariant recorded in the summary:

1. Replays the deterministic turbulence trace and confirms the SHA-256 digest.
2. Recomputes the baseline μ accounting and both solver MDL profiles.
3. Reconstructs the NUSD bound (μ_question + μ_answer − ε) for each solver and
   confirms the reported Landauer work floors.
4. Validates the hash chain and HMAC signature over the summary entry.
5. Confirms that the reported μ-gap (`blind − sighted`) matches the recomputed
   values to within `1e-6` bits.

Any discrepancy raises an exception and exits with a non-zero status so that CI
systems can treat the artifact as untrusted.

## Downstream use

The resulting receipt is consumed by the upcoming proofpack bundles for Phase 3.
Because it is deterministic and self-verifying, third parties can rerun the
entire head-to-head comparison with a single command and confirm the blind path
necessarily pays the larger μ cost.
