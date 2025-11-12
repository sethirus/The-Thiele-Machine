# NUSD Turbulence Benchmark

The turbulence benchmark exercises the sighted discovery engine on a set of synthetic cascades and
real direct numerical simulation (DNS) traces. Each target is accompanied by a μ-ledger so the
No Unpaid Sight Debt (NUSD) inequality can be checked end to end.

## Datasets

| dataset path | description | frames × samples | series samples | SHA-256 digest |
| --- | --- | --- | --- | --- |
| `public_data/jhtdb/isotropic1024_coarse.json` | coarse lattice of the JHTDB isotropic1024 run (synthetic reconstruction) | 96 × 48 | 96 | `9c0a7eb00dbb5097d4d830ec9082eba0f756bd062d0a9b9b91157c02a9da35b9` |
| `public_data/jhtdb/channel_flow_centerline.json` | centre-line streaks extracted from the JHTDB channel-flow dataset | 80 × 40 | 80 | `82be04d895f458dcdf4bb858c4ad749b82066437ea1a275225ea9c774655fa78` |
| `public_data/jhtdb/sample/jhtdb_samples.json` | published JHTDB sample packet (four frames) | 4 × 64 | 4 | `25a35d7afba1b19cac67ab1fd356af25f15889940acb4e0f3b514d7b2091819f` |

Synthetic training and validation cascades are generated with the deterministic seeds
`[314159, 271828, 161803]` for fitting and `[57721, 173205]` for evaluation. Each synthetic series
contains 384 samples unless the caller overrides `--samples`.

## Baselines

Each receipt reports the following baselines for every bundle:

- **Blind encoder:** constant bits-per-sample expenditure with μ-question cost `n · b + log₂(1 + b)`
  and μ-answer equal to the baseline residual MDL.
- **AR(1) and AR(2):** fitted autoregressive models with μ-question computed from the rational
  coefficients returned by the least-squares solve.
- **Smagorinsky-like closure:** linear combination of the instantaneous energy and squared gradient,
  mirroring a static eddy-viscosity closure.

All baselines are expressed as triples `(μ_question_bits, μ_answer_bits, μ_total_bits)` with RMSE and
MAE so that the μ-gap and classical error gap can be compared directly to the sighted law.

## Metrics

For every series the sighted discovery pipeline records:

- `μ_question_bits` – structure penalty + coefficient code length of the symbolic law;
- `μ_answer_bits` – MDL of the residuals (`log₂(1 + Σ r²)`);
- `μ_total_bits` – `μ_question_bits + μ_answer_bits - ε`, with ε taken from the receipt;
- `rmse` and `mae` – standard error metrics on the `E_{t+1}` predictions;
- `spectrum_error` – mean absolute difference between the real Fourier spectra of the forecast and
  reference trajectories;
- `mu_gap_bits` – improvement in μ-answer over the baseline mean predictor.

Landauer work bounds are derived from `μ_total_bits` at the specified temperature (default 300 K)
using the project-wide calibration dataset `mu_bit_correlation_data.json` when present.

## Reproduction

```
make turbulence-law-v2
python3 tools/verify_turbulence_law_v2_receipt.py artifacts/turbulence_law_v2_receipt.jsonl
```

The `make` target regenerates the discovery, emits a new receipt, and checks the μ-ledger. The
verifier recomputes every metric, recomputes the hash chain, and validates the HMAC signature so the
artifact is audit-ready.

For the closure witness, run:

```
python3 tools/make_turbulence_closure_v1_receipt.py
python3 tools/verify_turbulence_closure_v1_receipt.py
```

The closure receipt (documented in `docs/NUSD_Turbulence_Closure_v1.md`) records the symbolic
gradient law, the per-bundle μ-ledgers, and the signed summary for the same training and evaluation
bundles.【F:docs/NUSD_Turbulence_Closure_v1.md†L1-L32】
