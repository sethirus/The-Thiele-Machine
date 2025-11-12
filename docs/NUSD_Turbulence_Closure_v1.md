# NUSD Turbulence Closure v1

The first closure witness fits a symbolic model to turbulent energy gradients
across deterministic cascades and two DNS extracts. The greedy search under the
NUSD MDL objective selects a pure intercept, so the closure predicts that the
next-step gradient vanishes once the latent structure is exposed:

\[
\nabla E_{t+1} = 0.
\]

The model complexity is one μ-bit while the aggregated residual ledger records
1.4208 μ-bits, yielding a 2.4208 μ-bit total.【F:artifacts/turbulence_closure_v1_receipt.jsonl†L9-L9】

## μ-ledger by dataset

| series | μ_question (bits) | μ_answer (bits) | μ_total (bits) | blind μ_total (bits) | RMSE |
| --- | ---:| ---:| ---:| ---:| ---:|
| synthetic_seed_314159 | 1.0 | 0.6073 | 1.6073 | 6084.6930 | 3.71×10⁻² |
| synthetic_seed_271828 | 1.0 | 0.6645 | 1.6645 | 6084.7498 | 3.92×10⁻² |
| synthetic_seed_161803 | 1.0 | 0.6420 | 1.6420 | 6084.7277 | 3.84×10⁻² |
| synthetic_seed_57721 | 1.0 | 0.6500 | 1.6500 | 6084.7359 | 3.87×10⁻² |
| synthetic_seed_173205 | 1.0 | 0.6611 | 1.6611 | 6084.7466 | 3.91×10⁻² |
| isotropic1024_coarse | 1.0 | 0.0121 | 1.0121 | 1476.0993 | 9.58×10⁻³ |
| channel_flow_centerline | 1.0 | 1.0×10⁻⁵ | 1.0000 | 1220.0875 | 3.04×10⁻⁴ |

The blind baselines spend ≥1.2 kilobits per dataset, so the closure achieves a
μ-gap of at least 1.2 kilobits against the blind encoding on every bundle.【F:artifacts/turbulence_closure_v1_receipt.jsonl†L1-L6】【F:artifacts/turbulence_closure_v1_receipt.jsonl†L5-L8】【F:artifacts/turbulence_closure_v1_receipt.jsonl†L9-L9】

## Reproduction

```
python3 tools/make_turbulence_closure_v1_receipt.py
python3 tools/verify_turbulence_closure_v1_receipt.py
```

The first command regenerates the discovery, writes the hash-chained receipt,
and stores a summary snapshot. The verifier recomputes the law using the stored
parameters, validates the hash chain, and checks the HMAC signature.
