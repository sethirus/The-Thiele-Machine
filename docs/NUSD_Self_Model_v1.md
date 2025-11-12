# NUSD Self-Model v1

## Overview

`make self-model-v1` turns the Thiele VM on itself: the kernel emits compact JSONL traces for
canonical workloads, the NUSD structural modeler searches those traces for symbolic self-laws, and
the result is packaged as a signed receipt with a large μ-gap against blind logging.【F:tools/make_self_traces.py†L14-L193】【F:tools/make_self_model_v1_receipt.py†L20-L133】

## Self-trace dataset

Traces live under `artifacts/self_traces/` and are indexed by
`artifacts/self_traces/self_trace_index.json`.  Each entry records the workload, deterministic seed,
step count, and SHA-256 digest so the verifier can recompute the ledger from identical data.【F:artifacts/self_traces/self_trace_index.json†L1-L32】

| workload | steps | trace SHA256 | blind μ_total (bits) |
|----------|-------|--------------|----------------------|
| idle | 15 | `9d3539e295b9448b5002136ec9d40fc924546672e1884f0390730b6cfd9af537` | 120.000 |
| partition | 8 | `0e2a992ef949b0a8ece5cddf6fd9304d01251c01c242137c5e5f45c1f4e79280` | 64.000 |
| proof | 4 | `0881fa08b544ddfdbbbe0625c833d1860442339198abcdae6da4901bd248f172` | 32.000 |
| turbulence | 6 | `a5ec7e534d44637c02881fbac169f84b44ef546de6bd775be36255c92629a9c1` | 48.000 |

## Discovered self-law

The sighted search collapses the trace deltas to a single coefficient: every `MDLACC` step raises the
ledger by \(7.142857\) μ-bits on average, while other operations contribute only residual noise.  The
law is recorded as

\[
\Delta \mu_{\text{total}} = 7.142857 \cdot [\text{op} = \texttt{MDLACC}].
\]

The model costs 16 μ-question bits, the residual adds ≈61 μ-bits, and the total self-law ledger is
≈76.95 μ-bits, leaving a 187.05-bit gap against the blind 264-bit baseline.【F:artifacts/self_model_v1_summary.json†L1-L28】

## μ-ledger by workload

| workload | μ_question (bits) | μ_answer (bits) | μ_total (bits) | μ_gap (bits) | RMSE |
|----------|-------------------|-----------------|----------------|--------------|------|
| idle | 4.000 | 32.341 | 36.328 | 83.672 | 3.318 |
| partition | 4.000 | 22.804 | 26.792 | 37.208 | 5.051 |
| proof | 4.000 | 3.443 | 7.431 | 24.569 | 1.571 |
| turbulence | 4.000 | 2.411 | 6.398 | 41.602 | 0.660 |

Across the combined dataset the blind encoding spends 264 μ-bits, while the discovered law spends
76.95 μ-bits for the same predictive fidelity.【F:artifacts/self_model_v1_summary.json†L8-L25】

## Reproduce

```bash
make self-model-v1
python3 tools/verify_self_model_v1_receipt.py artifacts/self_model_v1_receipt.jsonl
```

Both commands regenerate (or refresh) the traces, recompute the self-law, and check the signed
receipt end to end.【F:Makefile†L130-L136】【F:tools/verify_self_model_v1_receipt.py†L20-L95】
