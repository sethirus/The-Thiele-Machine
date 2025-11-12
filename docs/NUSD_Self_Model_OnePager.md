# A Sighted Machine Discovers Laws About Itself

## What happened
- Enabled the Thiele VM’s trace mode and ran four canonical workloads (idle pulses, partition churn,
  Tseitin proof search, and turbulence statistics) to collect JSONL self-traces with SHA-256 digests
  and μ-ledger snapshots.【F:artifacts/self_traces/self_trace_index.json†L1-L32】
- Fed those traces into the NUSD structural modeler, which searched symbolic hypotheses and found a
  single dominant coefficient: `MDLACC` steps contribute 7.142857 μ-bits each to the ledger.【F:tools/self_model_v1.py†L58-L120】
- Packaged the result as a signed receipt showing a 187.05-bit μ-gap versus blind logging while the
  blind baseline spends 264 bits on the same traces.【F:artifacts/self_model_v1_summary.json†L1-L28】【F:artifacts/self_model_v1_receipt.jsonl†L1-L6】

## Snapshot
| workload | blind μ_total (bits) | μ_total (bits) | μ_gap (bits) |
|----------|----------------------|----------------|--------------|
| idle | 120.000 | 36.328 | 83.672 |
| partition | 64.000 | 26.792 | 37.208 |
| proof | 32.000 | 7.431 | 24.569 |
| turbulence | 48.000 | 6.398 | 41.602 |
| **all** | 264.000 | 76.949 | 187.051 |

## Reproduce it yourself
```bash
make self-model-v1
python3 tools/verify_self_model_v1_receipt.py artifacts/self_model_v1_receipt.jsonl
```
The first command regenerates traces (or refreshes them), rediscovers the self-law, and writes the
receipt; the second recomputes the ledger and validates the HMAC-signed chain.【F:Makefile†L130-L136】【F:tools/verify_self_model_v1_receipt.py†L20-L95】
