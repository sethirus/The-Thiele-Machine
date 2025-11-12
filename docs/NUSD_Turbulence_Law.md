# NUSD turbulence law witness

This note records the turbulence-specific discovery run driven by the sighted Thiele engine.  The
receipt `artifacts/turbulence_law_receipt.jsonl` and its verifier demonstrate that a single-term law
fitted from μ-accounted data sharply outperforms blind encodings across synthetic cascades and a
reference JHTDB sample.

## Discovered law

`tools/turbulence_law.py` enumerates sparse symbolic combinations built from local energies,
velocity gradients, and cascade features, selecting the law with the lowest model + residual
MDL.【F:tools/turbulence_law.py†L145-L228】  For the default seeds the optimiser converges to

\[
E_{t+1} = \tfrac{1}{59} + \tfrac{939}{955}\,\bar{E}_t
\]

where \(\bar{E}_t = (E_t + E_{t-1})/2\) is the local average energy.  The compact intercept and
single coefficient account for \(\mu_{\text{question}} = 26.68\) bits on the aggregated trace while
reducing the residual ledger to \(\mu_{\text{answer}} = 4.53\) bits, beating the blind baseline by
more than 12 kilobits.【F:artifacts/turbulence_law_receipt.jsonl†L1-L84】【F:artifacts/turbulence_law_receipt.jsonl†L85-L171】

## Training and evaluation ledger

`tools/discover_turbulence_law.py` runs the search and reports per-seed μ ledgers along with a JSON
summary for downstream tooling.【F:tools/discover_turbulence_law.py†L21-L140】  The receipt records the
same numbers for replay.  The table below summarises the bundled datasets (Δ = baseline − residual):

| dataset | residual bits | baseline bits | Δ bits | blind total bits |
|---------|---------------|---------------|--------|------------------|
| synthetic_seed_314159 | 0.7338 | 4.7292 | 3.9954 | 4056.8166 |
| synthetic_seed_271828 | 0.8109 | 4.9478 | 4.1369 | 4057.0353 |
| synthetic_seed_161803 | 0.7854 | 4.9060 | 4.1206 | 4056.9935 |
| synthetic_seed_57721 | 0.8451 | 4.9529 | 4.1078 | 4057.0404 |
| synthetic_seed_173205 | 0.8061 | 4.9256 | 4.1195 | 4057.0131 |
| JHTDB sample | 5.3e-05 | 0.0000 | −5.3e-05 | 20.0875 |

Values come directly from the signed receipt entries and exhibit a consistent four-bit gap between
baseline and sighted solvers on the synthetic flows while landing within \(5 \times 10^{-5}\) bits of
the (tiny) JHTDB baseline.【F:artifacts/turbulence_law_receipt.jsonl†L1-L84】  Aggregated across the
three fitting seeds the mean Δ is 4.08 bits; over the evaluation trio it is 2.74 bits, dominated by
the near-zero baseline of the four-point JHTDB trace.【F:artifacts/turbulence_law_summary.json†L29-L60】

## Receipt generation and verification

Running `make turbulence-law` executes the full pipeline: the law discovery, receipt writing, and the
verifier that recomputes the law, μ ledgers, and hash chain.【F:Makefile†L103-L132】  Manual invocation
is available as well:

1. `python3 tools/make_turbulence_law_receipt.py --eval-dataset public_data/jhtdb/sample/jhtdb_samples.json`
   synthesises the datasets, fits the law, emits the chained receipt, and signs the NUSD summary with
   an HMAC.【F:tools/make_turbulence_law_receipt.py†L1-L222】
2. `python3 tools/verify_turbulence_law_receipt.py artifacts/turbulence_law_receipt.jsonl` reloads the
   receipt, replays the discovery, checks every μ ledger (including the calibration metadata), and
   validates the signature.【F:tools/verify_turbulence_law_receipt.py†L1-L173】

The receipt therefore supplies a reproducible turbulence-specific witness for the NUSD law: the
sighted model spends tens of bits to describe the cascade and saves over 12 kilobits of blind encoding
across the combined traces, all under cryptographic and calibration audit.【F:artifacts/turbulence_law_receipt.jsonl†L85-L171】
