# NUSD Turbulence Law v2

The second-generation turbulence witness searches a symbolic model across deterministic cascades
and two DNS extracts (JHTDB isotropic1024 and channel flow). The sighted search converges to a
minimal law

\[
E_{t+1} = E_t,
\]

i.e. energy is conserved step to step once the latent structure is revealed. The cascade-ratio term
is retained in the basis but its fitted coefficient is quantised to zero at the 1/64 resolution used
for the MDL ledger, confirming that it does not contribute under the best law.

## μ-ledger summary

The aggregated μ-question cost is `13.392` bits (structure + coefficients). The table below reports
the μ-answer, μ-total and reconstruction error metrics for each bundle that participated in fitting
or evaluation.

| series | μ_answer (bits) | μ_total (bits) | μ_gap vs blind (bits) | RMSE | spectrum error |
| --- | ---:| ---:| ---:| ---:| ---:|
| synthetic_seed_314159 | 6 088.721 | 6 102.113 | 6 088.721 | 3.71e-02 | 2.32e-01 |
| synthetic_seed_271828 | 6 088.843 | 6 102.235 | 6 088.843 | 3.92e-02 | 2.39e-01 |
| synthetic_seed_161803 | 6 088.828 | 6 102.221 | 6 088.828 | 3.84e-02 | 2.10e-01 |
| synthetic_seed_57721 | 6 088.816 | 6 102.209 | 6 088.816 | 3.87e-02 | 2.39e-01 |
| synthetic_seed_173205 | 6 088.845 | 6 102.237 | 6 088.845 | 3.91e-02 | 2.34e-01 |
| isotropic1024_coarse | 1 476.414 | 1 489.807 | 1 476.414 | 9.58e-03 | 2.32e-02 |
| channel_flow_centerline | 1 220.088 | 1 233.481 | 1 220.088 | 3.04e-04 | 1.31e-04 |

(Entries with zero samples, such as the four-frame JHTDB sample snippet, are excluded.)

The blind baseline assumes a fixed 16 bits per sample and therefore records multi-kilobit μ-question
costs even before residuals are considered. The sighted law collapses the residuals to sub-bit levels
while paying only 13.4 μ-question bits, producing ≥1.2 kilobit μ-gaps on the DNS data and ~6 kilobit
μ-gaps on the synthetic cascades.

## Reproduction

```
make turbulence-law-v2
python3 tools/verify_turbulence_law_v2_receipt.py artifacts/turbulence_law_v2_receipt.jsonl
```

The `make` target runs discovery, emits the hash-chained receipt, and reruns the verifier. The
verifier recomputes the μ-ledger, validates the signature, and checks each baseline so the witness is
fully auditable.
