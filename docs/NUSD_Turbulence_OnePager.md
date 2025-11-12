# A Sighted Machine Discovers a Turbulence Law

**The law.**  The sighted MDL search settles on a single symbolic rule across synthetic cascades and
two JHTDB excerpts:

\[
E_{t+1} = E_t.
\]

The cascade term is present in the hypothesis class but its coefficient quantises to zero at the
1/64 grid, so the final rule is a pure energy conservation update.

**Why it matters.**  Blind encoders spend 16 bits per sample before modelling residuals; the receipts
show that the sighted law pays only 13.4 μ-bits to describe the rule and less than 0.013 residual
bits per DNS sample. The resulting μ-gaps are enormous:

- 6.1 kilobits of μ-gap on each synthetic cascade;
- 1.48 kilobits on isotropic1024;
- 1.22 kilobits on channel-flow centreline snapshots.

Every figure is verifiable: the receipt (`artifacts/turbulence_law_v2_receipt.jsonl`) is hash-chained,
HMAC-signed, and the verifier recomputes the residuals, baselines, and MDL ledger.

**Reproduce in one command.**

```
make turbulence-law-v2
```

This runs the discovery search, emits the signed receipt, and executes
`tools/verify_turbulence_law_v2_receipt.py` so the ledger can be audited immediately.
