# Verifying a multi-domain NUSD receipt

This guide explains how to regenerate and audit the receipts emitted by
`tools/make_nusd_receipt.py`. Each receipt is a JSONL file containing a
hash-chained trace, a μ/MDL ledger, the Landauer bound, optional
calibration metadata, and an HMAC signature.

## Generating fresh receipts

To generate all four domains (lattice, Tseitin, automaton, turbulence)
and leave the outputs in `artifacts/`, run:

```sh
make nusd
```

Every run prints the location of the written receipt. Domain-specific
parameters can be overridden on the command line; for example:

```sh
python3 tools/make_nusd_receipt.py --domain automaton --automaton-rule 90 \
    --automaton-width 48 --automaton-steps 40 --output artifacts/nusd_rule90.jsonl
```

All variants accept `--temperature`, `--epsilon-bits`, and
`--calibration-file` so you can change the ambient assumptions or supply
an independent μ↔joule dataset.

## Verifying a receipt

Use `tools/verify_nusd_receipt.py` to replay the chain and recompute the
bound:

```sh
python3 tools/verify_nusd_receipt.py artifacts/nusd_receipt.jsonl
```

The verifier performs the following checks:

1. Recomputes every `crypto_hash` entry and validates the hash chain.
2. Recomputes the HMAC signature using the baked-in key.
3. Replays the domain-specific inference to reconstruct `mdl_bits`.
4. Recomputes the Landauer bound (and the calibration overlay if the
   dataset is present) and checks the μ-question/answer split.
5. Verifies the recorded generator SHA-256 and domain parameters.

By default the verifier expects the calibration dataset recorded in the
summary to be available on disk. Use `--skip-calibration` if you want to
skip that check, or `--calibration-file <path>` to point at a different
power log for the replay.

A successful run prints `Receipt verification succeeded`. Any mismatch
results in a descriptive error and a non-zero exit code.
