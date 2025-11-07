# Audit conclusion — 2025-11-07

> **Superseded for current code by [`AUDIT_STATUS_20251107_UPDATED.md`](AUDIT_STATUS_20251107_UPDATED.md).** Historical snapshot preserved for transparency.

This snapshot records the findings from the 2025-11-07 narrative review. It remains untouched so reviewers can see what prompted the remediations.

## Summary of findings (historical)

- Partition experiment reruns failed three of four preregistered criteria, so the sighted vs. blind separation was not demonstrated under audit controls.
- `the_final_proof.py` did not reach the advertised fixed point; the executable halted after reporting that the hash balance was unreachable.
- Operation Cosmic Witness relied on a brittle single-feature threshold and stretched the marketing language toward cosmological prediction.
- The Ed25519 kernel signing key was published in plaintext (`kernel_secret.key`), rendering past signatures unauthentic.

These notes remain valid for the archived experiment bundles and historical commits predating the remediations summarised in `AUDIT_STATUS_20251107_UPDATED.md`.
