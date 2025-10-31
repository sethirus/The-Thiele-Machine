Receipt schema changelog

v1.1 (2025-10-31)

- Bumped receipt schema to 1.1 to reflect minor changes in certificate payloads.
  - `mu_delta` is treated as a numeric (float) value in receipts.
  - Steps may include stable `cnf_sha256`, `proof_sha256` and `status` fields to
    provide canonical digests for CNF and proof artifacts.
- Validators now accept both `spec_version` "1.0" (legacy) and "1.1" receipts.
- Tools/validators should prefer `1.1` for new receipts to ensure stable hashing
  and reproducible μ accounting.

Compatibility:
- Legacy receipts (`spec_version: "1.0"`) remain accepted for compatibility but
  authors are encouraged to canonicalize and re-emit receipts using `1.1`.

Security note:
- The μ-spec calculation is duplicated in `tools/mu_spec.py` so validators do not
  rely on runtime VM modules for μ recomputation (reducing the validator TCB).
