Receipt schema v1.1

This document summarises the changes introduced in spec version 1.1 and the
expected producer/validator behaviour.

Overview
--------
Spec v1.1 is a backward-compatible extension of v1.0 that adds canonical
artifact digests, numeric μ accounting, and an explicit LRUP acceptance policy.

New/changed fields
------------------
Top-level:
- spec_version: now allowed to be "1.0" or "1.1". New receipts SHOULD use "1.1".
- global_digest: SHA-256 of the concatenated step_hashes (unchanged semantics).

Per-step additions (optional but encouraged):
- cnf_sha256: canonical SHA-256 digest (hex) of the CNF blob referenced by cnf_blob_uri.
- proof_sha256: canonical SHA-256 digest (hex) of the proof blob referenced by proof_blob_uri.
- model_sha256: canonical SHA-256 digest (hex) of the canonicalised model file referenced by model_blob_uri.
- status: optional status string; producers MAY set values like "ok" or "requires_normalization".
- signature: per-step signature (hex) if the producer signs steps individually.
- mu_delta: numeric (float) μ charge; validators MUST accept numeric values and reject negative or non-numeric values.

LRAT acceptance policy (LRUP)
-----------------------------
The validator accepts only LRUP-style LRATs (LRATs that are RUP-derivable). RAT-only LRATs are rejected.
Producers should either:
- Emit LRUP (RUP-justified LRAT) proofs, or
- Run a normalization step (e.g., drat-trim/gratgen) to convert RAT hints into RUP-justified LRAT.

Validators MAY implement a conservative heuristic that rejects LRATs containing RAT-only hints, and MAY attempt best-effort normalization using available toolchain (drat-trim) before accepting a proof.

μ-spec
------
The μ calculation used by validators is pinned in `tools/mu_spec.py`. Validators MUST use this implementation (or an equivalent bit-for-bit compatible implementation) to recompute μ for LASSERT steps and reject receipts where the recorded `mu_delta` differs from recomputed value.

Canonical models
----------------
Producers SHOULD persist canonicalised models in the cert store and include `model_sha256` in the step payload. Validators will canonicalise CNF & remap incoming models to verify satisfiability and to compute the canonical model digest.

Backward compatibility
----------------------
- Validators MUST accept legacy `spec_version: "1.0"` receipts for compatibility but SHOULD prefer `1.1` for new receipts.
- Producers are encouraged to re-emit legacy receipts after canonicalisation using `spec_version: "1.1"`.

Security considerations
-----------------------
- Validators MUST not import mutable VM modules for μ recomputation; instead, use the pinned `tools/mu_spec.py` copy or a vendored, pinned implementation.
- Validators MUST validate per-step artifact digests (`cnf_sha256`, `proof_sha256`, `model_sha256`) when present.

Examples
--------
See `spec/golden` for golden receipts that conform to the new schema.
