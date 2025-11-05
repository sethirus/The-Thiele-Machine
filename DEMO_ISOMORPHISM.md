Demo: Isomorphism flow (canonical CNF/model → receipt → verify)

This short document describes the small demo CLI and how it exercises the
canonicalisation and verification chain in the repository.

scripts/demo_isomorphism_cli.py
-------------------------------
Usage:

python3 scripts/demo_isomorphism_cli.py --create-demo --outdir /tmp/demo
python3 scripts/demo_isomorphism_cli.py --receipt /tmp/demo/demo_receipt.json --show-cert-store --sign --normalize

Features:
- Create a tiny demo receipt with CNF and model blobs (use --create-demo).
- Canonicalize the receipt in-place (the script calls `canonicalize_file`).
- Optionally show files emitted under `cert_store/` (canonical models).
- Optionally sign the top-level `global_digest` using the deterministic
  kernel secret key (generates keys if missing) with `--sign`.
- Attempt LRAT normalization for LRAT proofs referenced by steps using
  `--normalize` (best-effort; depends on `scripts/analyze_lrat.py` and
  external tools when present).

Implementation notes:
- The demo uses the repository's canonical JSON encoding and the
  `tools.receipts.ReceiptValidator` for verification.
- Per-step signatures and canonical model persistence are produced by
  `scripts/canonicalize_receipts.py`.

Try it:

python3 scripts/demo_isomorphism_cli.py --create-demo --outdir /tmp/demo
python3 scripts/demo_isomorphism_cli.py --receipt /tmp/demo/demo_receipt.json --show-cert-store --sign

If you want CI to strictly enforce LRAT normalization, install `drat-trim`
and `lrat-check` in the CI runners and remove the '|| true' fallback in the
workflow step that installs them.
