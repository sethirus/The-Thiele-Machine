Demo quick pointer
===================

This repository includes a small demo that exercises the canonicalisation →
receipt → verify flow used throughout the project.

See `docs/DEMO_ISOMORPHISM.md` for detailed instructions, or run the demo CLI:

```bash
python3 scripts/demo_isomorphism_cli.py --create-demo --outdir /tmp/demo
python3 scripts/demo_isomorphism_cli.py --receipt /tmp/demo/demo_receipt.json --show-cert-store --sign --normalize --verify-with-public-key kernel_public.key
```

The CLI is intentionally conservative: normalization is best-effort and the
script will try to generate deterministic kernel keys if they are missing.
