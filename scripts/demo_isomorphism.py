#!/usr/bin/env python3
"""Minimal demo: show canonical CNF -> canonical model -> receipt -> verify

This is a tiny runnable script that exercises the canonicalisation and
verification path. It uses existing project utilities where available.

Usage (from repo root):
    python3 scripts/demo_isomorphism.py

Outputs: prints the canonical model SHA256, step digest, and verification
result.
"""
import hashlib
import json
import os
import tempfile
from pathlib import Path

# Try to import the project's canonicaliser and verifier helpers.
try:
    # canonicalize_receipts exposes `canonicalize_file`
    from scripts.canonicalize_receipts import canonicalize_file as canonicalize_receipt_file
except Exception:
    canonicalize_receipt_file = None

try:
    # verifier is in scripts/verify_receipt.py and exposes verify_receipt_file
    from scripts.verify_receipt import verify_receipt_file
except Exception:
    verify_receipt_file = None

# Fallback simple implementations if project utilities are not importable.

def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    repo = Path(__file__).resolve().parents[1]
    demo_dir = Path(tempfile.mkdtemp(prefix="thiele-demo-"))

    # Create a tiny CNF and a trivial model for demonstration.
    cnf = """c demo CNF
p cnf 3 2
1 0
-1 0
"""
    cnf_path = demo_dir / "demo.cnf"
    cnf_path.write_text(cnf)

    model = "1 -2 3 0\n"
    model_path = demo_dir / "demo.model"
    model_path.write_text(model)

    # Compute SHA256s
    print("demo dir:", demo_dir)
    print("cnf sha256:", sha256_file(cnf_path))
    print("model sha256:", sha256_file(model_path))

    # Build minimal receipt
    receipt = {
        "spec_version": "1.1",
        "global_digest": None,
        "steps": [
            {
                "id": "step0",
                "type": "LASSERT",
                "cnf_blob_uri": str(cnf_path),
                "model_blob_uri": str(model_path),
                "cnf_sha256": sha256_file(cnf_path),
                "model_sha256": sha256_file(model_path),
                "mu_delta": 1.0,
            }
        ],
    }

    receipt_path = demo_dir / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2))

    print("wrote receipt:", receipt_path)

    # Try canonicalize + verify using project's scripts if available.
    if canonicalize_receipt_file:
        print("Running canonicalizer... (project function detected)")
        canonicalize_receipt_file(str(receipt_path))
    else:
        print("canonicalizer not importable; skipping")

    if verify_receipt_file:
        print("Running verifier... (project function detected)")
        ok = verify_receipt_file(str(receipt_path))
        print("verify result:", ok)
    else:
        print("verifier not importable; skipping")


if __name__ == "__main__":
    main()
