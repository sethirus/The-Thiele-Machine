#!/usr/bin/env python3
"""CLI for the demo isomorphism flow.

Usage examples:
  python3 scripts/demo_isomorphism_cli.py --receipt /path/to/receipt.json
  python3 scripts/demo_isomorphism_cli.py --create-demo --outdir /tmp/demo

Features:
- canonicalize a receipt (calls scripts.canonicalize_receipts.canonicalize_file)
- optionally print the cert_store contents
- attempt to verify using tools.receipts.ReceiptValidator
"""
import argparse
import json
from pathlib import Path
import sys


# Ensure repository root is on the import path when invoked as a script. When
# this module is executed from within the ``scripts`` directory Python adds the
# current directory to ``sys.path`` which prevents ``import scripts.*`` from
# resolving (it would otherwise look for ``scripts/`` within ``scripts/``).
# Adding the repo root allows ``scripts`` to be treated as a package regardless
# of the current working directory.
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def main():
    p = argparse.ArgumentParser(description="Demo isomorphism CLI")
    p.add_argument("--receipt", help="Path to a receipt JSON file to canonicalize and verify")
    p.add_argument("--create-demo", action="store_true", help="Create a small demo receipt in --outdir")
    p.add_argument("--outdir", default=".", help="Output directory for demo creation")
    p.add_argument("--show-cert-store", action="store_true", help="Print cert_store contents after canonicalization")
    p.add_argument("--sign", action="store_true", help="Sign the global digest using kernel_secret.key (generates keys if missing)")
    p.add_argument("--normalize", action="store_true", help="Attempt LRAT normalization via scripts/analyze_lrat.py for LRAT proofs")
    p.add_argument("--verify-with-public-key", help="Verify the receipt using the given public key path via scripts.verify_receipt.verify_receipt_file")
    args = p.parse_args()

    outdir = Path(args.outdir)

    if args.create_demo:
        demo_receipt = outdir / "demo_receipt.json"
        # write a tiny example receipt that canonicalize_file will update
        cnf = outdir / "demo.cnf"
        model = outdir / "demo.model"
        cnf.write_text("c demo\np cnf 2 1\n1 0\n")
        model.write_text("1 0\n")
        receipt = {"spec_version": "1.0", "global_digest": None, "steps": [{"step": 0, "instruction": {"op": "LASSERT", "payload": {}}, "pre_state": {"pc":0}, "post_state": {"pc":1}, "pre_state_hash": "", "post_state_hash": "", "observation": {"mu_delta": 1.0, "cert": {}}, "cnf_blob_uri": str(cnf), "model_blob_uri": str(model)}]}
        demo_receipt.write_text(json.dumps(receipt, indent=2))
        print("Wrote demo receipt:", demo_receipt)
        args.receipt = str(demo_receipt)

    if not args.receipt:
        print("Please provide --receipt or --create-demo")
        sys.exit(2)

    receipt_path = Path(args.receipt)
    if not receipt_path.exists():
        print("Receipt not found:", receipt_path)
        sys.exit(2)

    # canonicalize
    try:
        from scripts.canonicalize_receipts import canonicalize_file
    except Exception as e:
        print("Failed to import canonicalizer:", e)
        sys.exit(1)

    changed = canonicalize_file(receipt_path)
    print("Canonicalize changed:", changed)

    if args.show_cert_store:
        cert_store = receipt_path.parent / "cert_store"
        if cert_store.exists():
            for p in sorted(cert_store.rglob("*")):
                if p.is_file():
                    print(p.relative_to(receipt_path.parent), p.stat().st_size)
        else:
            print("No cert_store found")

    # Optionally attempt LRAT normalization on any LRAT proofs referred to by steps
    if args.normalize:
        try:
            analyzer = Path(__file__).resolve().parents[1] / "scripts" / "analyze_lrat.py"
            if not analyzer.exists():
                print("Analyzer not present:", analyzer)
            else:
                import subprocess
                data = json.loads(receipt_path.read_text())
                for step in data.get("steps", []):
                    if step.get("proof_portable") == "LRAT" and step.get("proof_blob_uri"):
                        proof = step.get("proof_blob_uri")
                        cnf = step.get("cnf_blob_uri") or ""
                        print("Normalizing LRAT proof:", proof)
                        # call analyzer with --normalize
                        res = subprocess.run([sys.executable, str(analyzer), str(proof), "--cnf", str(cnf), "--normalize"], check=False)
                        print("analyzer exit:", res.returncode)
        except Exception as e:
            print("LRAT normalization attempt failed:", e)

    # verify using repository validator
    try:
        from tools.receipts import ReceiptValidator
    except Exception as e:
        print("Failed to import ReceiptValidator:", e)
        sys.exit(1)

    data = json.loads(receipt_path.read_text())

    # Optionally sign the top-level receipt global digest using the deterministic
    # kernel keypair. This mirrors the canonicaliser behaviour for per-step
    # signatures but produces a top-level signature that repository validators
    # expect.
    if args.sign and "signature" not in data:
        try:
            from thielecpu.receipts import ensure_kernel_keys
            from nacl import signing

            ensure_kernel_keys()
            secret_path = Path("kernel_secret.key")
            if not secret_path.exists():
                raise FileNotFoundError(str(secret_path))
            sk = signing.SigningKey(secret_path.read_bytes())
            sig = sk.sign(bytes.fromhex(data["global_digest"]))
            data["signature"] = sig.signature.hex()
            receipt_path.write_text(json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2))
            print("Signed receipt with kernel_secret.key")
        except Exception as e:
            print("Failed to sign receipt:", e)

    validator = ReceiptValidator(require_signature=False)
    try:
        mu = validator.validate(data)
    except Exception as e:
        print("Validation failed:", e)
        sys.exit(1)
    print("Validation OK; mu total:", mu)
    # Optionally run the repository verifier with a supplied public key
    if args.verify_with_public_key:
        try:
            # Use the repository ReceiptValidator and the provided public key to
            # verify the top-level signature and the canonical step hashes.
            from tools.receipts import ReceiptValidator

            pubpath = Path(args.verify_with_public_key)
            if not pubpath.exists():
                print("Public key not found:", pubpath)
                sys.exit(2)
            # load verify key bytes and write kernel_pubkey into the receipt so
            # ReceiptValidator can use it for signature verification.
            vk = pubpath.read_bytes().strip()
            try:
                # prefer hex if file contains ascii hex
                hextext = vk.decode("ascii").strip()
                if len(hextext) % 2 == 0 and all(c in "0123456789abcdefABCDEF" for c in hextext):
                    pubhex = hextext.lower()
                else:
                    pubhex = vk.hex()
            except Exception:
                pubhex = vk.hex()
            data["kernel_pubkey"] = pubhex
            receipt_path.write_text(json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2))

            validator = ReceiptValidator(require_signature=True)
            try:
                validator.validate(data)
            except Exception as e:
                print("Receipt validation failed:", e)
                sys.exit(1)
            print("Verified receipt with provided public key")
            sys.exit(0)
        except Exception as e:
            print("Verification invocation failed:", e)
            sys.exit(1)

    sys.exit(0)


if __name__ == "__main__":
    main()
