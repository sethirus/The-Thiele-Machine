#!/usr/bin/env python3
"""CLI wrapper for C-ENTROPY receipt-defined verification."""

from __future__ import annotations

import argparse
from pathlib import Path

from verifier.c_entropy2 import EntropyVerificationError, verify_entropy2
from verifier.receipt_protocol import (
    ReceiptProtocolError,
    ed25519_keypair,
    write_signed_verification_artifact,
    write_trust_manifest,
)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_dir", type=Path, help="Run directory containing entropy artifacts")
    parser.add_argument("trust_manifest", type=Path, help="Trust manifest to validate TRS-1.0 receipts")
    parser.add_argument("--out-dir", type=Path, default=Path("."), help="Directory to write verification artifacts")
    parser.add_argument("--key-id", type=str, default="verifier", help="Key id for signing verification output")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)

    try:
        result = verify_entropy2(args.run_dir, args.trust_manifest)
        status = "PASS"
        ok = True
        err: str | None = None
    except EntropyVerificationError as exc:
        result = {"ok": False, "error": str(exc)}
        status = "FAIL"
        ok = False
        err = str(exc)

    module = "C_entropy"
    receipt_name = "entropy.receipt.json"

    verification_payload = {
        "schema_version": "TM-VERIFY-1",
        "module": module,
        "status": status,
        "ok": ok,
        "inputs": {
            "run_dir": str(Path(args.run_dir).as_posix()),
            "trust_manifest": str(Path(args.trust_manifest).as_posix()),
            "receipt": receipt_name,
        },
        "results": dict(result),
        "falsifiers": [],
        "mu_summary": {
            "required_disclosure_bits": int(result.get("required_disclosure_bits", 0) if isinstance(result, dict) else 0),
            "provided_disclosure_bits": int(result.get("provided_disclosure_bits", 0) if isinstance(result, dict) else 0),
        },
        "metadata": {
            "generated_by": "verifier/check_entropy2.py",
            "timestamp": None,
            "error": err,
        },
    }

    # Sign verification output with an ephemeral key so the artifact is self-contained.
    sk, pk_hex = ed25519_keypair()
    out_dir = Path(args.out_dir)
    trust_path = out_dir / "trust_manifest.json"
    write_trust_manifest(trust_path, key_id=args.key_id, public_key_hex=pk_hex)

    write_signed_verification_artifact(
        out_dir=out_dir,
        module=module,
        verification=verification_payload,
        private_key=sk,
        public_key_hex=pk_hex,
        key_id=args.key_id,
        trust_manifest_path=trust_path,
    )

    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
