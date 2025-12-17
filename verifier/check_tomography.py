#!/usr/bin/env python3
"""CLI wrapper for C-TOMO receipt-defined verification."""

from __future__ import annotations

import argparse
from pathlib import Path

from verifier.c_tomography import TomographyVerificationError, verify_tomography
from verifier.receipt_protocol import ed25519_keypair, write_signed_verification_artifact, write_trust_manifest


def _int_field(result: object, key: str) -> int:
    if not isinstance(result, dict):
        return 0
    value = result.get(key)
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    if isinstance(value, str):
        try:
            return int(value)
        except ValueError:
            return 0
    return 0


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_dir", type=Path, help="Run directory containing tomography artifacts")
    parser.add_argument("trust_manifest", type=Path, help="Trust manifest to validate TRS-1.0 receipts")
    parser.add_argument("--out-dir", type=Path, default=Path("."), help="Directory to write verification artifacts")
    parser.add_argument("--key-id", type=str, default="verifier", help="Key id for signing verification output")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)

    try:
        result = verify_tomography(args.run_dir, args.trust_manifest)
        status = "PASS"
        ok = True
        err: str | None = None
    except TomographyVerificationError as exc:
        result = {"ok": False, "error": str(exc)}
        status = "FAIL"
        ok = False
        err = str(exc)

    module = "C_tomography"
    receipt_name = "tomography.receipt.json"

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
            "required_disclosure_bits": _int_field(result, "required_disclosure_bits"),
            "provided_disclosure_bits": _int_field(result, "provided_disclosure_bits"),
        },
        "metadata": {
            "generated_by": "verifier/check_tomography.py",
            "timestamp": None,
            "error": err,
        },
    }

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
