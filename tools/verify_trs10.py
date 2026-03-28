#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from cryptography.exceptions import InvalidSignature

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tools.trs10_standalone import verify_receipt_dict


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Verify a signed TRS-1.0 receipt.")
    parser.add_argument("receipt", help="Path to the receipt JSON file")
    parser.add_argument("--trusted-pubkey", required=True, help="Trusted Ed25519 public key as 32-byte hex")
    parser.add_argument(
        "--base-dir",
        help="Base directory containing the files referenced by basename in the receipt. Defaults to the receipt directory.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    receipt_path = Path(args.receipt)
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    base_dir = Path(args.base_dir) if args.base_dir else receipt_path.parent

    try:
        verify_receipt_dict(receipt, trusted_public_key_hex=args.trusted_pubkey, base_dir=base_dir)
    except InvalidSignature:
        print("Receipt verification failed: invalid signature")
        return 1
    except Exception as exc:
        print(f"Receipt verification failed: {exc}")
        return 1

    print("Receipt verification succeeded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())