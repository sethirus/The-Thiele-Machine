#!/usr/bin/env python3
"""Provision an Ed25519 kernel keypair for the Thiele Machine.

This script writes a secret key file (32 bytes) and a public key file (32 bytes)
to the requested paths with safe filesystem permissions (600). It will refuse to
overwrite existing keys unless --force is passed.

Usage:
  python scripts/provision_keys.py --secret-path kernel_secret.key --public-path kernel_public.key

Operators should generate keys on an air-gapped machine if required and copy them
to the runtime host using secure channels. When deploying to production set
THIELE_PRODUCTION=1 and ensure keys are present; the runtime will refuse to
auto-generate keys in production mode.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
from typing import Optional

from nacl import signing


def write_bytes(path: Path, data: bytes, mode: int = 0o600) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    # write atomically
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_bytes(data)
    os.chmod(tmp, mode)
    tmp.replace(path)


def generate_keys(secret_path: Path, public_path: Path, force: bool = False) -> None:
    if secret_path.exists() or public_path.exists():
        if not force:
            raise SystemExit(
                "Refusing to overwrite existing key files; use --force to replace"
            )
    # generate a new signing key
    sk = signing.SigningKey.generate()
    pk = sk.verify_key
    # SigningKey.encode() returns 32-byte seed; for compatibility we store the
    # 32-byte seed (ed25519 seed) used by nacl
    secret_bytes = sk.encode()
    public_bytes = pk.encode()

    write_bytes(secret_path, secret_bytes)
    write_bytes(public_path, public_bytes)

    print(f"Wrote secret key to: {secret_path}")
    print(f"Wrote public key to: {public_path}")


def main(argv: Optional[list[str]] = None) -> None:
    p = argparse.ArgumentParser(description="Provision Ed25519 kernel keypair")
    p.add_argument("--secret-path", required=True, help="Path to write secret key file")
    p.add_argument("--public-path", required=True, help="Path to write public key file")
    p.add_argument("--force", action="store_true", help="Overwrite existing files")
    args = p.parse_args(argv)

    secret = Path(args.secret_path).expanduser()
    public = Path(args.public_path).expanduser()

    try:
        generate_keys(secret, public, force=args.force)
    except Exception as e:
        raise SystemExit(f"Failed to provision keys: {e}")


if __name__ == "__main__":
    main()
