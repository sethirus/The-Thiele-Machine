# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Generate Ed25519 signing keys for the Thiele Machine kernel."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

from nacl import signing


DEFAULT_SECRET_PATH = Path("kernel_secret.key")
DEFAULT_PUBLIC_PATH = Path("kernel_public.key")


def write_key(path: Path, data: bytes | str, *, force: bool, text: bool = False) -> None:
    """Write ``data`` to ``path`` unless it already exists and ``force`` is False."""

    if path.exists() and not force:
        raise FileExistsError(
            f"Refusing to overwrite existing key at {path}. Use --force to regenerate."
        )
    path.parent.mkdir(parents=True, exist_ok=True)
    if text:
        if isinstance(data, bytes):
            raise TypeError("text=True requires data to be a string")
        path.write_text(data + "\n")
    else:
        if isinstance(data, str):
            raise TypeError("Binary write expects bytes data")
        path.write_bytes(data)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate an Ed25519 keypair for Thiele Machine receipts"
    )
    parser.add_argument(
        "--secret-path",
        type=Path,
        default=DEFAULT_SECRET_PATH,
        help=f"Path for the signing key (default: {DEFAULT_SECRET_PATH})",
    )
    parser.add_argument(
        "--public-path",
        type=Path,
        default=DEFAULT_PUBLIC_PATH,
        help=f"Path for the verifying key (default: {DEFAULT_PUBLIC_PATH})",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Overwrite existing keys instead of aborting",
    )
    parser.add_argument(
        "--deterministic-test-key",
        action="store_true",
        help=(
            "Generate the deterministic test keypair shipped with the repository. "
            "This uses a fixed seed so auditors can reproduce signatures."
        ),
    )
    args = parser.parse_args()

    if args.deterministic_test_key:
        seed = hashlib.sha256(
            b"Thiele Machine deterministic kernel signing key v1"
        ).digest()
        signing_key = signing.SigningKey(seed)
    else:
        signing_key = signing.SigningKey.generate()
    verify_key = signing_key.verify_key

    write_key(args.secret_path, signing_key.encode(), force=args.force)
    write_key(args.public_path, verify_key.encode().hex(), force=args.force, text=True)

    print(f"Generated signing key: {args.secret_path}")
    print(f"Generated verifying key: {args.public_path}")


if __name__ == "__main__":
    main()

