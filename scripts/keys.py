"""Helpers for managing local Thiele Machine signing keys."""
from __future__ import annotations

import os
from pathlib import Path
from typing import Optional

from nacl import signing

__all__ = [
    "get_or_create_signing_key",
    "ensure_public_key",
]


def _atomic_write_bytes(path: Path, data: bytes, mode: int = 0o600) -> None:
    """Write ``data`` to ``path`` atomically and apply ``mode`` where possible."""

    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.parent / f".{path.name}.tmp"
    tmp_path.write_bytes(data)
    try:
        os.chmod(tmp_path, mode)
    except PermissionError:
        # Ignore permission errors on platforms that do not expose POSIX modes.
        pass
    tmp_path.replace(path)
    try:
        os.chmod(path, mode)
    except PermissionError:
        pass


def _load_public_key_bytes(path: Path) -> Optional[bytes]:
    try:
        raw = path.read_bytes().strip()
    except FileNotFoundError:
        return None
    except OSError:
        return None
    if not raw:
        return None
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError:
        return raw
    if len(text) % 2 == 0:
        try:
            return bytes.fromhex(text)
        except ValueError:
            pass
    return raw


def get_or_create_signing_key(
    path: Path,
    *,
    public_key_path: Path | None = None,
) -> signing.SigningKey:
    """Return the Ed25519 signing key at ``path`` or create a new one.

    The secret key is stored with 0600 permissions. When ``public_key_path`` is
    provided the corresponding verify key is written alongside it (also with
    restrictive permissions) whenever the material is missing or out-of-date.
    """

    path = path.expanduser()
    try:
        key_bytes = path.read_bytes()
    except FileNotFoundError:
        key_bytes = b""
    except OSError:
        key_bytes = b""

    signing_key: signing.SigningKey
    if key_bytes:
        try:
            signing_key = signing.SigningKey(key_bytes)
        except Exception:
            signing_key = signing.SigningKey.generate()
            _atomic_write_bytes(path, signing_key.encode())
        else:
            # Ensure file permissions are restrictive even if the key already existed.
            try:
                os.chmod(path, 0o600)
            except PermissionError:
                pass
    else:
        signing_key = signing.SigningKey.generate()
        _atomic_write_bytes(path, signing_key.encode())

    if public_key_path is not None:
        ensure_public_key(signing_key, public_key_path)

    return signing_key


def ensure_public_key(signing_key: signing.SigningKey, path: Path) -> None:
    """Ensure ``path`` contains the verify key for ``signing_key``."""

    path = path.expanduser()
    expected = signing_key.verify_key.encode()
    current = _load_public_key_bytes(path)
    if current == expected:
        return
    encoded = (expected.hex() + "\n").encode("ascii")
    _atomic_write_bytes(path, encoded)
