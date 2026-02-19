# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Certificate storage and hashing utilities.

The :class:`CertStore` assigns monotonically increasing certificate ids and
persists solver artefacts to disk.  Each certificate consists of a set of
files with a common numeric prefix (e.g. ``0001.assert.smt2``) and a companion
``.sha256`` hash file.  Hashes are returned to the caller so they can be
recorded in CSRs or summary documents.
"""

from __future__ import annotations

from pathlib import Path
import hashlib


class CertStore:
    """Filesystem-backed certificate repository."""

    def __init__(self, outdir: Path) -> None:
        self.outdir = outdir
        self.outdir.mkdir(parents=True, exist_ok=True)
        # Initialize a persistent counter to avoid repeated directory scans
        existing = len(list(self.outdir.glob("*.sha256")))
        # Next id to use (1-based)
        self._next = existing + 1

    # ------------------------------------------------------------------
    # Id management
    # ------------------------------------------------------------------
    def next_id(self) -> str:
        """Return the next certificate id as a zero-padded string."""
        cid = f"{self._next:04d}"
        self._next += 1
        return cid

    # ------------------------------------------------------------------
    # File helpers
    # ------------------------------------------------------------------
    def write_text(self, cid: str, name: str, text: str) -> Path:
        path = self.outdir / f"{cid}.{name}"
        path.write_text(text)
        return path

    def write_bytes(self, cid: str, name: str, data: bytes) -> Path:
        path = self.outdir / f"{cid}.{name}"
        path.write_bytes(data)
        return path

    def save_hash(self, cid: str, data: bytes) -> str:
        """Compute and persist the SHA‑256 digest for ``data``."""

        digest = hashlib.sha256(data).hexdigest()
        (self.outdir / f"{cid}.sha256").write_text(digest)
        return digest

    def hash_path(self, cid: str) -> Path:
        """Path to the ``.sha256`` file for ``cid``."""

        return self.outdir / f"{cid}.sha256"


__all__ = ["CertStore"]
