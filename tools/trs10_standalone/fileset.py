from __future__ import annotations

import hashlib
from pathlib import Path

from .protocol import validate_receipt_path


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def verify_fileset_entries(receipt: dict, *, base_dir: Path) -> None:
    for entry in receipt["files"]:
        path = base_dir / validate_receipt_path(entry["path"], field_name="fileset.path")
        if not path.exists() or not path.is_file():
            raise FileNotFoundError(f"Receipt file missing during verification: {path}")
        actual_sha = sha256_file(path)
        if actual_sha != entry["sha256"]:
            raise ValueError(f"Digest mismatch for {entry['path']}")
        actual_size = path.stat().st_size
        if actual_size != entry["size"]:
            raise ValueError(f"Size mismatch for {entry['path']}")