#!/usr/bin/env python3
"""Reconstruct a revision snapshot in a fresh directory and verify its manifest."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tarfile
import tempfile


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    options = parser.parse_args()
    manifest = json.loads((options.snapshot / "manifest.json").read_text())
    archive = options.snapshot / "workspace.tar.gz"
    if digest(archive) != manifest["archive_sha256"]:
        raise ValueError("Archive hash mismatch")
    with tempfile.TemporaryDirectory(prefix="thiele-reconstructed-") as folder:
        root = Path(folder)
        with tarfile.open(archive) as source:
            source.extractall(root, filter="data")
        for record in manifest["files"]:
            relative = Path(record["path"])
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError(f"Invalid manifest path: {relative}")
            path = root / relative
            if "link" in record:
                if not path.is_symlink() or os.readlink(path) != record["link"]:
                    raise ValueError(f"Symlink mismatch: {relative}")
            else:
                if path.is_symlink() or digest(path) != record["sha256"]:
                    raise ValueError(f"File mismatch: {relative}")
                # The data filter removes group/other write permissions.
                # Restore the manifest's source mode before checking it.
                path.chmod(record["mode"])
                if path.stat().st_mode & 0o777 != record["mode"]:
                    raise ValueError(f"Mode mismatch: {relative}")
    print(f"PASS: reconstructed {len(manifest['files'])} files; bytes, modes and symlinks match")


if __name__ == "__main__":
    main()
