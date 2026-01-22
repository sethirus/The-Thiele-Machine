#!/usr/bin/env python3
"""Fetch and verify external artifacts listed in a manifest.

Manifest format (configs/data_manifest.json):
{
  "catnet": {
    "url": "https://example.org/catnet-showcase.tar.gz",
    "sha256": "...",
    "dest": "archive/showcase"
  },
  "prereg_a": {
    "url": "https://example.org/prereg_a_dataset.zip",
    "sha256": "...",
    "dest": "DATA_A"
  }
}

The script uses tools/create_receipt.fetch_archive for safe downloading and extraction.
"""
from pathlib import Path
import hashlib
import json
from tools.create_receipt import fetch_archive

MANIFEST = Path(__file__).resolve().parents[1] / "configs" / "data_manifest.json"


def verify_sha256(path: Path, expected: str) -> bool:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest() == expected


def fetch_all(manifest_path: Path = MANIFEST) -> dict:
    if not manifest_path.exists():
        print(f"No manifest at {manifest_path}, nothing to fetch")
        return {}
    m = json.loads(manifest_path.read_text())
    results = {}
    for name, entry in m.items():
        url = entry.get("url")
        sha256 = entry.get("sha256")
        dest = Path(entry.get("dest", name))
        dest.mkdir(parents=True, exist_ok=True)
        print(f"Fetching {name} from {url} into {dest}")
        extracted = fetch_archive(url, dest)
        if sha256 and not verify_sha256(extracted):
            raise SystemExit(f"SHA256 mismatch for {name}")
        results[name] = str(extracted)
    return results


if __name__ == "__main__":
    fetch_all()
