#!/usr/bin/env python3
"""Canonicalize legacy receipt JSON files so the verifier accepts them.

This script updates receipts in-place by copying observation.mu_delta -> mu_delta,
observation.cert -> certificate, computing certificate_hash when a certificate
is present, and computing the canonical step_hash for each step using the
repository's canonical JSON encoding rules.

Run: python scripts/canonicalize_receipts.py receipts
"""
from pathlib import Path
import json
import hashlib
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools.receipts import compute_step_hash


def canonicalize_step(step: dict) -> bool:
    changed = False
    # Pull mu_delta up from observation if present
    obs = step.get("observation")
    if "mu_delta" not in step and isinstance(obs, dict) and "mu_delta" in obs:
        step["mu_delta"] = obs["mu_delta"]
        changed = True

    # Pull certificate up from observation if present
    if "certificate" not in step and isinstance(obs, dict) and "cert" in obs:
        step["certificate"] = obs["cert"]
        changed = True

    # Compute certificate_hash if missing and certificate present
    if "certificate" in step and "certificate_hash" not in step:
        cert = step["certificate"]
        if isinstance(cert, str):
            payload = cert.encode("utf-8")
        else:
            payload = json.dumps(cert, sort_keys=True).encode("utf-8")
        step["certificate_hash"] = hashlib.sha256(payload).hexdigest()
        changed = True

    # Compute canonical step_hash if missing
    if "step_hash" not in step:
        step["step_hash"] = compute_step_hash(step)
        changed = True

    return changed


def canonicalize_file(path: Path) -> bool:
    data = json.loads(path.read_text(encoding="utf-8"))
    if "steps" not in data:
        return False
    changed_any = False
    for step in data["steps"]:
        if canonicalize_step(step):
            changed_any = True
    if changed_any:
        path.write_text(json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2), encoding="utf-8")
    return changed_any


def main():
    import argparse

    p = argparse.ArgumentParser(description="Canonicalize receipt JSON files in a directory")
    p.add_argument("directory", help="Directory containing receipt JSON files")
    args = p.parse_args()
    d = Path(args.directory)
    if not d.is_dir():
        print(f"Not a directory: {d}")
        raise SystemExit(2)
    changed = False
    for pth in sorted(d.glob("*.json")):
        try:
            updated = canonicalize_file(pth)
            if updated:
                print(f"Updated: {pth}")
                changed = True
            else:
                print(f"No change: {pth}")
        except Exception as e:
            print(f"Failed to canonicalize {pth}: {e}")
    if changed:
        print("Some receipts were canonicalized. Please run: python scripts/challenge.py verify receipts")


if __name__ == '__main__':
    main()
