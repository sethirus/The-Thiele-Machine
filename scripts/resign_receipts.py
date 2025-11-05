# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Re-sign structured Thiele Machine receipts using the Ed25519 kernel key."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))

from thielecpu.receipts import sign_receipt


def resign_file(path: Path) -> bool:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False

    if isinstance(data, list):
        return False

    steps = data.get("steps")
    if not isinstance(steps, list):
        return False

    changed = False
    for step in steps:
        if not isinstance(step, dict):
            continue
        payload = {
            "step": step.get("step"),
            "instruction": step.get("instruction"),
            "pre_state": step.get("pre_state"),
            "post_state": step.get("post_state"),
            "observation": step.get("observation"),
            "pre_state_hash": step.get("pre_state_hash"),
            "post_state_hash": step.get("post_state_hash"),
        }
        signature = sign_receipt(payload)
        if step.get("signature") != signature:
            step["signature"] = signature
            changed = True

    if changed:
        path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return changed


def iter_targets(root: Path) -> Iterable[Path]:
    if root.is_file() and root.suffix == ".json":
        yield root
    elif root.is_dir():
        for candidate in sorted(root.rglob("*.json")):
            if candidate.is_file():
                yield candidate


def main() -> None:
    parser = argparse.ArgumentParser(description="Re-sign Thiele Machine receipt JSON files")
    parser.add_argument(
        "paths",
        nargs="*",
        default=["receipts", "examples", "demo_output", "rsa_demo_output"],
        help="Files or directories containing structured receipts",
    )
    args = parser.parse_args()

    total = 0
    updated = 0
    for raw in args.paths:
        for candidate in iter_targets(Path(raw).resolve()):
            total += 1
            if resign_file(candidate):
                print(f"Re-signed: {candidate}")
                updated += 1

    print(f"Processed {total} files; updated {updated} receipts.")


if __name__ == "__main__":
    main()

