#!/usr/bin/env python3
"""Convert legacy Thiele Machine receipt JSON files to the canonical schema."""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List

GENESIS_HASH = "genesis"


def canonical_json(data: Any) -> str:
    return json.dumps(data, sort_keys=True, separators=(",", ":"))


def hash_payload(payload: Any) -> str:
    return hashlib.sha256(canonical_json(payload).encode("utf-8")).hexdigest()


def detect_legacy_steps(data: Any) -> bool:
    if not isinstance(data, list) or not data:
        return False
    first = data[0]
    return isinstance(first, dict) and "instruction" in first and "pre_state" in first


def convert_step_list(path: Path, data: List[Dict[str, Any]]) -> Dict[str, Any]:
    steps: List[Dict[str, Any]] = []
    prev_hash = GENESIS_HASH
    mu_total = 0.0

    for index, entry in enumerate(data):
        instruction = entry.get("instruction", {})
        observation = entry.get("observation", {})
        certificate = observation.get("cert", {})
        pre_state = entry.get("pre_state", {})
        post_state = entry.get("post_state", {})
        mu_delta = float(observation.get("mu_delta", entry.get("mu_delta", 0.0)))

        mu_total += mu_delta

        pre_state_hash = entry.get("pre_state_hash") or hash_payload(pre_state)
        post_state_hash = entry.get("post_state_hash") or hash_payload(post_state)
        if isinstance(certificate, str):
            certificate_hash = hashlib.sha256(certificate.encode("utf-8")).hexdigest()
        else:
            certificate_hash = hashlib.sha256(json.dumps(certificate, sort_keys=True).encode("utf-8")).hexdigest()

        step_payload = {
            "step": int(entry.get("step", index)),
            "instruction": instruction,
            "pre_state_hash": pre_state_hash,
            "post_state_hash": post_state_hash,
            "observation": observation,
            "mu_delta": mu_delta,
            "prev_step_hash": prev_hash,
        }
        step_hash = hash_payload(step_payload)

        canonical_step = {
            "step": step_payload["step"],
            "instruction": instruction,
            "pre_state": pre_state,
            "post_state": post_state,
            "observation": observation,
            "mu_delta": mu_delta,
            "pre_state_hash": pre_state_hash,
            "post_state_hash": post_state_hash,
            "signature": entry.get("signature", ""),
            "certificate": certificate,
            "certificate_hash": certificate_hash,
            "prev_step_hash": prev_hash,
            "step_hash": step_hash,
        }

        steps.append(canonical_step)
        prev_hash = step_hash

    instance_hint = {
        "path": str(path),
        "initial_state": steps[0]["pre_state"] if steps else {},
        "final_state": steps[-1]["post_state"] if steps else {},
        "instruction_sequence": [step["instruction"] for step in steps],
    }

    converted = {
        "version": "1.0",
        "instance_hash": hash_payload(instance_hint),
        "mu_total": mu_total,
        "step_count": len(steps),
        "final_claim": observation.get("event", {}).get("tag", "UNKNOWN") if steps else "UNKNOWN",
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "steps": steps,
    }
    return converted


def migrate_file(path: Path, dry_run: bool = False) -> bool:
    try:
        with path.open("r", encoding="utf-8") as handle:
            data = json.load(handle)
    except (OSError, json.JSONDecodeError):
        return False

    if detect_legacy_steps(data):
        converted = convert_step_list(path, data)
        if dry_run:
            return True
        with path.open("w", encoding="utf-8") as handle:
            json.dump(converted, handle, indent=2)
            handle.write("\n")
        return True

    return False


def iter_candidate_files(root_dirs: Iterable[Path]) -> Iterable[Path]:
    for directory in root_dirs:
        for path in directory.glob("*.json"):
            if path.is_file():
                yield path


def main() -> None:
    parser = argparse.ArgumentParser(description="Migrate legacy Thiele Machine receipt JSON files")
    parser.add_argument("--dry-run", action="store_true", help="Report files that would be migrated without modifying them")
    parser.add_argument(
        "paths",
        nargs="*",
        default=["receipts", "examples"],
        help="Directories to scan for legacy receipts",
    )
    args = parser.parse_args()

    targets = [Path(p).resolve() for p in args.paths]
    migrated = []
    for file_path in iter_candidate_files(targets):
        if migrate_file(file_path, dry_run=args.dry_run):
            migrated.append(file_path)

    if args.dry_run:
        if migrated:
            print("Files requiring migration:")
            for path in migrated:
                print(f"  - {path}")
        else:
            print("No legacy receipts detected.")
    else:
        if migrated:
            print("Migrated receipts:")
            for path in migrated:
                print(f"  - {path}")
        else:
            print("No legacy receipts converted.")


if __name__ == "__main__":
    main()
