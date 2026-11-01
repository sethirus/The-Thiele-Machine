#!/usr/bin/env python3
"""Update the companion release record's two receipt fingerprints."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


def synchronize(record: Path, receipt: Path) -> None:
    data = receipt.read_bytes()
    digest = json.loads(data)["corpus_digest"]
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("receipt has no valid corpus digest")
    text = record.read_text(encoding="utf-8")
    for label, value, indent in (
        ("SHA-256", hashlib.sha256(data).hexdigest(), "          "),
        ("corpus digest", digest, "                "),
    ):
        text, count = re.subn(
            rf"{label} [0-9a-f]{{32}}\n\s+[0-9a-f]{{32}}",
            f"{label} {value[:32]}\n{indent}{value[32:]}", text,
        )
        if count != 1:
            raise ValueError(f"expected one {label} field, found {count}")
    record.write_text(text, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path, default=Path("monograph/COMPANION_CHECKS.txt"))
    parser.add_argument("--receipt", type=Path, default=Path("artifacts/print_assumptions_all_proofs.json"))
    args = parser.parse_args()
    synchronize(args.record, args.receipt)


if __name__ == "__main__":
    main()
