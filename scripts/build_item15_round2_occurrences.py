#!/usr/bin/env python3
"""Build the corrected frozen pointer-conjecture ledger for Item 1.5 Round 2."""

from __future__ import annotations

import csv
from hashlib import sha256
from pathlib import Path
import subprocess

from build_item15_occurrences import INPUTS, PATTERN, classify, scope_block


ROOT = Path(__file__).resolve().parents[1]
FROZEN_REF = "10aeb40dde7cd02ca7d4a64c143e7d2335da546d"
OUTPUT = ROOT / "research/rounds/2026-10-01-part1-item1.5-round2-occurrences.tsv"


def frozen_lines(document: str) -> list[str]:
    return subprocess.check_output(
        ["git", "show", f"{FROZEN_REF}:{document}"], cwd=ROOT, text=True
    ).splitlines()


def round2_classify(document: str, number: int, line: str) -> tuple[str, str, str]:
    if document == "README.md" and number == 600:
        return (
            "scope-boundary",
            "frozen README.md:600",
            "The sentence limits theorem status to formal definitions and selected model instances and explicitly leaves the general criterion conjectural.",
        )
    if document == "monograph/monograph.tex" and number == 4707:
        return (
            "scope-boundary",
            "frozen enclosing paragraph and cited local-model declarations",
            "The line identifies observer and event selection as a modeling choice that the formal proofs cannot settle.",
        )
    return classify(document, number, line)


def main() -> None:
    rows: list[dict[str, str]] = []
    for document in INPUTS:
        lines = frozen_lines(document)
        for number, line in enumerate(lines, 1):
            if not PATTERN.search(line):
                continue
            classification, evidence, note = round2_classify(document, number, line)
            rows.append({
                "document": document,
                "line": str(number),
                "line_sha256": sha256(line.encode()).hexdigest(),
                "frozen_text": line,
                "classification": classification,
                "evidence": evidence,
                "scope_text": scope_block(lines, number),
                "note": note,
            })
    if len(rows) != 40:
        raise SystemExit(f"expected 40 frozen occurrences, found {len(rows)}")
    with OUTPUT.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(rows[0]), delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {OUTPUT.relative_to(ROOT)} with {len(rows)} rows")


if __name__ == "__main__":
    main()
