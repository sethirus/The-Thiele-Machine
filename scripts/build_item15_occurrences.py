#!/usr/bin/env python3
"""Build the frozen pointer-conjecture occurrence ledger for Item 1.5."""

from __future__ import annotations

import csv
from hashlib import sha256
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
FROZEN_REF = "4888677e^"
OUTPUT = ROOT / "research/rounds/2026-09-30-part1-item1.5-round1-occurrences.tsv"
INPUTS = [
    "monograph/monograph.tex",
    "README.md",
    "THIELE_MACHINE.txt",
    "monograph/thiele_machine_math_spec.tex",
    "research/rounds/outputs/2026-09-30-v3.4.0-release-notes.md",
]
PATTERN = re.compile(
    r"PointerObservable|pointer-observable|pointer observable|pointer conjecture|"
    r"pointer question|pointer criterion|"
    r"pointer\\_criterion|unique pointer|unique\\_pointer|sec:pointer|"
    r"unique-pointer|redundant record proliferation|"
    r"five proofs establish the criterion|five confirmations settle nothing|"
    r"stated as a conjecture and nothing more|proofs cannot make it for me|"
    r"correspondence to deployed signatures remains a modeling judgment",
    re.IGNORECASE,
)


def frozen_lines(document: str) -> list[str]:
    return subprocess.check_output(
        ["git", "show", f"{FROZEN_REF}:{document}"], cwd=ROOT, text=True
    ).splitlines()


def scope_block(lines: list[str], number: int) -> str:
    """Return the frozen paragraph containing a one-based line number."""
    index = number - 1
    start = index
    while start > 0 and lines[start - 1].strip():
        start -= 1
    end = index + 1
    while end < len(lines) and lines[end].strip():
        end += 1
    if start == index and end == index + 1:
        following = end
        while following < len(lines) and not lines[following].strip():
            following += 1
        following_end = following
        while following_end < len(lines) and lines[following_end].strip():
            following_end += 1
        end = following_end
    return " ".join(part.strip() for part in lines[start:end] if part.strip())


def classify(document: str, number: int, line: str) -> tuple[str, str, str]:
    lower = line.lower()
    if document == "README.md" and number == 600:
        return (
            "overclaim",
            "frozen README.md:600",
            "The sentence groups the pointer-observable criterion with theorems and therefore presents the general criterion as established.",
        )
    if line.lstrip().startswith((r"\section{", r"\label{", r"\multicolumn")):
        return (
            "nonclaim",
            "document structure",
            "A heading, label, or table divider; substantive status is checked in nearby rows.",
        )
    if any(marker in line for marker in (
        "PointerObservable.v} defines",
        "PointerObservableReductions.v} instantiates",
        "PointerObservableReductions.v} supplies",
        "Models of the five disciplines are unique pointers",
        "Proliferation / unique-pointer schema",
    )):
        return (
            "proved-local-model",
            "Kernel.PointerObservable; Kernel.PointerObservableReductions",
            "The definitions or selected synthetic model instances are proved; the line does not prove the real-system criterion.",
        )
    if any(marker in lower for marker in (
        "modeling input", "modeling claim", "not a proof", "correspondence",
        "models ask", "this kind:", "sanity instance", "model structure only",
        "open question of section", "borrowed", "not a derivation",
        "pointer observables win",
        "five proofs establish the criterion", "five confirmations settle nothing",
        "pointerobservablecounterexamples",
    )):
        return (
            "scope-boundary",
            "frozen enclosing paragraph and cited local-model declarations",
            "The line limits the formal result to definitions, chosen models, or analogy and leaves the general criterion unproved.",
        )
    return (
        "conjecture-open",
        "frozen document wording",
        "The line calls the criterion a conjecture, candidate, question, or open problem rather than a proved headline result.",
    )


def main() -> None:
    rows: list[dict[str, str]] = []
    for document in INPUTS:
        lines = frozen_lines(document)
        for number, line in enumerate(lines, 1):
            if not PATTERN.search(line):
                continue
            classification, evidence, note = classify(document, number, line)
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
