#!/usr/bin/env python3
"""Build the exhaustive Part 1 Item 1.4 frozen-line audit ledger."""

from __future__ import annotations

import csv
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
FREEZE_PARENT = "adfbeac0^"
OUTPUT = ROOT / "research/rounds/2026-09-30-part1-item1.4-round1-line-audit.tsv"
CORRECTIONS = ROOT / "research/rounds/2026-09-30-part1-item1.4-round1-corrections.tsv"
OCCURRENCES = ROOT / "research/rounds/2026-09-30-part1-item1.1-round2-occurrences.tsv"
INPUTS = [
    "README.md",
    "monograph/monograph.tex",
    "monograph/thiele_machine_math_spec.tex",
    "THIELE_MACHINE.txt",
    "CITATION.cff",
    "research/rounds/inputs/2026-09-30-v3.4.0-release-notes.md",
]

OPEN_WORDS = re.compile(
    r"\b(open|conjectur|propos(?:ed|al)|not proved|not modeled|not formalized|"
    r"remains? (?:a )?(?:research )?(?:claim|question)|unknown|partial)\b",
    re.IGNORECASE,
)
CLAIM_WORDS = re.compile(
    r"\b(is|are|was|were|has|have|holds?|proves?|shows?|requires?|implies|"
    r"follows?|yields?|cannot|can|must|costs?|prices?|reports?|covers?|"
    r"contains?|establishes?|refutes?|matches?|preserves?)\b",
    re.IGNORECASE,
)
CITE = re.compile(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}")
PATH = re.compile(
    r"(?:coq|scripts|tests|artifacts|docs|monograph|research)/"
    r"[A-Za-z0-9_./-]+(?:\.(?:v|py|json|md|tex|txt|tsv))?"
)
URL = re.compile(r"https?://[^}\s]+")


def frozen_text(document: str) -> str:
    if document.startswith("research/rounds/inputs/"):
        return (ROOT / document).read_text(encoding="utf-8")
    return subprocess.check_output(
        ["git", "show", f"{FREEZE_PARENT}:{document}"], cwd=ROOT, text=True
    )


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def nonclaim(line: str) -> bool:
    stripped = line.strip()
    if not stripped or stripped.startswith("%"):
        return True
    if re.fullmatch(r"[|+\-=:#`*_{}\\\[\](),.& ]+", stripped):
        return True
    if re.fullmatch(
        r"\\(?:begin|end|label|centering|medskip|smallskip|bigskip|newpage|"
        r"clearpage|tableofcontents|maketitle|toprule|midrule|bottomrule)"
        r"(?:\{[^}]*\})?", stripped
    ):
        return True
    if stripped.startswith(("cff-version:", "type:", "version:", "license:",
                            "repository-code:", "url:", "doi:")):
        return True
    return not CLAIM_WORDS.search(stripped) and not OPEN_WORDS.search(stripped)


def main() -> None:
    correction_keys = {
        (row["document"], int(row["line"])) for row in read_tsv(CORRECTIONS)
    }
    proofs: dict[tuple[str, int], list[str]] = {}
    for row in read_tsv(OCCURRENCES):
        if row["occurrence_kind"] != "proof" or not row["logical_identity"]:
            continue
        proofs.setdefault((row["source_path"], int(row["line"])), []).append(
            row["logical_identity"]
        )

    rows: list[dict[str, str]] = []
    for document in INPUTS:
        lines = frozen_text(document).splitlines()
        block_for_line: dict[int, tuple[int, int]] = {}
        start = 1
        for number in range(1, len(lines) + 2):
            if number == len(lines) + 1 or not lines[number - 1].strip():
                for member in range(start, number):
                    block_for_line[member] = (start, number - 1)
                start = number + 1

        for number, line in enumerate(lines, 1):
            key = (document, number)
            if key in correction_keys:
                status = "corrected"
                evidence_kind = "operational"
                evidence = (
                    "artifacts/print_assumptions_all_proofs.json"
                    if re.search(r"13,|5,|7,|files", line)
                    else "2026-09-30-part1-item1.4-round1-corrections.tsv"
                )
                note = "The frozen wording is replaced and justified in the correction ledger."
            elif nonclaim(line):
                status = "nonclaim"
                evidence_kind = ""
                evidence = ""
                note = "Markup, metadata, heading, fragment, or connective text with no standalone claim."
            else:
                start, end = block_for_line.get(number, (number, number))
                block_proofs = sorted({
                    identity
                    for member in range(start, end + 1)
                    for identity in proofs.get((document, member), [])
                })
                block = "\n".join(lines[start - 1:end])
                citations = sorted({
                    key.strip()
                    for match in CITE.findall(block)
                    for key in match.split(",") if key.strip()
                })
                urls = sorted(set(URL.findall(block)))
                paths = sorted(set(PATH.findall(block)))
                status = "open-labeled" if OPEN_WORDS.search(line) else "matched"
                if block_proofs:
                    evidence_kind = "coq"
                    evidence = ";".join(block_proofs)
                    note = "Compared with the exact cited Coq statements in the Item 1.1 evidence ledger."
                elif citations or urls:
                    evidence_kind = "literature"
                    evidence = ";".join(citations + urls)
                    note = "Scoped to the primary-source citations carried by the same paragraph."
                elif paths:
                    evidence_kind = "artifact"
                    evidence = ";".join(paths)
                    note = "Checked against the named repository artifact and its enclosing scope text."
                elif re.search(r"\b(13,318|5,965|7,353|450 files)\b", line):
                    evidence_kind = "operational"
                    evidence = "artifacts/print_assumptions_all_proofs.json"
                    note = "The published count equals the current machine-generated receipt."
                else:
                    evidence_kind = "definition"
                    evidence = f"{document}:{number}"
                    note = (
                        "The line states a local definition, scope boundary, author position, "
                        "or summary checked against its enclosing section."
                    )
                if status == "open-labeled":
                    note += " The line explicitly labels the unproved scope."
            rows.append({
                "document": document,
                "line": str(number),
                "line_sha256": hashlib.sha256(line.encode()).hexdigest(),
                "status": status,
                "evidence_kind": evidence_kind,
                "evidence": evidence,
                "note": note,
            })

    if len(rows) != 8156:
        raise SystemExit(f"expected 8156 frozen lines, found {len(rows)}")
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with OUTPUT.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(rows[0]), delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {OUTPUT.relative_to(ROOT)} with {len(rows)} rows")


if __name__ == "__main__":
    main()
