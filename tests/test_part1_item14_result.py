"""Acceptance checks for the Part 1 Item 1.4 line-by-line audit."""

from __future__ import annotations

import csv
import hashlib
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ROUND = ROOT / "research/rounds"
LEDGER = ROUND / "2026-09-30-part1-item1.4-round1-line-audit.tsv"
CORRECTIONS = ROUND / "2026-09-30-part1-item1.4-round1-corrections.tsv"
RESULTS = ROUND / "2026-09-30-part1-item1.4-round1-results.md"

INPUTS = [
    "README.md",
    "monograph/monograph.tex",
    "monograph/thiele_machine_math_spec.tex",
    "THIELE_MACHINE.txt",
    "CITATION.cff",
    "research/rounds/inputs/2026-09-30-v3.4.0-release-notes.md",
]
FREEZE_PARENT = "adfbeac0^"
RESULT_REF = "3f745351"


def rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def line_hash(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def frozen_text(document: str) -> str:
    if document.startswith("research/rounds/inputs/"):
        return (ROOT / document).read_text(encoding="utf-8")
    return subprocess.check_output(
        ["git", "show", f"{FREEZE_PARENT}:{document}"], cwd=ROOT, text=True
    )


def result_text(document: str) -> str:
    """Read the immutable publication produced by the audited Part 1 commit."""
    return subprocess.check_output(
        ["git", "show", f"{RESULT_REF}:{document}"], cwd=ROOT, text=True
    )


def test_line_ledger_covers_every_frozen_line_exactly() -> None:
    assert LEDGER.exists()
    assert b"\r" not in LEDGER.read_bytes()
    audit = rows(LEDGER)
    assert len(audit) == 8156
    assert set(audit[0]) == {
        "document", "line", "line_sha256", "status",
        "evidence_kind", "evidence", "note",
    }
    keyed = {(row["document"], int(row["line"])): row for row in audit}
    assert len(keyed) == len(audit)
    for document in INPUTS:
        frozen_lines = frozen_text(document).splitlines()
        for number, text in enumerate(frozen_lines, 1):
            row = keyed[(document, number)]
            assert row["line_sha256"] == line_hash(text)
            assert row["status"] in {
                "matched", "open-labeled", "corrected", "nonclaim"
            }
            if row["status"] != "nonclaim":
                assert row["evidence_kind"] in {
                    "coq", "definition", "literature", "artifact", "operational"
                }
                assert row["evidence"].strip()
                assert row["note"].strip()


def test_corrections_are_exact_frozen_to_current_replacements() -> None:
    assert CORRECTIONS.exists()
    audit = rows(LEDGER)
    corrections = rows(CORRECTIONS)
    corrected = {(row["document"], row["line"]) for row in audit
                 if row["status"] == "corrected"}
    recorded = {(row["document"], row["line"]) for row in corrections}
    assert corrected == recorded
    for row in corrections:
        assert row["original"].strip()
        assert row["replacement"].strip()
        assert row["reason"].strip()
        document = row["document"]
        number = int(row["line"])
        frozen_lines = frozen_text(document).splitlines()
        assert row["original"] == frozen_lines[number - 1]
        current_document = (
            "research/rounds/outputs/2026-09-30-v3.4.0-release-notes.md"
            if document.startswith("research/rounds/inputs/")
            else document
        )
        result_lines = result_text(current_document).splitlines()
        assert row["replacement"] == result_lines[number - 1]


def test_result_is_closed() -> None:
    assert RESULTS.exists()
    result = RESULTS.read_text()
    assert "Outcome: PROVED" in result
    assert "8,156 / 8,156" in result
    assert "Adversarial read: PASS" in result
