"""Acceptance checks for Part 1 Item 1.5's conjecture boundary."""

import csv
from hashlib import sha256
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ROUND = ROOT / "research/rounds"
LEDGER = ROUND / "2026-09-30-part1-item1.5-round1-occurrences.tsv"
RESULT = ROUND / "2026-09-30-part1-item1.5-round1-results.md"
FROZEN_REF = "4888677e^"
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


def test_occurrence_ledger_covers_the_exact_frozen_surface() -> None:
    assert LEDGER.exists()
    with LEDGER.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    assert len(rows) == 40
    assert set(rows[0]) == {
        "document", "line", "line_sha256", "frozen_text", "classification",
        "evidence", "scope_text", "note"
    }
    keyed = {(row["document"], int(row["line"])): row for row in rows}
    expected = {}
    for document in INPUTS:
        for number, line in enumerate(frozen_lines(document), 1):
            if PATTERN.search(line):
                expected[(document, number)] = line
    assert set(keyed) == set(expected)
    for key, line in expected.items():
        row = keyed[key]
        assert row["line_sha256"] == sha256(line.encode()).hexdigest()
        assert row["frozen_text"] == line
        assert row["classification"] in {
            "conjecture-open", "proved-local-model", "scope-boundary", "nonclaim",
            "overclaim",
        }
        assert row["evidence"].strip()
        assert row["scope_text"].strip()
        assert row["note"].strip()


def test_frozen_headlines_and_chapter_keep_the_conjecture_open() -> None:
    monograph = "\n".join(frozen_lines("monograph/monograph.tex"))
    readme = "\n".join(frozen_lines("README.md"))
    distillation = "\n".join(frozen_lines("THIELE_MACHINE.txt"))
    spec = "\n".join(frozen_lines("monograph/thiele_machine_math_spec.tex"))
    release = "\n".join(frozen_lines(INPUTS[-1]))
    assert r"\section{The pointer-observable conjecture}" in monograph
    assert "stated as a conjecture and nothing more" in monograph
    assert "Five proofs about chosen models do not settle those choices" in monograph
    assert "pointer question. It is open" in readme
    assert "pointer question. It is open" in distillation
    assert "evidence for the pointer-observable conjecture, not a proof of it" in spec
    assert "Nothing here settles it" in release


def test_round1_counterexample_is_exact() -> None:
    line = frozen_lines("README.md")[599]
    assert "pointer-observable criterion" in line
    assert "frontier-criterion theorems" in line


def test_item15_round1_result_is_closed() -> None:
    assert RESULT.exists()
    text = RESULT.read_text()
    assert "Outcome: REFUTED" in text
    assert "40 / 40" in text
    assert "README.md:600" in text
    assert "Adversarial read: NOT PASS" in text
    assert "not proved or refuted by this item" in text
