"""Post-freeze acceptance checks for Part 1 Item 1.3."""

from __future__ import annotations

import csv
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "coq/kernel/foundation/EventSwapTheorem.v"
EVIDENCE = ROOT / "research/rounds/2026-09-30-part1-item1.3-round1-evidence.tsv"
RESULTS = ROOT / "research/rounds/2026-09-30-part1-item1.3-round1-results.md"


def theorem_statement(source: str, name: str) -> str:
    match = re.search(
        rf"^Theorem\s+{re.escape(name)}\s*:\s*(.*?)\.[ \t]*$",
        source,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert match is not None, f"missing theorem declaration: {name}"
    return " ".join(match.group(1).split())


def test_item_13_exact_closed_outcomes() -> None:
    assert SOURCE.exists(), f"missing proof source: {SOURCE}"
    assert EVIDENCE.exists(), f"missing evidence: {EVIDENCE}"
    assert RESULTS.exists(), f"missing result report: {RESULTS}"

    source = SOURCE.read_text()
    assert theorem_statement(source, "item1_3_swap_refuted") == (
        "~ swap_preserves_main_results"
    )
    assert theorem_statement(source, "item1_3_certification_sanity") == (
        "certification_main_results"
    )

    with EVIDENCE.open(newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    assert len(rows) == 2
    assert set(rows[0]) == {
        "target",
        "predicted_outcome",
        "outcome",
        "result_name",
        "assumptions",
        "definitional",
        "built_in",
        "vacuity",
        "swap",
        "adversarial",
        "wrong_prediction",
        "note",
    }
    expected = [
        (
            "swap_preserves_main_results",
            "REFUTED",
            "REFUTED",
            "item1_3_swap_refuted",
        ),
        (
            "certification_main_results",
            "PROVED",
            "PROVED",
            "item1_3_certification_sanity",
        ),
    ]
    for row, values in zip(rows, expected, strict=True):
        assert tuple(row[key] for key in (
            "target", "predicted_outcome", "outcome", "result_name"
        )) == values
        assert row["assumptions"] == "closed"
        assert row["wrong_prediction"] == "no"
        for field in (
            "definitional", "built_in", "vacuity", "swap", "adversarial", "note"
        ):
            assert row[field].strip(), (row["target"], field)


def test_item_13_result_source_is_registered() -> None:
    project = (ROOT / "coq/_CoqProject").read_text().splitlines()
    assert "kernel/foundation/EventSwapTheorem.v" in project
    manifest = (ROOT / "scripts/vacuity_targets.json").read_text()
    assert '"path": "coq/kernel/foundation/EventSwapTheorem.v"' in manifest
