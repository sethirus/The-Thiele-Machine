"""Integrity checks for the frozen Part 1 Item 1.2 target ledger.

These checks pin the inherited certification-specific universe and require
each row to name one exact Coq proposition.  They do not decide or prove any
of the predicted outcomes.
"""

from __future__ import annotations

import csv
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ITEM_11 = ROOT / "research/rounds/2026-09-30-part1-item1.1-round2-evidence.tsv"
TARGETS = ROOT / "research/rounds/2026-09-30-part1-item1.2-round1-targets.tsv"
COQ_TARGETS = ROOT / "coq/kernel/foundation/EventGeneralizationTargets.v"


def rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def test_item_12_freezes_every_item_11_certification_specific_identity() -> None:
    expected = [
        row["logical_identity"]
        for row in rows(ITEM_11)
        if row["observed_class"] == "C"
    ]
    frozen = rows(TARGETS)
    assert len(expected) == 55
    assert [row["logical_identity"] for row in frozen] == expected
    assert len({row["logical_identity"] for row in frozen}) == 55


def test_item_12_rows_bind_current_statements_and_exact_target_names() -> None:
    item_11 = {
        row["logical_identity"]: row
        for row in rows(ITEM_11)
        if row["observed_class"] == "C"
    }
    frozen = rows(TARGETS)
    assert set(frozen[0]) == {
        "logical_identity",
        "source_statement_sha256",
        "target_name",
        "predicted_outcome",
        "translation",
    }
    source = COQ_TARGETS.read_text()
    for row in frozen:
        identity = row["logical_identity"]
        assert row["source_statement_sha256"] == item_11[identity]["statement_sha256"]
        assert row["predicted_outcome"] in {"PROVED", "REFUTED", "BLOCKED"}
        assert row["translation"].strip()
        assert f"Definition {row['target_name']} : Prop" in source


def test_item_12_target_source_hash_is_recorded_in_freeze() -> None:
    freeze = (
        ROOT / "research/rounds/2026-09-30-part1-item1.2-round1-freeze.md"
    ).read_text()
    digest = hashlib.sha256(COQ_TARGETS.read_bytes()).hexdigest()
    assert f"target source: `{digest}`" in freeze
