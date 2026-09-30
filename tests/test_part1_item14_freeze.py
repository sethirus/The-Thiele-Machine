"""Integrity checks for the Part 1 Item 1.4 documentation-audit freeze."""

from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FREEZE = ROOT / "research/rounds/2026-09-30-part1-item1.4-round1-freeze.md"

INPUTS = {
    "README.md": "96cf5b2209b64f7c8bfd3968323ab89fbc0c4bdc807e27fec9d05bf7905e372e",
    "monograph/monograph.tex": "78d983e0e1601e42aabd1feb1e1f307cb236c7fa598061369f1c1b47461d8792",
    "monograph/thiele_machine_math_spec.tex": "143889c1172fa668943005e35d2e2b97aa3451e5ac13377a813e3f5f78cfa659",
    "THIELE_MACHINE.txt": "a6f00acf52e13c90e02a84a0c395748964a2f7d6024802190dab2ae091eae95b",
    "CITATION.cff": "7b13319e3dfa245213b91a508469f179e4e6e8431690705908d5e72d285c84d7",
    "research/rounds/inputs/2026-09-30-v3.4.0-release-notes.md":
        "587ff9131c86d128d2eb3349c866894c382590964017495a516086bea1ac4182",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_frozen_inputs_have_exact_hashes() -> None:
    assert FREEZE.exists()
    text = FREEZE.read_text()
    for name, expected in INPUTS.items():
        assert digest(ROOT / name) == expected
        assert f"`{name}` | `{expected}`" in text


def test_freeze_pins_exact_outcome_and_acceptance_surface() -> None:
    text = FREEZE.read_text()
    assert "Prediction: PROVED." in text
    assert "every one of the 8,156 physical input lines" in text
    assert "matched, open-labeled, corrected, or nonclaim" in text
    assert "No row may be omitted" in text
    assert "three genuinely different strategies" in text
