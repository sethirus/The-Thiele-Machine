"""Freeze checks for Part 1 Item 1.5, the Chapter 26 status boundary."""

from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FREEZE = ROOT / "research/rounds/2026-09-30-part1-item1.5-round1-freeze.md"
INPUTS = {
    "monograph/monograph.tex": "045541ffafb66b8c0a54ff5914f9177d0705bbc0be4914eb84c21bec9f1c1428",
    "README.md": "1b4bdb6ecba6b39fe82de7aef7bb89fd271ba530eba0e1349386518e2f327fe9",
    "THIELE_MACHINE.txt": "5f0159466a17e9f508465151cf85e81f549666c72a1fd5f64b8a003e525de6a2",
    "monograph/thiele_machine_math_spec.tex": "b0c7513ec7e6054401cc91c0b5e5278b7c533ce5efafa129efe596fc1b291fe5",
    "research/rounds/outputs/2026-09-30-v3.4.0-release-notes.md": "96750be0df5e1411f7e7f0e265e2731152d2bda64699886ebc0a6da15a8f4ff8",
}


def test_item15_freeze_exists_and_pins_exact_inputs() -> None:
    assert FREEZE.exists()
    text = FREEZE.read_text()
    for relative, expected in INPUTS.items():
        actual = sha256((ROOT / relative).read_bytes()).hexdigest()
        assert actual == expected
        assert f"`{relative}` | `{expected}`" in text


def test_item15_freezes_outcome_and_acceptance_before_result() -> None:
    text = FREEZE.read_text()
    assert "Prediction: PROVED" in text
    assert "pointer-observable criterion remains a labeled conjecture" in text
    assert "not one of the proved headline claims" in text
    assert "independent adversarial read" in text
    assert "Outcome: PROVED" not in text
