"""Freeze checks for the corrected Part 1 Item 1.5 Round 2 corpus."""

from hashlib import sha256
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
FREEZE = ROOT / "research/rounds/2026-10-01-part1-item1.5-round2-freeze.md"
FROZEN_REF = "10aeb40dde7cd02ca7d4a64c143e7d2335da546d"
INPUTS = {
    "monograph/monograph.tex": "045541ffafb66b8c0a54ff5914f9177d0705bbc0be4914eb84c21bec9f1c1428",
    "README.md": "79b0d348a251202ac5d8e9011f9762edc2ca9b273dbd227c3a56600272cc2f75",
    "THIELE_MACHINE.txt": "5f0159466a17e9f508465151cf85e81f549666c72a1fd5f64b8a003e525de6a2",
    "monograph/thiele_machine_math_spec.tex": "b0c7513ec7e6054401cc91c0b5e5278b7c533ce5efafa129efe596fc1b291fe5",
    "research/rounds/outputs/2026-09-30-v3.4.0-release-notes.md": "96750be0df5e1411f7e7f0e265e2731152d2bda64699886ebc0a6da15a8f4ff8",
}


def test_item15_round2_freeze_pins_corrected_inputs() -> None:
    assert FREEZE.exists()
    text = FREEZE.read_text()
    for relative, expected in INPUTS.items():
        frozen = subprocess.check_output(
            ["git", "show", f"{FROZEN_REF}:{relative}"], cwd=ROOT
        )
        assert sha256(frozen).hexdigest() == expected
        assert f"`{relative}` | `{expected}`" in text


def test_item15_round2_freezes_outcome_and_acceptance_before_result() -> None:
    text = FREEZE.read_text()
    normalized = " ".join(text.split())
    assert "Prediction: PROVED" in normalized
    assert "general pointer-observable criterion remains a labeled conjecture" in normalized
    assert "selected model instances may be stated as proved" in normalized
    assert "independent adversarial read must PASS" in normalized
    assert "Outcome: PROVED" not in text
