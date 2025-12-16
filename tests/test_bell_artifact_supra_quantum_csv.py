from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from tools.verify_supra_quantum import CSV_PATH, load_distribution, verify_distribution


def test_supra_quantum_csv_verifies() -> None:
    result = verify_distribution(CSV_PATH)
    assert result["valid"] is True
    assert result["chsh"] == "16/5"


def test_supra_quantum_csv_matches_expected_table() -> None:
    expected = {
        (0, 0, 0, 0): Fraction(1, 5),
        (0, 0, 1, 1): Fraction(1, 5),
        (0, 0, 0, 1): Fraction(3, 10),
        (0, 0, 1, 0): Fraction(3, 10),
        (0, 1, 0, 0): Fraction(1, 2),
        (0, 1, 1, 1): Fraction(1, 2),
        (0, 1, 0, 1): Fraction(0, 1),
        (0, 1, 1, 0): Fraction(0, 1),
        (1, 0, 0, 0): Fraction(1, 2),
        (1, 0, 1, 1): Fraction(1, 2),
        (1, 0, 0, 1): Fraction(0, 1),
        (1, 0, 1, 0): Fraction(0, 1),
        (1, 1, 0, 0): Fraction(1, 2),
        (1, 1, 1, 1): Fraction(1, 2),
        (1, 1, 0, 1): Fraction(0, 1),
        (1, 1, 1, 0): Fraction(0, 1),
    }

    probs = load_distribution(CSV_PATH)

    # Ensure the CSV contains exactly the expected 16 entries.
    assert set(probs.keys()) == set(expected.keys())
    for key, value in expected.items():
        assert probs[key] == value


def test_supra_quantum_csv_path_is_repo_relative() -> None:
    # Basic guardrail: ensure we didn't accidentally point at a temp file.
    repo_root = Path(__file__).resolve().parents[1]
    assert CSV_PATH == repo_root / "artifacts" / "bell" / "supra_quantum_16_5.csv"
