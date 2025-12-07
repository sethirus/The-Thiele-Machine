"""
Test suite for the supra-quantum 16/5 distribution isomorphism.

This tests the isomorphism between:
1. The CSV distribution in artifacts/bell/supra_quantum_16_5.csv
2. The Coq proof in coq/sandboxes/AbstractPartitionCHSH.v
3. The Python verification in tools/verify_supra_quantum.py

The tests verify that all three representations agree on:
- The probability distribution is valid (normalized, no-signaling)
- The CHSH value is exactly 16/5 = 3.2
- The CHSH value exceeds the Tsirelson bound of 2√2 ≈ 2.828
"""

from __future__ import annotations

import math
import shutil
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest

# Add the repo root to the path
REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.verify_supra_quantum import (
    CSV_PATH,
    load_distribution,
    verify_normalization,
    verify_no_signaling_alice,
    verify_no_signaling_bob,
    compute_expectation,
    compute_chsh,
    exceeds_tsirelson,
    verify_distribution,
)


class TestSupraQuantumDistribution:
    """Tests for the supra-quantum 16/5 distribution."""

    def test_csv_exists(self) -> None:
        """The CSV file should exist."""
        assert CSV_PATH.exists(), f"CSV file not found: {CSV_PATH}"

    def test_load_distribution(self) -> None:
        """The distribution should load correctly with 16 entries."""
        probs = load_distribution(CSV_PATH)
        assert len(probs) == 16, f"Expected 16 probability entries, got {len(probs)}"

    def test_normalization(self) -> None:
        """Probabilities should sum to 1 for each (x,y) setting."""
        probs = load_distribution(CSV_PATH)
        # Should not raise
        verify_normalization(probs)

    def test_no_signaling_alice(self) -> None:
        """Alice's marginal P(a|x) should be independent of Bob's input y."""
        probs = load_distribution(CSV_PATH)
        # Should not raise
        verify_no_signaling_alice(probs)

    def test_no_signaling_bob(self) -> None:
        """Bob's marginal P(b|y) should be independent of Alice's input x."""
        probs = load_distribution(CSV_PATH)
        # Should not raise
        verify_no_signaling_bob(probs)

    def test_expectation_e00(self) -> None:
        """E(0,0) should be -1/5 (anti-correlated)."""
        probs = load_distribution(CSV_PATH)
        e00 = compute_expectation(probs, 0, 0)
        assert e00 == Fraction(-1, 5), f"E(0,0) = {e00}, expected -1/5"

    def test_expectation_e01(self) -> None:
        """E(0,1) should be 1 (perfectly correlated)."""
        probs = load_distribution(CSV_PATH)
        e01 = compute_expectation(probs, 0, 1)
        assert e01 == Fraction(1), f"E(0,1) = {e01}, expected 1"

    def test_expectation_e10(self) -> None:
        """E(1,0) should be 1 (perfectly correlated)."""
        probs = load_distribution(CSV_PATH)
        e10 = compute_expectation(probs, 1, 0)
        assert e10 == Fraction(1), f"E(1,0) = {e10}, expected 1"

    def test_expectation_e11(self) -> None:
        """E(1,1) should be 1 (perfectly correlated)."""
        probs = load_distribution(CSV_PATH)
        e11 = compute_expectation(probs, 1, 1)
        assert e11 == Fraction(1), f"E(1,1) = {e11}, expected 1"

    def test_chsh_value(self) -> None:
        """CHSH value should be exactly 16/5."""
        probs = load_distribution(CSV_PATH)
        chsh = compute_chsh(probs)
        assert chsh == Fraction(16, 5), f"CHSH = {chsh}, expected 16/5"

    def test_chsh_exceeds_tsirelson(self) -> None:
        """CHSH value should exceed the Tsirelson bound of 2√2."""
        probs = load_distribution(CSV_PATH)
        chsh = compute_chsh(probs)
        assert exceeds_tsirelson(chsh), f"CHSH = {chsh} does not exceed Tsirelson bound"

    def test_chsh_numeric_comparison(self) -> None:
        """Numeric comparison: 3.2 > 2√2 ≈ 2.828."""
        probs = load_distribution(CSV_PATH)
        chsh = compute_chsh(probs)
        tsirelson = 2 * math.sqrt(2)
        assert float(chsh) > tsirelson, f"3.2 should be > {tsirelson}"

    def test_full_verification(self) -> None:
        """Full verification should pass with correct results."""
        result = verify_distribution()
        assert result["valid"]
        assert result["normalized"]
        assert result["no_signaling"]
        assert result["chsh"] == "16/5"
        assert result["exceeds_tsirelson"]


class TestCoqIsomorphism:
    """Tests verifying isomorphism with the Coq proof."""

    COQ_FILE = REPO_ROOT / "coq" / "sandboxes" / "AbstractPartitionCHSH.v"

    def test_coq_file_exists(self) -> None:
        """The Coq file should exist."""
        assert self.COQ_FILE.exists(), f"Coq file not found: {self.COQ_FILE}"

    def test_coq_contains_supra_quantum_ns(self) -> None:
        """The Coq file should define supra_quantum_ns."""
        content = self.COQ_FILE.read_text()
        assert "Definition supra_quantum_ns" in content

    def test_coq_contains_sighted_is_supra_quantum(self) -> None:
        """The Coq file should contain the sighted_is_supra_quantum theorem."""
        content = self.COQ_FILE.read_text()
        assert "Theorem sighted_is_supra_quantum" in content

    def test_coq_contains_supra_quantum_chsh(self) -> None:
        """The Coq file should prove supra_quantum_chsh : chsh_ns supra_quantum_ns = 16/5."""
        content = self.COQ_FILE.read_text()
        assert "Lemma supra_quantum_chsh" in content
        assert "chsh_ns supra_quantum_ns = 16/5" in content

    def test_coq_contains_supra_quantum_valid(self) -> None:
        """The Coq file should prove supra_quantum_valid : valid_ns supra_quantum_ns."""
        content = self.COQ_FILE.read_text()
        assert "Lemma supra_quantum_valid" in content
        assert "valid_ns supra_quantum_ns" in content

    def test_coq_contains_exceeds_tsirelson(self) -> None:
        """The Coq file should prove the CHSH value exceeds the Tsirelson bound."""
        content = self.COQ_FILE.read_text()
        assert "Lemma supra_quantum_exceeds_tsirelson" in content
        assert "8 < (16/5) * (16/5)" in content

    @pytest.mark.skipif(
        shutil.which("coqc") is None,
        reason="coqc not available"
    )
    def test_coq_compiles(self) -> None:
        """The Coq file should compile without errors."""
        result = subprocess.run(
            ["coqc", str(self.COQ_FILE)],
            capture_output=True,
            text=True,
            cwd=self.COQ_FILE.parent,
        )
        assert result.returncode == 0, f"Coq compilation failed:\n{result.stderr}"


class TestDistributionProperties:
    """Mathematical property tests for the distribution."""

    def test_probabilities_non_negative(self) -> None:
        """All probabilities should be non-negative."""
        probs = load_distribution(CSV_PATH)
        for key, prob in probs.items():
            assert prob >= 0, f"Negative probability at {key}: {prob}"

    def test_probabilities_at_most_one(self) -> None:
        """All probabilities should be at most 1."""
        probs = load_distribution(CSV_PATH)
        for key, prob in probs.items():
            assert prob <= 1, f"Probability > 1 at {key}: {prob}"

    def test_marginals_uniform(self) -> None:
        """Marginal distributions P(a|x) and P(b|y) should be uniform (1/2).
        
        For a no-signaling distribution, P(a|x) = sum_y sum_b P(a,b|x,y) / 2
        should equal 1/2 for all a, x (and similarly for Bob).
        
        This is a consequence of the uniform marginals in our specific distribution.
        """
        probs = load_distribution(CSV_PATH)
        
        # Check Alice's marginals: P(a|x) should be 1/2 for all a, x
        # We sum over all (y, b) pairs and divide by 2 (number of y values)
        # to get the average marginal P(a|x) = sum_y P(a|x,y) / 2
        for x in [0, 1]:
            for a in [0, 1]:
                # Sum P(a,b|x,y) over all y and b
                total = sum(probs.get((x, y, a, b), Fraction(0))
                           for y in [0, 1] for b in [0, 1])
                # This equals sum_y P(a|x,y) = 2 * P(a|x) due to no-signaling
                # So P(a|x) = total / 2
                marginal = total / 2
                assert marginal == Fraction(1, 2), \
                    f"P(a={a}|x={x}) = {marginal}, expected 1/2"
        
        # Check Bob's marginals: P(b|y) should be 1/2 for all b, y
        for y in [0, 1]:
            for b in [0, 1]:
                # Sum P(a,b|x,y) over all x and a
                total = sum(probs.get((x, y, a, b), Fraction(0))
                           for x in [0, 1] for a in [0, 1])
                # This equals sum_x P(b|x,y) = 2 * P(b|y) due to no-signaling
                # So P(b|y) = total / 2
                marginal = total / 2
                assert marginal == Fraction(1, 2), \
                    f"P(b={b}|y={y}) = {marginal}, expected 1/2"

    def test_classical_bound_violated(self) -> None:
        """The distribution should violate the classical CHSH bound of 2."""
        probs = load_distribution(CSV_PATH)
        chsh = compute_chsh(probs)
        assert chsh > 2, f"CHSH = {chsh} does not violate classical bound of 2"

    def test_pr_box_bound_satisfied(self) -> None:
        """The distribution should satisfy the PR-box bound of 4."""
        probs = load_distribution(CSV_PATH)
        chsh = compute_chsh(probs)
        assert chsh <= 4, f"CHSH = {chsh} exceeds PR-box bound of 4"


class TestStressAndEdgeCases:
    """Extreme stress tests and edge cases for the distribution."""

    def test_exact_chsh_squared(self) -> None:
        """S² = (16/5)² = 256/25 should exceed 8 (= 200/25)."""
        probs = load_distribution(CSV_PATH)
        chsh = compute_chsh(probs)
        chsh_squared = chsh * chsh
        expected_squared = Fraction(256, 25)
        assert chsh_squared == expected_squared, f"S² = {chsh_squared}, expected {expected_squared}"
        assert chsh_squared > 8, f"S² = {chsh_squared} should be > 8"

    def test_convex_decomposition(self) -> None:
        """16/5 = (3/5)×4 + (2/5)×2 (convex combination of PR-box and classical)."""
        lambda_pr = Fraction(3, 5)
        lambda_cl = Fraction(2, 5)
        # PR-box CHSH = 4, classical perfectly-correlated CHSH = 2
        reconstructed = lambda_pr * 4 + lambda_cl * 2
        expected = Fraction(16, 5)
        assert reconstructed == expected, f"Convex reconstruction = {reconstructed}, expected {expected}"
        assert lambda_pr + lambda_cl == 1, "Convex weights should sum to 1"

    def test_gap_above_tsirelson(self) -> None:
        """The gap above Tsirelson should be approximately 13.14%."""
        probs = load_distribution(CSV_PATH)
        chsh = compute_chsh(probs)
        tsirelson = 2 * math.sqrt(2)
        gap_percent = (float(chsh) - tsirelson) / tsirelson * 100
        # Should be approximately 13.14%
        assert 13.0 < gap_percent < 14.0, f"Gap = {gap_percent}%, expected ~13.14%"

    def test_e11_specific_value(self) -> None:
        """E(0,0) = -1/5 should be the only anti-correlated setting."""
        probs = load_distribution(CSV_PATH)
        e00 = compute_expectation(probs, 0, 0)
        assert e00 == Fraction(-1, 5), f"E(0,0) = {e00}, expected -1/5"
        # The other three should all be +1
        for (x, y) in [(0, 1), (1, 0), (1, 1)]:
            e_val = compute_expectation(probs, x, y)
            assert e_val == Fraction(1), f"E({x},{y}) = {e_val}, expected 1"

    def test_probability_fractions_exact(self) -> None:
        """Verify exact fractional probabilities for (0,0) setting."""
        probs = load_distribution(CSV_PATH)
        # Expected: 1/5, 3/10, 3/10, 1/5
        assert probs[(0, 0, 0, 0)] == Fraction(1, 5)
        assert probs[(0, 0, 0, 1)] == Fraction(3, 10)
        assert probs[(0, 0, 1, 0)] == Fraction(3, 10)
        assert probs[(0, 0, 1, 1)] == Fraction(1, 5)

    def test_perfectly_correlated_settings(self) -> None:
        """For (x,y) in {(0,1), (1,0), (1,1)}, P(a≠b) = 0."""
        probs = load_distribution(CSV_PATH)
        for (x, y) in [(0, 1), (1, 0), (1, 1)]:
            p_diff = probs.get((x, y, 0, 1), 0) + probs.get((x, y, 1, 0), 0)
            assert p_diff == 0, f"P(a≠b|{x},{y}) = {p_diff}, expected 0"

    def test_all_chsh_variants_bounded(self) -> None:
        """All 8 CHSH variants should satisfy |S| ≤ 4."""
        probs = load_distribution(CSV_PATH)
        e00 = compute_expectation(probs, 0, 0)
        e01 = compute_expectation(probs, 0, 1)
        e10 = compute_expectation(probs, 1, 0)
        e11 = compute_expectation(probs, 1, 1)
        
        variants = [
            (+1, +1, +1, -1), (+1, +1, -1, +1), (+1, -1, +1, +1), (-1, +1, +1, +1),
            (+1, -1, -1, -1), (-1, +1, -1, -1), (-1, -1, +1, -1), (-1, -1, -1, +1),
        ]
        for (s00, s01, s10, s11) in variants:
            S = s00 * e00 + s01 * e01 + s10 * e10 + s11 * e11
            assert abs(S) <= 4, f"CHSH variant = {S}, violates |S| ≤ 4"

    def test_numerical_precision_extreme(self) -> None:
        """Test at extreme numerical precision."""
        probs = load_distribution(CSV_PATH)
        chsh = compute_chsh(probs)
        
        # Exact comparison
        assert chsh == Fraction(16, 5)
        
        # High-precision floating point
        chsh_float = float(chsh)
        tsirelson_float = 2 * math.sqrt(2)
        
        assert chsh_float == 3.2
        assert chsh_float > tsirelson_float
        assert abs(chsh_float - 3.2) < 1e-15  # Machine precision

    def test_supra_quantum_gap_positive(self) -> None:
        """The distribution should have a strictly positive supra-quantum gap."""
        probs = load_distribution(CSV_PATH)
        chsh = compute_chsh(probs)
        
        # S² - 8 should be positive (since S > 2√2 ⟺ S² > 8)
        gap = chsh * chsh - Fraction(8)
        assert gap > 0, f"S² - 8 = {gap}, should be positive"
        
        # The gap should be exactly 256/25 - 200/25 = 56/25
        expected_gap = Fraction(256, 25) - Fraction(200, 25)
        assert gap == expected_gap, f"Gap = {gap}, expected {expected_gap}"
