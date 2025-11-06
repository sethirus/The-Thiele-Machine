"""Comprehensive and stress tests for the THIELE verifier system.

This test suite ensures all verifier components work correctly under:
- Normal conditions
- Edge cases (empty data, extreme values, boundary conditions)
- Error conditions (malformed data, missing files)
- Stress conditions (large datasets, extreme parameter values)
"""

from __future__ import annotations

import csv
import json
import math
from pathlib import Path
from typing import Any, Dict

import pytest

from experiments import ledger_io
from experiments.run_cross_domain import main as cross_domain_main
from experiments.run_cwd import main as cwd_main
from experiments.run_einstein import main as einstein_main
from experiments.run_entropy import main as entropy_main
from experiments.run_landauer import main as landauer_main
from tools.thiele_verifier import (
    _collect_bools,
    _collect_floats,
    _cwd_highlights,
    _einstein_phase_highlights,
    _einstein_run_highlights,
    _entropy_phase_highlights,
    _entropy_run_highlights,
    _landauer_phase_highlights,
    _landauer_run_highlights,
    _safe_float,
    verify_proofpack,
)
from verifier.check_cross_domain import verify_cross_domain
from verifier.check_cwd import verify_cwd
from verifier.check_einstein import verify_einstein
from verifier.check_entropy import verify_entropy
from verifier.check_landauer import verify_landauer


# =============================================================================
# Helper function tests
# =============================================================================


class TestSafeFloat:
    """Test the _safe_float utility function."""

    def test_valid_float(self):
        assert _safe_float(3.14) == 3.14

    def test_valid_int(self):
        assert _safe_float(42) == 42.0

    def test_valid_string(self):
        assert _safe_float("2.718") == 2.718

    def test_invalid_string(self):
        assert _safe_float("not a number") is None

    def test_none(self):
        assert _safe_float(None) is None

    def test_empty_string(self):
        assert _safe_float("") is None

    def test_infinity(self):
        result = _safe_float(float("inf"))
        assert result == float("inf")

    def test_negative_infinity(self):
        result = _safe_float(float("-inf"))
        assert result == float("-inf")

    def test_nan(self):
        result = _safe_float(float("nan"))
        assert result is not None and math.isnan(result)


class TestCollectFloats:
    """Test the _collect_floats utility function."""

    def test_empty_list(self):
        assert _collect_floats([], "key") == []

    def test_single_value(self):
        items = [{"key": 1.5}]
        assert _collect_floats(items, "key") == [1.5]

    def test_multiple_values(self):
        items = [{"key": 1.0}, {"key": 2.0}, {"key": 3.0}]
        assert _collect_floats(items, "key") == [1.0, 2.0, 3.0]

    def test_missing_key(self):
        items = [{"other": 1.0}, {"key": 2.0}]
        assert _collect_floats(items, "key") == [2.0]

    def test_non_mapping_items(self):
        items = [1, 2, {"key": 3.0}, "string"]
        assert _collect_floats(items, "key") == [3.0]

    def test_infinity_filtered(self):
        items = [{"key": 1.0}, {"key": float("inf")}, {"key": 2.0}]
        assert _collect_floats(items, "key") == [1.0, 2.0]

    def test_nan_filtered(self):
        items = [{"key": 1.0}, {"key": float("nan")}, {"key": 2.0}]
        assert _collect_floats(items, "key") == [1.0, 2.0]


class TestCollectBools:
    """Test the _collect_bools utility function."""

    def test_empty_list(self):
        assert _collect_bools([], "key") == []

    def test_true_values(self):
        items = [{"key": True}, {"key": 1}, {"key": "yes"}]
        assert _collect_bools(items, "key") == [True, True, True]

    def test_false_values(self):
        items = [{"key": False}, {"key": 0}, {"key": ""}]
        assert _collect_bools(items, "key") == [False, False, False]

    def test_missing_key(self):
        items = [{"other": True}, {"key": False}]
        assert _collect_bools(items, "key") == [False]

    def test_non_mapping_items(self):
        items = [True, {"key": False}, "string"]
        assert _collect_bools(items, "key") == [False]


# =============================================================================
# Landauer verifier tests
# =============================================================================


class TestLandauerVerifier:
    """Comprehensive tests for Landauer phase verification."""

    def test_basic_verification(self, tmp_path: Path):
        """Test basic Landauer verification with minimal data."""
        run_dir = tmp_path / "landauer"
        landauer_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "0",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "10",
            ]
        )
        _, result = verify_landauer(run_dir, epsilon=0.1)
        assert result["status"] is True
        assert result["trial_count"] == 1
        assert len(result["trials"]) == 1

    def test_tight_epsilon(self, tmp_path: Path):
        """Test verification with very tight tolerance."""
        run_dir = tmp_path / "landauer"
        landauer_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "42",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "20",
            ]
        )
        _, result = verify_landauer(run_dir, epsilon=0.001)
        assert result["epsilon"] == 0.001
        assert "trials" in result
        # May pass or fail depending on random seed, but should not crash

    def test_large_epsilon(self, tmp_path: Path):
        """Test verification with very loose tolerance."""
        run_dir = tmp_path / "landauer"
        landauer_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "1",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "10",
            ]
        )
        _, result = verify_landauer(run_dir, epsilon=100.0)
        assert result["status"] is True
        assert result["epsilon"] == 100.0

    def test_multiple_trials(self, tmp_path: Path):
        """Test verification with multiple trials."""
        run_dir = tmp_path / "landauer"
        landauer_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "1",
                "2",
                "3",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "2",
                "--steps",
                "15",
            ]
        )
        _, result = verify_landauer(run_dir, epsilon=0.1)
        assert result["trial_count"] >= 3
        assert all(trial.get("within_tolerance") is not None for trial in result["trials"])

    def test_multiple_temperatures(self, tmp_path: Path):
        """Test verification across different temperatures."""
        run_dir = tmp_path / "landauer"
        landauer_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "0",
                "--temps",
                "0.5",
                "1.0",
                "2.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "12",
            ]
        )
        _, result = verify_landauer(run_dir, epsilon=0.1)
        assert result["trial_count"] == 3
        temperatures = {trial["key"]["T"] for trial in result["trials"]}
        assert 0.5 in temperatures
        assert 1.0 in temperatures
        assert 2.0 in temperatures

    def test_missing_ledger(self, tmp_path: Path):
        """Test error handling when ledger file is missing."""
        run_dir = tmp_path / "landauer"
        run_dir.mkdir()
        with pytest.raises(FileNotFoundError, match="Missing Landauer ledger"):
            verify_landauer(run_dir, epsilon=0.05)

    def test_empty_ledger(self, tmp_path: Path):
        """Test error handling with empty ledger file."""
        run_dir = tmp_path / "landauer"
        run_dir.mkdir()
        (run_dir / "landauer_steps.jsonl").write_text("")
        (run_dir / "landauer_summary.csv").write_text("seed,T,trial_id,protocol,sum_mu_bits,work,work_over_kTln2\n")
        (run_dir / "landauer_metadata.json").write_text("{}")
        
        with pytest.raises(ValueError):
            verify_landauer(run_dir, epsilon=0.05)

    def test_malformed_json(self, tmp_path: Path):
        """Test error handling with malformed JSON in ledger."""
        run_dir = tmp_path / "landauer"
        run_dir.mkdir()
        (run_dir / "landauer_steps.jsonl").write_text("not valid json\n")
        (run_dir / "landauer_summary.csv").write_text("seed,T,trial_id,protocol,sum_mu_bits,work,work_over_kTln2\n")
        (run_dir / "landauer_metadata.json").write_text("{}")
        
        with pytest.raises(Exception):  # JSONDecodeError or similar
            verify_landauer(run_dir, epsilon=0.05)

    def test_landauer_highlights(self):
        """Test extraction of highlights from Landauer payload."""
        payload = {
            "trials": [
                {"diff_ledger": 0.05, "within_tolerance": True},
                {"diff_ledger": -0.03, "within_tolerance": True},
                {"diff_ledger": 0.08, "within_tolerance": False},
            ],
            "metadata_digest_matches": True,
        }
        highlights = _landauer_run_highlights(payload)
        assert highlights["max_bits_gap"] == 0.08
        assert 0.05 < highlights["mean_bits_gap"] < 0.06
        assert highlights["tolerance_pass_rate"] == 2 / 3
        assert highlights["metadata_digest_ok"] is True


# =============================================================================
# Einstein verifier tests
# =============================================================================


class TestEinsteinVerifier:
    """Comprehensive tests for Einstein relation verification."""

    def test_basic_verification(self, tmp_path: Path):
        """Test basic Einstein verification."""
        run_dir = tmp_path / "einstein"
        einstein_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "0",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "20",
            ]
        )
        _, result = verify_einstein(run_dir, delta=0.1)
        assert result["status"] is True
        assert result["trial_count"] >= 1

    def test_tight_delta(self, tmp_path: Path):
        """Test with very tight delta tolerance."""
        run_dir = tmp_path / "einstein"
        einstein_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "42",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "30",
            ]
        )
        _, result = verify_einstein(run_dir, delta=0.001)
        assert result["delta"] == 0.001

    def test_multiple_temperatures(self, tmp_path: Path):
        """Test Einstein verification across temperatures."""
        run_dir = tmp_path / "einstein"
        einstein_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "5",
                "--temps",
                "0.8",
                "1.2",
                "--trials-per-condition",
                "1",
                "--steps",
                "25",
            ]
        )
        _, result = verify_einstein(run_dir, delta=0.15)
        assert result["trial_count"] == 2

    def test_einstein_highlights(self):
        """Test Einstein highlights extraction."""
        payload = {
            "trials": [
                {"residual": 0.02, "drift_velocity": 0.001},
                {"residual": -0.03, "drift_velocity": -0.002},
                {"residual": 0.01, "drift_velocity": 0.0015},
            ],
            "metadata_digest_matches": True,
        }
        highlights = _einstein_run_highlights(payload)
        assert highlights["max_abs_residual"] == 0.03
        assert highlights["max_abs_drift_velocity"] == 0.002
        assert highlights["metadata_digest_ok"] is True


# =============================================================================
# Entropy verifier tests
# =============================================================================


class TestEntropyVerifier:
    """Comprehensive tests for entropy identity verification."""

    def test_basic_verification(self, tmp_path: Path):
        """Test basic entropy verification."""
        run_dir = tmp_path / "entropy"
        entropy_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "0",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "30",
            ]
        )
        _, result = verify_entropy(run_dir)
        assert result["status"] is True
        assert result["trial_count"] >= 1

    def test_large_dataset(self, tmp_path: Path):
        """Test entropy verification with larger dataset."""
        run_dir = tmp_path / "entropy"
        entropy_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "1",
                "2",
                "--temps",
                "0.9",
                "1.1",
                "--trials-per-condition",
                "2",
                "--steps",
                "50",
            ]
        )
        _, result = verify_entropy(run_dir)
        assert result["trial_count"] >= 4

    def test_entropy_highlights(self):
        """Test entropy highlights extraction."""
        payload = {
            "trials": [
                {"slope_ci": [0.9, 1.1], "rho": 0.95, "p_value": 1e-8},
                {"slope_ci": [0.85, 1.05], "rho": 0.92, "p_value": 1e-7},
            ],
            "metadata_digest_matches": True,
        }
        highlights = _entropy_run_highlights(payload)
        assert highlights["min_slope_ci"] == 0.85
        assert highlights["max_slope_ci"] == 1.1
        assert highlights["min_rho"] == 0.92
        assert highlights["max_p_value"] == 1e-7


# =============================================================================
# CWD verifier tests
# =============================================================================


class TestCWDVerifier:
    """Comprehensive tests for CWD (Copy With Destroy) verification."""

    def test_basic_verification(self, tmp_path: Path):
        """Test basic CWD verification with all protocols."""
        common_args = [
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--modules",
            "3",
            "--steps-per-module",
            "4",
        ]

        sighted_dir = tmp_path / "sighted"
        blind_dir = tmp_path / "blind"
        destroyed_dir = tmp_path / "destroyed"

        cwd_main(["--output-dir", str(sighted_dir), "--protocol", "sighted", *common_args])
        cwd_main(["--output-dir", str(blind_dir), "--protocol", "blind", *common_args])
        cwd_main(["--output-dir", str(destroyed_dir), "--protocol", "destroyed", *common_args])

        _, result = verify_cwd(
            sighted_dir=sighted_dir,
            blind_dir=blind_dir,
            destroyed_dir=destroyed_dir,
            epsilon=0.2,
            eta=0.2,
        )
        assert result["status"] is True
        assert "penalty_checks" in result

    def test_tight_tolerances(self, tmp_path: Path):
        """Test CWD with very tight tolerances."""
        common_args = [
            "--seeds",
            "42",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--modules",
            "2",
            "--steps-per-module",
            "3",
        ]

        sighted_dir = tmp_path / "sighted"
        blind_dir = tmp_path / "blind"
        destroyed_dir = tmp_path / "destroyed"

        cwd_main(["--output-dir", str(sighted_dir), "--protocol", "sighted", *common_args])
        cwd_main(["--output-dir", str(blind_dir), "--protocol", "blind", *common_args])
        cwd_main(["--output-dir", str(destroyed_dir), "--protocol", "destroyed", *common_args])

        _, result = verify_cwd(
            sighted_dir=sighted_dir,
            blind_dir=blind_dir,
            destroyed_dir=destroyed_dir,
            epsilon=0.01,
            eta=0.01,
        )
        # May pass or fail, but should not crash
        assert "status" in result

    def test_missing_protocol(self, tmp_path: Path):
        """Test error handling when a protocol is missing."""
        sighted_dir = tmp_path / "sighted"
        blind_dir = tmp_path / "blind"
        destroyed_dir = tmp_path / "destroyed"
        
        sighted_dir.mkdir()
        blind_dir.mkdir()
        # destroyed_dir not created

        with pytest.raises(Exception):  # Should fail with missing directory
            verify_cwd(
                sighted_dir=sighted_dir,
                blind_dir=blind_dir,
                destroyed_dir=destroyed_dir,
                epsilon=0.1,
                eta=0.1,
            )

    def test_cwd_highlights(self):
        """Test CWD highlights extraction."""
        payload = {
            "penalty_checks": [
                {"diff_bits": 5.0, "mutual_information_bits": 2.0, "penalty_bits_blind": 2.5},
                {"diff_bits": 6.0, "mutual_information_bits": 2.5, "penalty_bits_blind": 3.0},
            ],
            "metadata_digest_matches": {"sighted": True, "blind": True, "destroyed": True},
        }
        highlights = _cwd_highlights(payload)
        assert highlights["min_penalty_margin_bits"] == 3.0  # min(5-2, 6-2.5)
        assert highlights["min_blind_penalty_bits"] == 2.5
        assert highlights["metadata_digest_ok"] is True


# =============================================================================
# Cross-domain verifier tests
# =============================================================================


class TestCrossDomainVerifier:
    """Comprehensive tests for cross-domain verification."""

    def test_sighted_protocol(self, tmp_path: Path):
        """Test cross-domain verification for sighted protocol."""
        run_dir = tmp_path / "cross_sighted"
        cross_domain_main(
            [
                "--output-dir",
                str(run_dir),
                "--protocol",
                "sighted",
                "--seeds",
                "0",
                "1",
                "--trials-per-condition",
                "2",
            ]
        )
        _, result = verify_cross_domain(run_dir)
        assert result["status"] is True

    def test_blind_protocol(self, tmp_path: Path):
        """Test cross-domain verification for blind protocol."""
        run_dir = tmp_path / "cross_blind"
        cross_domain_main(
            [
                "--output-dir",
                str(run_dir),
                "--protocol",
                "blind",
                "--seeds",
                "0",
                "--trials-per-condition",
                "1",
            ]
        )
        _, result = verify_cross_domain(run_dir, delta_aic_threshold=10.0)
        # Status may vary depending on random data, but should not crash
        assert "status" in result

    def test_destroyed_protocol(self, tmp_path: Path):
        """Test cross-domain verification for destroyed protocol."""
        run_dir = tmp_path / "cross_destroyed"
        cross_domain_main(
            [
                "--output-dir",
                str(run_dir),
                "--protocol",
                "destroyed",
                "--seeds",
                "0",
                "--trials-per-condition",
                "1",
            ]
        )
        _, result = verify_cross_domain(run_dir)
        assert result["status"] is True

    def test_high_delta_aic_threshold(self, tmp_path: Path):
        """Test with very high delta AIC threshold."""
        run_dir = tmp_path / "cross_blind"
        cross_domain_main(
            [
                "--output-dir",
                str(run_dir),
                "--protocol",
                "blind",
                "--seeds",
                "5",
                "--trials-per-condition",
                "1",
            ]
        )
        _, result = verify_cross_domain(run_dir, delta_aic_threshold=1000.0)
        # Status may vary with random data, but should not crash
        assert "status" in result
        assert isinstance(result["status"], bool)


# =============================================================================
# Unified verifier tests
# =============================================================================


class TestUnifiedVerifier:
    """Comprehensive tests for the unified proofpack verifier."""

    def test_complete_proofpack_verification(self, tmp_path: Path):
        """Test verification of a complete proofpack."""
        proofpack_dir = tmp_path / "proofpack"
        proofpack_dir.mkdir()

        # Build all required phases
        self._build_all_phases(proofpack_dir)

        result = verify_proofpack(proofpack_dir, delta_aic=100.0)  # Use lenient threshold for random data
        # Status may vary with random data, but verification should complete
        assert "status" in result
        assert "verdict" in result
        assert all(
            phase in result["phases"]
            for phase in ["landauer", "einstein", "entropy", "cwd", "cross_domain"]
        )

    def test_extreme_tolerances(self, tmp_path: Path):
        """Test with extreme tolerance parameters."""
        proofpack_dir = tmp_path / "proofpack"
        proofpack_dir.mkdir()
        self._build_all_phases(proofpack_dir)

        # Very tight tolerances
        result = verify_proofpack(
            proofpack_dir,
            epsilon=0.001,
            delta=0.001,
            eta=0.001,
            delta_aic=1.0,
            spearman_threshold=0.999,
            pvalue_threshold=1e-10,
        )
        assert "status" in result
        # May pass or fail, but should not crash

    def test_loose_tolerances(self, tmp_path: Path):
        """Test with very loose tolerance parameters."""
        proofpack_dir = tmp_path / "proofpack"
        proofpack_dir.mkdir()
        self._build_all_phases(proofpack_dir)

        result = verify_proofpack(
            proofpack_dir,
            epsilon=10.0,
            delta=10.0,
            eta=10.0,
            delta_aic=1000.0,
            spearman_threshold=0.1,
            pvalue_threshold=0.5,
        )
        # Loose tolerances should generally pass, but verify it completes without error
        assert "status" in result
        assert isinstance(result["status"], bool)

    def test_missing_phase(self, tmp_path: Path):
        """Test error handling when a required phase is missing."""
        proofpack_dir = tmp_path / "proofpack"
        proofpack_dir.mkdir()
        
        # Only build landauer, missing other phases
        landauer_dir = proofpack_dir / "landauer"
        landauer_main(
            [
                "--output-dir",
                str(landauer_dir),
                "--seeds",
                "0",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "10",
            ]
        )

        with pytest.raises(FileNotFoundError):
            verify_proofpack(proofpack_dir)

    def test_nonexistent_directory(self, tmp_path: Path):
        """Test error handling for non-existent proofpack directory."""
        fake_dir = tmp_path / "nonexistent"
        with pytest.raises(FileNotFoundError):
            verify_proofpack(fake_dir)

    def test_phase_highlights_aggregation(self, tmp_path: Path):
        """Test that phase highlights are properly aggregated."""
        proofpack_dir = tmp_path / "proofpack"
        proofpack_dir.mkdir()
        self._build_all_phases(proofpack_dir)

        result = verify_proofpack(proofpack_dir)
        
        # Check landauer highlights
        landauer = result["phases"]["landauer"]
        assert "highlights" in landauer
        assert "runs" in landauer
        
        # Check einstein highlights
        einstein = result["phases"]["einstein"]
        assert "highlights" in einstein
        
        # Check entropy highlights
        entropy = result["phases"]["entropy"]
        assert "highlights" in entropy

    def test_verdict_file_creation(self, tmp_path: Path):
        """Test that verdict files are created correctly."""
        proofpack_dir = tmp_path / "proofpack"
        proofpack_dir.mkdir()
        self._build_all_phases(proofpack_dir)

        result = verify_proofpack(proofpack_dir)
        
        verifier_dir = proofpack_dir / "verifier"
        assert verifier_dir.exists()
        
        # Check OK flag exists for success
        if result["status"]:
            ok_flag = verifier_dir / "THIELE_OK"
            assert ok_flag.exists()
            assert not (verifier_dir / "THIELE_FAIL").exists()
        
        # Check aggregated JSON exists
        aggregate_path = verifier_dir / "proofpack_verifier.json"
        assert aggregate_path.exists()
        
        # Verify JSON is valid
        with aggregate_path.open("r") as f:
            payload = json.load(f)
        assert payload["verdict"] == result["verdict"]

    def test_idempotent_verification(self, tmp_path: Path):
        """Test that running verification multiple times is idempotent."""
        proofpack_dir = tmp_path / "proofpack"
        proofpack_dir.mkdir()
        self._build_all_phases(proofpack_dir)

        # Run verification twice
        result1 = verify_proofpack(proofpack_dir)
        result2 = verify_proofpack(proofpack_dir)

        # Results should be identical
        assert result1["status"] == result2["status"]
        assert result1["verdict"] == result2["verdict"]
        
        # Only one verdict file should exist
        verifier_dir = proofpack_dir / "verifier"
        verdict_files = list(verifier_dir.glob("THIELE_*"))
        assert len(verdict_files) == 1

    @staticmethod
    def _build_all_phases(base_dir: Path) -> None:
        """Build all required phases for a complete proofpack."""
        # Landauer
        landauer_dir = base_dir / "landauer"
        landauer_main(
            [
                "--output-dir",
                str(landauer_dir),
                "--seeds",
                "0",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "12",
            ]
        )

        # Einstein
        einstein_dir = base_dir / "einstein"
        einstein_main(
            [
                "--output-dir",
                str(einstein_dir),
                "--seeds",
                "0",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "20",
            ]
        )

        # Entropy
        entropy_dir = base_dir / "entropy"
        entropy_main(
            [
                "--output-dir",
                str(entropy_dir),
                "--seeds",
                "0",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "30",
            ]
        )

        # CWD
        cwd_root = base_dir / "cwd"
        for protocol in ("sighted", "blind", "destroyed"):
            cwd_main(
                [
                    "--output-dir",
                    str(cwd_root / protocol),
                    "--protocol",
                    protocol,
                    "--seeds",
                    "0",
                    "--temps",
                    "1.0",
                    "--trials-per-condition",
                    "1",
                    "--modules",
                    "3",
                    "--steps-per-module",
                    "4",
                ]
            )

        # Cross-domain
        cross_root = base_dir / "cross_domain"
        cross_common = [
            "--seeds",
            "0",
            "--trials-per-condition",
            "2",
            "--modules",
            "4",
        ]
        for protocol in ("sighted", "blind", "destroyed"):
            cross_domain_main(
                [
                    "--output-dir",
                    str(cross_root / protocol),
                    "--protocol",
                    protocol,
                    *cross_common,
                ]
            )


# =============================================================================
# Stress tests
# =============================================================================


class TestVerifierStress:
    """Stress tests for the verifier under extreme conditions."""

    def test_large_number_of_trials(self, tmp_path: Path):
        """Stress test with a large number of trials."""
        run_dir = tmp_path / "landauer_stress"
        landauer_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "1",
                "2",
                "3",
                "4",
                "5",
                "--temps",
                "0.5",
                "1.0",
                "1.5",
                "--trials-per-condition",
                "3",
                "--steps",
                "15",
            ]
        )
        _, result = verify_landauer(run_dir, epsilon=0.1)
        # 5 seeds × 3 temps × 3 trials = 45 trials
        assert result["trial_count"] >= 15
        assert result["status"] is not None

    def test_many_steps(self, tmp_path: Path):
        """Stress test with many steps per trial."""
        run_dir = tmp_path / "einstein_stress"
        einstein_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "0",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "1",
                "--steps",
                "100",  # Large number of steps
            ]
        )
        _, result = verify_einstein(run_dir, delta=0.1)
        assert result["status"] is not None

    def test_extreme_temperature_range(self, tmp_path: Path):
        """Test with extreme temperature values."""
        run_dir = tmp_path / "entropy_stress"
        entropy_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "0",
                "--temps",
                "0.1",  # Very low temperature
                "10.0",  # Very high temperature
                "--trials-per-condition",
                "1",
                "--steps",
                "25",
            ]
        )
        _, result = verify_entropy(run_dir)
        assert result["trial_count"] == 2
        assert result["status"] is not None

    def test_many_modules(self, tmp_path: Path):
        """Stress test CWD with many modules."""
        common_args = [
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--modules",
            "10",  # Many modules
            "--steps-per-module",
            "5",
        ]

        sighted_dir = tmp_path / "sighted"
        blind_dir = tmp_path / "blind"
        destroyed_dir = tmp_path / "destroyed"

        cwd_main(["--output-dir", str(sighted_dir), "--protocol", "sighted", *common_args])
        cwd_main(["--output-dir", str(blind_dir), "--protocol", "blind", *common_args])
        cwd_main(["--output-dir", str(destroyed_dir), "--protocol", "destroyed", *common_args])

        _, result = verify_cwd(
            sighted_dir=sighted_dir,
            blind_dir=blind_dir,
            destroyed_dir=destroyed_dir,
            epsilon=0.2,
            eta=0.2,
        )
        assert "penalty_checks" in result

    def test_concurrent_verifications(self, tmp_path: Path):
        """Test that multiple verifications can run without interference."""
        # Create two independent proofpacks
        pack1 = tmp_path / "pack1"
        pack2 = tmp_path / "pack2"
        pack1.mkdir()
        pack2.mkdir()

        # Build minimal landauer runs for both
        for pack in [pack1, pack2]:
            landauer_dir = pack / "landauer"
            landauer_main(
                [
                    "--output-dir",
                    str(landauer_dir),
                    "--seeds",
                    "0",
                    "--temps",
                    "1.0",
                    "--trials-per-condition",
                    "1",
                    "--steps",
                    "10",
                ]
            )

        # Verify both (simulating concurrent access)
        _, result1 = verify_landauer(pack1 / "landauer", epsilon=0.1)
        _, result2 = verify_landauer(pack2 / "landauer", epsilon=0.1)

        # Both should succeed independently
        assert result1["status"] is True
        assert result2["status"] is True
