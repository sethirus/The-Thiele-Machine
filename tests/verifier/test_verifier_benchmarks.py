"""Performance benchmarks for the THIELE verifier system.

This module contains performance benchmarks to measure verification speed
and resource usage under various conditions.

NOTE: These tests require the pytest-benchmark plugin.
Install with: pip install pytest-benchmark
Run with: pytest tests/verifier/test_verifier_benchmarks.py --benchmark-only
"""

from __future__ import annotations

import time
from pathlib import Path

import pytest

# Try to import benchmark support
try:
    import pytest_benchmark  # noqa: F401
    BENCHMARK_AVAILABLE = True
except ImportError:
    BENCHMARK_AVAILABLE = False

from experiments.run_cross_domain import main as cross_domain_main
from experiments.run_cwd import main as cwd_main
from experiments.run_einstein import main as einstein_main
from experiments.run_entropy import main as entropy_main
from experiments.run_landauer import main as landauer_main
from tools.thiele_verifier import verify_proofpack
from verifier.check_cross_domain import verify_cross_domain
from verifier.check_cwd import verify_cwd
from verifier.check_einstein import verify_einstein
from verifier.check_entropy import verify_entropy
from verifier.check_landauer import verify_landauer


# Skip all benchmark tests if pytest-benchmark is not installed
pytestmark = pytest.mark.skipif(
    not BENCHMARK_AVAILABLE,
    reason="pytest-benchmark not installed. Install with: pip install pytest-benchmark"
)


class TestVerifierPerformance:
    """Performance benchmarks for individual verifier components."""

    def test_landauer_performance_small(self, tmp_path: Path, benchmark):
        """Benchmark Landauer verification with small dataset."""
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

        def verify():
            return verify_landauer(run_dir, epsilon=0.1)

        result = benchmark(verify)
        assert result[1]["status"] is not None

    def test_landauer_performance_medium(self, tmp_path: Path, benchmark):
        """Benchmark Landauer verification with medium dataset."""
        run_dir = tmp_path / "landauer"
        landauer_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "0",
                "1",
                "2",
                "--temps",
                "0.8",
                "1.0",
                "1.2",
                "--trials-per-condition",
                "2",
                "--steps",
                "25",
            ]
        )

        def verify():
            return verify_landauer(run_dir, epsilon=0.1)

        result = benchmark(verify)
        assert result[1]["trial_count"] >= 6

    def test_einstein_performance(self, tmp_path: Path, benchmark):
        """Benchmark Einstein verification performance."""
        run_dir = tmp_path / "einstein"
        einstein_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "0",
                "1",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "2",
                "--steps",
                "30",
            ]
        )

        def verify():
            return verify_einstein(run_dir, delta=0.1)

        result = benchmark(verify)
        assert result[1]["status"] is not None

    def test_entropy_performance(self, tmp_path: Path, benchmark):
        """Benchmark Entropy verification performance."""
        run_dir = tmp_path / "entropy"
        entropy_main(
            [
                "--output-dir",
                str(run_dir),
                "--seeds",
                "0",
                "1",
                "--temps",
                "1.0",
                "--trials-per-condition",
                "2",
                "--steps",
                "40",
            ]
        )

        def verify():
            return verify_entropy(run_dir)

        result = benchmark(verify)
        assert result[1]["status"] is not None

    def test_cwd_performance(self, tmp_path: Path, benchmark):
        """Benchmark CWD verification performance."""
        common_args = [
            "--seeds",
            "0",
            "1",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "2",
            "--modules",
            "4",
            "--steps-per-module",
            "5",
        ]

        sighted_dir = tmp_path / "sighted"
        blind_dir = tmp_path / "blind"
        destroyed_dir = tmp_path / "destroyed"

        cwd_main(["--output-dir", str(sighted_dir), "--protocol", "sighted", *common_args])
        cwd_main(["--output-dir", str(blind_dir), "--protocol", "blind", *common_args])
        cwd_main(["--output-dir", str(destroyed_dir), "--protocol", "destroyed", *common_args])

        def verify():
            return verify_cwd(
                sighted_dir=sighted_dir,
                blind_dir=blind_dir,
                destroyed_dir=destroyed_dir,
                epsilon=0.2,
                eta=0.2,
            )

        result = benchmark(verify)
        assert result[1]["status"] is not None


class TestUnifiedVerifierPerformance:
    """Performance benchmarks for unified proofpack verification."""

    def test_complete_proofpack_performance(self, tmp_path: Path, benchmark):
        """Benchmark complete proofpack verification."""
        proofpack_dir = tmp_path / "proofpack"
        proofpack_dir.mkdir()
        self._build_minimal_proofpack(proofpack_dir)

        def verify():
            return verify_proofpack(proofpack_dir, delta_aic=100.0)

        result = benchmark(verify)
        assert "status" in result

    def test_proofpack_with_multiple_runs(self, tmp_path: Path, benchmark):
        """Benchmark proofpack with multiple runs per phase."""
        proofpack_dir = tmp_path / "proofpack"
        proofpack_dir.mkdir()

        # Build multiple Landauer runs
        for seed in range(3):
            landauer_dir = proofpack_dir / f"landauer_{seed}"
            landauer_main(
                [
                    "--output-dir",
                    str(landauer_dir),
                    "--seeds",
                    str(seed),
                    "--temps",
                    "1.0",
                    "--trials-per-condition",
                    "1",
                    "--steps",
                    "12",
                ]
            )

        # Build other phases minimally
        einstein_dir = proofpack_dir / "einstein"
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
                "15",
            ]
        )

        entropy_dir = proofpack_dir / "entropy"
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
                "20",
            ]
        )

        # CWD
        cwd_root = proofpack_dir / "cwd"
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
                    "2",
                    "--steps-per-module",
                    "3",
                ]
            )

        # Cross-domain
        cross_root = proofpack_dir / "cross_domain"
        for protocol in ("sighted", "blind", "destroyed"):
            cross_domain_main(
                [
                    "--output-dir",
                    str(cross_root / protocol),
                    "--protocol",
                    protocol,
                    "--seeds",
                    "0",
                    "--trials-per-condition",
                    "1",
                    "--modules",
                    "3",
                ]
            )

        def verify():
            return verify_proofpack(proofpack_dir, delta_aic=100.0)

        result = benchmark(verify)
        assert "status" in result

    @staticmethod
    def _build_minimal_proofpack(base_dir: Path) -> None:
        """Build minimal proofpack for performance testing."""
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
                "10",
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
                "15",
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
                "20",
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
                    "2",
                    "--steps-per-module",
                    "3",
                ]
            )

        # Cross-domain
        cross_root = base_dir / "cross_domain"
        for protocol in ("sighted", "blind", "destroyed"):
            cross_domain_main(
                [
                    "--output-dir",
                    str(cross_root / protocol),
                    "--protocol",
                    protocol,
                    "--seeds",
                    "0",
                    "--trials-per-condition",
                    "1",
                    "--modules",
                    "3",
                ]
            )


class TestVerifierScaling:
    """Test how verifier performance scales with data size."""

    def test_landauer_scaling_by_steps(self, tmp_path: Path):
        """Test how verification time scales with number of steps."""
        results = []
        
        for steps in [10, 20, 40]:
            run_dir = tmp_path / f"landauer_{steps}"
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
                    str(steps),
                ]
            )
            
            start = time.time()
            _, result = verify_landauer(run_dir, epsilon=0.1)
            elapsed = time.time() - start
            
            results.append((steps, elapsed, result["status"]))
        
        # Verify all passed and times are reasonable
        assert all(status is not None for _, _, status in results)
        # Verify it scales reasonably (not exponential)
        assert results[-1][1] < results[0][1] * 10  # 4x steps shouldn't take >10x time

    def test_landauer_scaling_by_trials(self, tmp_path: Path):
        """Test how verification time scales with number of trials."""
        results = []
        
        for num_seeds in [1, 2, 4]:
            run_dir = tmp_path / f"landauer_seeds_{num_seeds}"
            seeds = [str(i) for i in range(num_seeds)]
            landauer_main(
                [
                    "--output-dir",
                    str(run_dir),
                    "--seeds",
                    *seeds,
                    "--temps",
                    "1.0",
                    "--trials-per-condition",
                    "1",
                    "--steps",
                    "15",
                ]
            )
            
            start = time.time()
            _, result = verify_landauer(run_dir, epsilon=0.1)
            elapsed = time.time() - start
            
            results.append((num_seeds, elapsed, result["trial_count"]))
        
        # Verify scaling is roughly linear
        assert all(count >= seeds for seeds, _, count in results)
        # 4x trials shouldn't take more than 6x time (allowing for overhead)
        if results[-1][1] > 0.01:  # Only check if not too fast to measure
            assert results[-1][1] < results[0][1] * 6
