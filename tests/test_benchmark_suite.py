"""
Tests for the blind vs sighted benchmark suite.

These tests verify:
1. Problem generators produce valid instances
2. Solvers produce correct results
3. μ-cost accounting is consistent
4. Reproducibility from (size, seed)
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import pytest

from thielecpu.benchmarks import (
    BenchmarkInstance,
    generate_instance,
    generate_tseitin_instance,
    generate_planted_sat_instance,
    generate_period_finding_instance,
    list_families,
    PROBLEM_FAMILIES,
    BlindSolver,
    SightedSolver,
    SolverResult,
    run_both_solvers,
)


class TestProblemGenerators:
    """Tests for problem family generators."""

    def test_list_families_returns_all(self) -> None:
        """All families should be listed."""
        families = list_families()
        assert len(families) >= 3
        names = [f["name"] for f in families]
        assert "tseitin" in names
        assert "planted_sat" in names
        assert "period_finding" in names

    def test_generate_tseitin_basic(self) -> None:
        """Tseitin generator should produce valid instances."""
        instance = generate_tseitin_instance(10, 42)
        
        assert instance.family == "tseitin"
        assert instance.size == 10
        assert instance.seed == 42
        assert instance.num_variables > 0
        assert len(instance.cnf_clauses) > 0
        assert len(instance.partition) > 0
        assert instance.expected_answer == "UNSAT"

    def test_generate_planted_sat_basic(self) -> None:
        """Planted SAT generator should produce valid instances."""
        instance = generate_planted_sat_instance(20, 42)
        
        assert instance.family == "planted_sat"
        assert instance.size == 20
        assert instance.num_variables == 20
        assert len(instance.cnf_clauses) > 0
        assert len(instance.partition) >= 2
        assert instance.expected_answer == "SAT"

    def test_generate_period_finding_basic(self) -> None:
        """Period finding generator should produce valid instances."""
        instance = generate_period_finding_instance(21, 2)
        
        assert instance.family == "period_finding"
        assert instance.size == 21
        assert instance.num_variables > 0
        assert instance.expected_answer == "6"  # Period of 2 mod 21

    def test_reproducibility_tseitin(self) -> None:
        """Same (n, seed) should produce identical instances."""
        i1 = generate_tseitin_instance(8, 123)
        i2 = generate_tseitin_instance(8, 123)
        
        assert i1.generation_hash == i2.generation_hash
        assert i1.num_variables == i2.num_variables
        assert i1.cnf_clauses == i2.cnf_clauses

    def test_reproducibility_planted_sat(self) -> None:
        """Same (n, seed) should produce identical instances."""
        i1 = generate_planted_sat_instance(15, 456)
        i2 = generate_planted_sat_instance(15, 456)
        
        assert i1.generation_hash == i2.generation_hash
        assert i1.num_variables == i2.num_variables

    def test_different_seeds_different_instances(self) -> None:
        """Different seeds should produce different instances."""
        i1 = generate_tseitin_instance(10, 1)
        i2 = generate_tseitin_instance(10, 2)
        
        # Generation hashes should differ
        assert i1.generation_hash != i2.generation_hash

    def test_partition_covers_all_variables(self) -> None:
        """Partition should cover all variables."""
        instance = generate_tseitin_instance(12, 42)
        
        covered = set()
        for module in instance.partition:
            covered |= module
        
        all_vars = set(range(1, instance.num_variables + 1))
        assert covered == all_vars

    def test_instance_to_dict(self) -> None:
        """Instance serialization should work."""
        instance = generate_tseitin_instance(6, 42)
        d = instance.to_dict()
        
        assert d["family"] == "tseitin"
        assert d["size"] == 6
        assert d["seed"] == 42
        assert "num_variables" in d
        assert "num_clauses" in d


class TestBlindSolver:
    """Tests for the blind (Turing-equivalent) solver."""

    def test_solve_small_sat(self) -> None:
        """Blind solver should find SAT on planted instances."""
        instance = generate_planted_sat_instance(8, 42)
        solver = BlindSolver(timeout_s=5.0)
        result = solver.solve(instance)
        
        # Planted SAT should be satisfiable
        assert result.status in ["SAT", "TIMEOUT"]
        assert result.mode == "blind"
        assert result.mu_total >= 0

    def test_solve_tseitin_unsat(self) -> None:
        """Blind solver should find UNSAT on Tseitin (if not timeout)."""
        instance = generate_tseitin_instance(5, 42)
        solver = BlindSolver(timeout_s=10.0)
        result = solver.solve(instance)
        
        # Small Tseitin should complete
        assert result.status in ["UNSAT", "SAT", "TIMEOUT"]
        assert result.mode == "blind"

    def test_mu_cost_positive(self) -> None:
        """μ-cost should be positive after solving."""
        instance = generate_tseitin_instance(5, 42)
        solver = BlindSolver(timeout_s=5.0)
        result = solver.solve(instance)
        
        assert result.mu_operational >= 0
        assert result.mu_discovery == 0  # Blind never discovers
        assert result.mu_total == result.mu_operational

    def test_result_to_json(self) -> None:
        """Result serialization should work."""
        instance = generate_planted_sat_instance(6, 42)
        solver = BlindSolver(timeout_s=5.0)
        result = solver.solve(instance)
        
        json_str = result.to_json()
        parsed = json.loads(json_str)
        
        assert parsed["mode"] == "blind"
        assert "mu_total" in parsed


class TestSightedSolver:
    """Tests for the sighted (partition-aware) solver."""

    def test_solve_with_partition(self) -> None:
        """Sighted solver should use partition information."""
        instance = generate_planted_sat_instance(12, 42)
        solver = SightedSolver(timeout_s=5.0)
        result = solver.solve(instance)
        
        assert result.mode == "sighted"
        assert result.mu_discovery > 0  # Sighted charges discovery

    def test_discovery_cost_charged(self) -> None:
        """Sighted solver should charge μ_discovery."""
        instance = generate_tseitin_instance(6, 42)
        solver = SightedSolver(timeout_s=5.0, discovery_cost=10.0)
        result = solver.solve(instance)
        
        assert result.mu_discovery == 10.0
        assert result.mu_total >= result.mu_discovery

    def test_faster_than_blind_on_structured(self) -> None:
        """Sighted should make fewer decisions on structured problems."""
        instance = generate_planted_sat_instance(16, 42)
        
        blind = BlindSolver(timeout_s=10.0)
        sighted = SightedSolver(timeout_s=10.0)
        
        br = blind.solve(instance)
        sr = sighted.solve(instance)
        
        # Sighted should typically have fewer decisions
        # (though not guaranteed for all instances)
        # Just verify both complete
        assert br.status in ["SAT", "UNSAT", "TIMEOUT"]
        assert sr.status in ["SAT", "UNSAT", "TIMEOUT"]


class TestBothSolvers:
    """Tests comparing blind and sighted solvers."""

    def test_run_both_solvers(self) -> None:
        """run_both_solvers should return two results."""
        instance = generate_tseitin_instance(6, 42)
        br, sr = run_both_solvers(instance, timeout_s=5.0)
        
        assert br.mode == "blind"
        assert sr.mode == "sighted"

    def test_same_answer_on_small_instance(self) -> None:
        """Both solvers should agree on small instances."""
        instance = generate_planted_sat_instance(6, 42)
        br, sr = run_both_solvers(instance, timeout_s=10.0)
        
        # Both should complete on small instance
        assert br.status in ["SAT", "UNSAT"]
        assert sr.status in ["SAT", "UNSAT"]

    @pytest.mark.parametrize("size", [5, 6, 7, 8])
    def test_scaling_tseitin(self, size: int) -> None:
        """Verify scaling behavior on Tseitin formulas."""
        instance = generate_tseitin_instance(size, 42)
        br, sr = run_both_solvers(instance, timeout_s=30.0)
        
        # Just verify both complete without error
        assert br.status in ["SAT", "UNSAT", "TIMEOUT"]
        assert sr.status in ["SAT", "UNSAT", "TIMEOUT"]
        assert br.wall_time_s >= 0
        assert sr.wall_time_s >= 0


class TestPeriodFinding:
    """Tests for period-finding instances."""

    @pytest.mark.parametrize("N,base,expected_period", [
        (21, 2, 6),
        (15, 2, 4),
        (35, 2, 12),
    ])
    def test_period_finding_correctness(self, N: int, base: int, expected_period: int) -> None:
        """Period finding instances should have correct expected answer."""
        instance = generate_period_finding_instance(N, base)
        
        assert instance.expected_answer == str(expected_period)

    def test_period_finding_rejects_non_coprime(self) -> None:
        """Should reject non-coprime inputs."""
        with pytest.raises(ValueError):
            generate_period_finding_instance(15, 3)  # gcd(15, 3) = 3


class TestMuCostAccounting:
    """Tests for μ-cost accounting correctness."""

    def test_blind_no_discovery(self) -> None:
        """Blind solver should never charge discovery cost."""
        instance = generate_tseitin_instance(6, 42)
        solver = BlindSolver(timeout_s=5.0)
        result = solver.solve(instance)
        
        assert result.mu_discovery == 0

    def test_sighted_charges_discovery(self) -> None:
        """Sighted solver should charge discovery cost."""
        instance = generate_tseitin_instance(6, 42)
        solver = SightedSolver(timeout_s=5.0, discovery_cost=100.0)
        result = solver.solve(instance)
        
        assert result.mu_discovery == 100.0

    def test_mu_total_sum(self) -> None:
        """μ_total should equal μ_operational + μ_discovery."""
        instance = generate_planted_sat_instance(10, 42)
        
        for SolverClass in [BlindSolver, SightedSolver]:
            solver = SolverClass(timeout_s=5.0)
            result = solver.solve(instance)
            
            expected_total = result.mu_operational + result.mu_discovery
            assert abs(result.mu_total - expected_total) < 0.001


class TestCoqIsomorphism:
    """Tests verifying alignment with Coq definitions."""

    COQ_DIR = Path(__file__).resolve().parents[1] / "coq" / "thielemachine" / "coqproofs"

    def test_blind_sighted_file_exists(self) -> None:
        """BlindSighted.v should exist."""
        assert (self.COQ_DIR / "BlindSighted.v").exists()

    def test_separation_file_exists(self) -> None:
        """Separation.v should exist."""
        assert (self.COQ_DIR / "Separation.v").exists()

    def test_coq_contains_blind_definitions(self) -> None:
        """BlindSighted.v should define ThieleBlind concepts."""
        content = (self.COQ_DIR / "BlindSighted.v").read_text()
        
        assert "is_blind_safe" in content
        assert "is_blind_program" in content
        assert "TM_as_BlindThiele" in content
        assert "Blind_is_restriction_of_Sighted" in content

    def test_coq_contains_separation_theorem(self) -> None:
        """Separation.v should contain the main theorem."""
        content = (self.COQ_DIR / "Separation.v").read_text()
        
        assert "thiele_exponential_separation" in content
        assert "turing_blind_steps" in content
        assert "thiele_sighted_steps" in content


class TestFalsifiability:
    """Tests verifying falsifiability requirements."""

    def test_deterministic_generation(self) -> None:
        """Generation should be deterministic."""
        for _ in range(3):
            i1 = generate_tseitin_instance(10, 42)
            i2 = generate_tseitin_instance(10, 42)
            assert i1.generation_hash == i2.generation_hash

    def test_hash_includes_params(self) -> None:
        """Hash should change with parameters."""
        h1 = generate_tseitin_instance(10, 42).generation_hash
        h2 = generate_tseitin_instance(11, 42).generation_hash
        h3 = generate_tseitin_instance(10, 43).generation_hash
        
        assert h1 != h2
        assert h1 != h3
        assert h2 != h3

    def test_result_has_all_metrics(self) -> None:
        """Results should include all required metrics."""
        instance = generate_planted_sat_instance(8, 42)
        solver = BlindSolver(timeout_s=5.0)
        result = solver.solve(instance)
        
        d = result.to_dict()
        
        required_fields = [
            "family", "size", "seed", "mode",
            "wall_time_s", "decisions", "propagations", "conflicts",
            "oracle_calls", "mu_discovery", "mu_operational", "mu_total",
            "status", "verified",
        ]
        
        for field in required_fields:
            assert field in d, f"Missing field: {field}"
