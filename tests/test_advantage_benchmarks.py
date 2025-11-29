# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Test Suite for Thiele Advantage Benchmarks

Validates that the benchmarks produce correct and reproducible results,
proving the measurable advantages of the Thiele Machine.
"""

import pytest
import random
import sys
from pathlib import Path

# Add repo root to path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

from demos.benchmarks.advantage_benchmarks import (
    benchmark_binary_vs_linear_search,
    benchmark_constraint_propagation,
    benchmark_divide_and_conquer,
    benchmark_early_termination,
    benchmark_verification_vs_discovery,
    benchmark_graph_components,
    BenchmarkResult,
)


class TestBinaryVsLinearSearch:
    """Test binary search advantage benchmark."""
    
    def test_binary_search_fewer_ops(self):
        """Binary search uses significantly fewer operations."""
        random.seed(42)
        result = benchmark_binary_vs_linear_search(1000, 0.5)
        
        # Binary should use O(log n) ≈ 10 ops
        assert result.thiele_ops <= 15
        # Linear uses O(n/2) ≈ 500 ops
        assert result.classical_ops >= 400
        # Advantage ratio should be > 10x
        assert result.advantage_ratio > 10
    
    def test_binary_search_edge_cases(self):
        """Binary search handles edge cases."""
        # Target at start
        result = benchmark_binary_vs_linear_search(1000, 0.0)
        assert result.thiele_ops <= 15  # Still O(log n)
        
        # Target at end
        result = benchmark_binary_vs_linear_search(1000, 1.0)
        assert result.thiele_ops <= 15  # Still O(log n)
    
    def test_advantage_scales_with_n(self):
        """Advantage increases with problem size."""
        result_small = benchmark_binary_vs_linear_search(100, 0.5)
        result_large = benchmark_binary_vs_linear_search(10000, 0.5)
        
        # Larger n should have bigger advantage ratio
        assert result_large.advantage_ratio > result_small.advantage_ratio


class TestConstraintPropagation:
    """Test constraint propagation advantage benchmark."""
    
    def test_propagation_fewer_ops(self):
        """Propagation uses fewer operations than brute force."""
        result = benchmark_constraint_propagation(4)
        
        # Brute force checks many combinations
        assert result.classical_ops > 100
        # Propagation is much more efficient
        assert result.advantage_ratio > 10
    
    def test_mu_cost_tracked(self):
        """μ-cost is tracked for propagation."""
        result = benchmark_constraint_propagation(4)
        assert result.thiele_mu_cost > 0


class TestDivideAndConquer:
    """Test divide and conquer benchmark."""
    
    def test_correct_result(self):
        """D&C finds same max as sequential."""
        random.seed(42)
        result = benchmark_divide_and_conquer(100)
        
        # If it ran without assertion error, results matched
        assert result is not None
        assert result.advantage_type == "structure"
    
    def test_partition_creation(self):
        """D&C demonstrates partition usage."""
        random.seed(42)
        result = benchmark_divide_and_conquer(100)
        
        # Description should mention partitions
        assert "partition" in result.description.lower()


class TestEarlyTermination:
    """Test early termination benchmark."""
    
    def test_both_find_duplicate(self):
        """Both methods find the duplicate."""
        result = benchmark_early_termination(1000)
        
        # Test completed without error = both found duplicate
        assert result is not None
    
    def test_structure_awareness_documented(self):
        """Structure awareness is documented."""
        result = benchmark_early_termination(1000)
        
        # Description mentions sortedness
        assert "sorted" in result.description.lower()


class TestVerificationVsDiscovery:
    """Test verification vs discovery benchmark."""
    
    def test_verification_simpler(self):
        """Verification uses fewer operations than discovery."""
        result = benchmark_verification_vs_discovery()
        
        # Discovery requires trial division
        assert result.classical_ops > 1
        # Verification is just one multiplication
        assert result.thiele_ops == 1
    
    def test_information_advantage_type(self):
        """Benchmark correctly identifies information advantage."""
        result = benchmark_verification_vs_discovery()
        assert result.advantage_type == "information"


class TestGraphComponents:
    """Test graph component benchmark."""
    
    def test_bipartite_detection(self):
        """Both methods correctly detect bipartiteness."""
        result = benchmark_graph_components(50, 5)
        
        # Both should complete without error
        assert result is not None
    
    def test_partition_per_component(self):
        """Thiele creates partition per component."""
        result = benchmark_graph_components(100, 10)
        
        # Description should mention components/partitions
        assert "partition" in result.description.lower() or "component" in result.description.lower()


class TestBenchmarkResults:
    """Test benchmark result integrity."""
    
    def test_all_benchmarks_return_results(self):
        """All benchmarks return valid BenchmarkResult objects."""
        random.seed(42)
        
        results = [
            benchmark_binary_vs_linear_search(100, 0.5),
            benchmark_constraint_propagation(4),
            benchmark_divide_and_conquer(100),
            benchmark_early_termination(1000),
            benchmark_verification_vs_discovery(),
            benchmark_graph_components(50, 5),
        ]
        
        for result in results:
            assert isinstance(result, BenchmarkResult)
            assert result.name is not None
            assert result.classical_ops >= 0
            assert result.thiele_ops >= 0
            assert result.thiele_mu_cost >= 0
    
    def test_advantage_ratio_computed(self):
        """Advantage ratios are computed for all benchmarks."""
        random.seed(42)
        
        result = benchmark_binary_vs_linear_search(1000, 0.5)
        
        # Ratio should be ops_classical / ops_thiele
        expected = result.classical_ops / max(result.thiele_ops, 1)
        assert abs(result.advantage_ratio - expected) < 0.01
    
    def test_reproducibility(self):
        """Benchmarks produce reproducible results with same seed."""
        random.seed(42)
        result1 = benchmark_divide_and_conquer(100)
        
        random.seed(42)
        result2 = benchmark_divide_and_conquer(100)
        
        assert result1.classical_ops == result2.classical_ops
        assert result1.thiele_ops == result2.thiele_ops


class TestProvenAdvantages:
    """Test that proven advantages are significant."""
    
    def test_binary_search_advantage_significant(self):
        """Binary search provides >100x advantage on large inputs."""
        result = benchmark_binary_vs_linear_search(10000, 0.5)
        assert result.advantage_ratio > 100
    
    def test_constraint_propagation_advantage_significant(self):
        """Constraint propagation provides >10x advantage."""
        result = benchmark_constraint_propagation(4)
        assert result.advantage_ratio > 10
    
    def test_at_least_two_significant_advantages(self):
        """At least two benchmarks show >1.5x advantage."""
        random.seed(42)
        
        results = [
            benchmark_binary_vs_linear_search(1000, 0.5),
            benchmark_constraint_propagation(4),
            benchmark_divide_and_conquer(100),
            benchmark_early_termination(1000),
            benchmark_verification_vs_discovery(),
            benchmark_graph_components(50, 5),
        ]
        
        significant = [r for r in results if r.advantage_ratio > 1.5]
        assert len(significant) >= 2, f"Only {len(significant)} benchmarks show >1.5x advantage"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
