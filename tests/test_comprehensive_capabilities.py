#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Test suite for comprehensive capability demonstrations.

Tests that all capability categories produce isomorphic results
between Standard Python and Thiele VM.
"""

import pytest
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))


class TestStringEdgeCases:
    """Test string manipulation edge cases."""
    
    def test_string_edge_cases_isomorphism(self):
        """Verify string operations produce identical results."""
        from demos.comprehensive_capabilities.string_edge_cases import compare_and_report
        result = compare_and_report()
        
        assert result['all_match'], f"String edge cases failed: {[c['name'] for c in result['comparisons'] if not c['match']]}"
    
    def test_empty_string_handling(self):
        """Test empty string edge cases."""
        from demos.comprehensive_capabilities.string_edge_cases import reverse_string, palindrome_check
        
        # Empty string reverse
        result, ops = reverse_string("")
        assert result == ""
        assert ops == 0
        
        # Empty string palindrome
        is_palindrome, ops = palindrome_check("")
        assert is_palindrome is True
    
    def test_unicode_handling(self):
        """Test Unicode string handling."""
        from demos.comprehensive_capabilities.string_edge_cases import reverse_string
        
        # Unicode reverse
        result, ops = reverse_string("héllo")
        assert result == "olléh"
        assert ops == 5


class TestRecursionPatterns:
    """Test recursion pattern implementations."""
    
    def test_recursion_patterns_isomorphism(self):
        """Verify recursion patterns produce identical results."""
        from demos.comprehensive_capabilities.recursion_patterns import compare_and_report
        result = compare_and_report()
        
        assert result['all_match'], f"Recursion patterns failed: {[c['name'] for c in result['comparisons'] if not c['match']]}"
    
    def test_factorial(self):
        """Test factorial computation."""
        from demos.comprehensive_capabilities.recursion_patterns import factorial_recursive
        
        assert factorial_recursive(0)[0] == 1
        assert factorial_recursive(1)[0] == 1
        assert factorial_recursive(5)[0] == 120
        assert factorial_recursive(10)[0] == 3628800
    
    def test_fibonacci_memoized(self):
        """Test memoized Fibonacci."""
        from demos.comprehensive_capabilities.recursion_patterns import fibonacci_memoized
        
        assert fibonacci_memoized(0)[0] == 0
        assert fibonacci_memoized(1)[0] == 1
        assert fibonacci_memoized(10)[0] == 55
        assert fibonacci_memoized(50)[0] == 12586269025
    
    def test_mutual_recursion(self):
        """Test mutual recursion even/odd."""
        from demos.comprehensive_capabilities.recursion_patterns import mutual_recursion_even_odd
        
        assert mutual_recursion_even_odd(0)[0] is True
        assert mutual_recursion_even_odd(1)[0] is False
        assert mutual_recursion_even_odd(100)[0] is True
        assert mutual_recursion_even_odd(99)[0] is False
    
    def test_gcd(self):
        """Test GCD computation."""
        from demos.comprehensive_capabilities.recursion_patterns import gcd_recursive
        
        assert gcd_recursive(48, 18)[0] == 6
        assert gcd_recursive(100, 1)[0] == 1
        assert gcd_recursive(17, 23)[0] == 1


class TestGraphAlgorithms:
    """Test graph algorithm implementations."""
    
    def test_graph_algorithms_isomorphism(self):
        """Verify graph algorithms produce identical results."""
        from demos.comprehensive_capabilities.graph_algorithms import compare_and_report
        result = compare_and_report()
        
        assert result['all_match'], f"Graph algorithms failed: {[c['name'] for c in result['comparisons'] if not c['match']]}"
    
    def test_bfs(self):
        """Test BFS traversal."""
        from demos.comprehensive_capabilities.graph_algorithms import bfs
        
        graph = {0: [1, 2], 1: [3], 2: [3], 3: []}
        visited, ops = bfs(graph, 0)
        
        assert visited[0] == 0
        assert set(visited) == {0, 1, 2, 3}
    
    def test_dfs(self):
        """Test DFS traversal."""
        from demos.comprehensive_capabilities.graph_algorithms import dfs
        
        graph = {0: [1, 2], 1: [3], 2: [], 3: []}
        visited, ops = dfs(graph, 0)
        
        assert visited[0] == 0
        assert set(visited) == {0, 1, 2, 3}
    
    def test_dijkstra(self):
        """Test Dijkstra shortest path."""
        from demos.comprehensive_capabilities.graph_algorithms import dijkstra
        
        graph = {
            0: [(1, 4), (2, 1)],
            1: [(3, 1)],
            2: [(1, 2), (3, 5)],
            3: []
        }
        distances, ops = dijkstra(graph, 0)
        
        assert distances[0] == 0
        assert distances[2] == 1  # Direct path
        assert distances[1] == 3  # Through 2
        assert distances[3] == 4  # Through 2, then 1
    
    def test_cycle_detection(self):
        """Test cycle detection."""
        from demos.comprehensive_capabilities.graph_algorithms import has_cycle
        
        # Graph with cycle
        cycle_graph = {0: [1], 1: [2], 2: [0]}
        has, ops = has_cycle(cycle_graph, [0, 1, 2])
        assert has is True
        
        # DAG (no cycle)
        dag = {0: [1, 2], 1: [3], 2: [3], 3: []}
        has, ops = has_cycle(dag, [0, 1, 2, 3])
        assert has is False


class TestMathematicalEdgeCases:
    """Test mathematical edge case implementations."""
    
    def test_math_edge_cases_isomorphism(self):
        """Verify math operations produce identical results."""
        from demos.comprehensive_capabilities.mathematical_edge_cases import compare_and_report
        result = compare_and_report()
        
        assert result['all_match'], f"Math edge cases failed: {[c['name'] for c in result['comparisons'] if not c['match']]}"
    
    def test_power_mod(self):
        """Test modular exponentiation."""
        from demos.comprehensive_capabilities.mathematical_edge_cases import power_mod
        
        assert power_mod(2, 10, 1000)[0] == 1024 % 1000
        assert power_mod(3, 1000, 7)[0] == pow(3, 1000, 7)
    
    def test_prime_factors(self):
        """Test prime factorization."""
        from demos.comprehensive_capabilities.mathematical_edge_cases import prime_factors
        
        assert prime_factors(12)[0] == [2, 2, 3]
        assert prime_factors(1001)[0] == [7, 11, 13]
        assert prime_factors(997)[0] == [997]  # Prime
    
    def test_binomial(self):
        """Test binomial coefficients."""
        from demos.comprehensive_capabilities.mathematical_edge_cases import binomial
        
        assert binomial(10, 5)[0] == 252
        assert binomial(20, 10)[0] == 184756
        assert binomial(5, 0)[0] == 1
        assert binomial(5, 6)[0] == 0  # k > n
    
    def test_integer_sqrt(self):
        """Test integer square root."""
        from demos.comprehensive_capabilities.mathematical_edge_cases import integer_sqrt
        
        assert integer_sqrt(0)[0] == 0
        assert integer_sqrt(1)[0] == 1
        assert integer_sqrt(100)[0] == 10
        assert integer_sqrt(99)[0] == 9


class TestBacktracking:
    """Test backtracking algorithm implementations."""
    
    def test_backtracking_isomorphism(self):
        """Verify backtracking algorithms produce identical results."""
        from demos.comprehensive_capabilities.backtracking import compare_and_report
        result = compare_and_report()
        
        assert result['all_match'], f"Backtracking failed: {[c['name'] for c in result['comparisons'] if not c['match']]}"
    
    def test_n_queens(self):
        """Test N-Queens solver."""
        from demos.comprehensive_capabilities.backtracking import n_queens
        
        # 4-Queens has 2 solutions
        solutions, ops = n_queens(4)
        assert len(solutions) == 2
        
        # 5-Queens has 10 solutions
        solutions, ops = n_queens(5)
        assert len(solutions) == 10
    
    def test_subset_sum(self):
        """Test subset sum."""
        from demos.comprehensive_capabilities.backtracking import subset_sum
        
        # Has solution
        result, ops = subset_sum([3, 1, 4, 2, 5], 9)
        assert result is not None
        assert sum(result) == 9
        
        # No solution
        result, ops = subset_sum([2, 4, 6], 7)
        assert result is None
    
    def test_permutations(self):
        """Test permutation generation."""
        from demos.comprehensive_capabilities.backtracking import generate_permutations
        
        perms, ops = generate_permutations(3)
        assert len(perms) == 6  # 3! = 6
        
        perms, ops = generate_permutations(4)
        assert len(perms) == 24  # 4! = 24
    
    def test_combinations(self):
        """Test combination generation."""
        from demos.comprehensive_capabilities.backtracking import generate_combinations
        
        combs, ops = generate_combinations(5, 2)
        assert len(combs) == 10  # C(5,2) = 10
        
        combs, ops = generate_combinations(6, 3)
        assert len(combs) == 20  # C(6,3) = 20


class TestComprehensiveRunner:
    """Test the comprehensive runner itself."""
    
    def test_comprehensive_runner(self):
        """Test that comprehensive runner executes successfully."""
        from demos.comprehensive_capabilities.run_comprehensive_tests import run_all_capabilities
        
        results = run_all_capabilities()
        
        # Should have results
        assert 'categories' in results
        assert 'aggregate' in results
        assert 'derived_conclusions' in results
        
        # Should have multiple categories
        assert len(results['categories']) >= 1
        
        # Check aggregate
        assert results['aggregate']['total_tests'] > 0
    
    def test_all_categories_pass(self):
        """Test that all capability categories pass isomorphism checks."""
        from demos.comprehensive_capabilities.run_comprehensive_tests import run_all_capabilities
        
        results = run_all_capabilities()
        
        # All categories should pass
        for cat in results['categories']:
            assert cat['all_match'], f"Category {cat['name']} failed isomorphism check"
        
        # Overall pass rate should be 100%
        assert results['aggregate']['pass_rate'] == 1.0, \
            f"Overall pass rate is {results['aggregate']['pass_rate']*100:.1f}%, expected 100%"
    
    def test_mu_cost_tracked(self):
        """Test that μ-cost is tracked for all VM executions."""
        from demos.comprehensive_capabilities.run_comprehensive_tests import run_all_capabilities
        
        results = run_all_capabilities()
        
        # Total μ-cost should be positive
        assert results['aggregate']['total_mu_cost'] > 0, \
            "No μ-cost tracked - Thiele VM separation not demonstrated"
    
    def test_derived_conclusions_supported(self):
        """Test that key conclusions are supported by evidence."""
        from demos.comprehensive_capabilities.run_comprehensive_tests import run_all_capabilities
        
        results = run_all_capabilities()
        
        # Check for key conclusions
        conclusion_types = {c['type'] for c in results['derived_conclusions']}
        
        assert 'STRUCTURAL_ISOMORPHISM' in conclusion_types
        assert 'MU_COST_TRACKING' in conclusion_types
        
        # Structural isomorphism should be supported
        isomorphism_conc = next(c for c in results['derived_conclusions'] 
                               if c['type'] == 'STRUCTURAL_ISOMORPHISM')
        assert isomorphism_conc['supported'], "Structural isomorphism not supported by evidence"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
