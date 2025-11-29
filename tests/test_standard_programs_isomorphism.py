# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Test Suite: Standard Programs Isomorphism Validation

Tests that standard programs produce identical results when run in:
1. Standard Python interpreter
2. Thiele VM

This validates the structural isomorphism between the two execution environments.
"""

import pytest
import sys
from pathlib import Path

# Add repo root to path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))


class TestNumberGuessing:
    """Test number guessing algorithm isomorphism."""
    
    def test_binary_search_isomorphism(self):
        """Binary search produces same results in both environments."""
        from demos.standard_programs.number_guessing import (
            run_standard_python, run_thiele_vm
        )
        
        test_cases = [(42, 1, 100), (1, 1, 50), (50, 1, 50)]
        
        for target, low, high in test_cases:
            std = run_standard_python(target, low, high)
            vm = run_thiele_vm(target, low, high)
            
            # Same found value
            assert std['binary']['found'] == vm['binary']['found']
            # Same number of guesses
            assert std['binary']['guesses'] == vm['binary']['guesses']
            # Both correct
            assert std['binary']['correct'] and vm['binary']['correct']
    
    def test_linear_search_isomorphism(self):
        """Linear search produces same results in both environments."""
        from demos.standard_programs.number_guessing import (
            run_standard_python, run_thiele_vm
        )
        
        target, low, high = 10, 1, 20
        
        std = run_standard_python(target, low, high)
        vm = run_thiele_vm(target, low, high)
        
        assert std['linear']['found'] == vm['linear']['found']
        assert std['linear']['guesses'] == vm['linear']['guesses']
    
    def test_binary_fewer_guesses_than_linear(self):
        """Binary search uses fewer guesses (separation)."""
        from demos.standard_programs.number_guessing import run_thiele_vm
        
        result = run_thiele_vm(500, 1, 1000)
        
        # Binary should use O(log n) guesses
        assert result['binary']['guesses'] <= 10  # log2(1000) ≈ 10
        # Linear uses O(n) guesses
        assert result['linear']['guesses'] == 500
        
        # Thiele tracks μ-cost
        assert result['binary']['mu_cost'] > 0
        assert result['linear']['mu_cost'] > result['binary']['mu_cost']


class TestSortingAlgorithms:
    """Test sorting algorithm isomorphism."""
    
    def test_bubble_sort_isomorphism(self):
        """Bubble sort produces same results in both environments."""
        from demos.standard_programs.sorting_algorithms import (
            run_standard_python, run_thiele_vm
        )
        
        arr = [5, 2, 8, 1, 9]
        std = run_standard_python(arr)
        vm = run_thiele_vm(arr)
        
        assert std['bubble']['sorted'] == vm['bubble']['sorted']
        assert std['bubble']['comparisons'] == vm['bubble']['comparisons']
        assert std['bubble']['correct'] and vm['bubble']['correct']
    
    def test_quick_sort_isomorphism(self):
        """Quick sort produces same results in both environments."""
        from demos.standard_programs.sorting_algorithms import (
            run_standard_python, run_thiele_vm
        )
        
        arr = [3, 1, 4, 1, 5, 9, 2, 6]
        std = run_standard_python(arr)
        vm = run_thiele_vm(arr)
        
        assert std['quick']['sorted'] == vm['quick']['sorted']
        assert std['quick']['comparisons'] == vm['quick']['comparisons']
    
    def test_merge_sort_isomorphism(self):
        """Merge sort produces same results in both environments."""
        from demos.standard_programs.sorting_algorithms import (
            run_standard_python, run_thiele_vm
        )
        
        arr = [9, 7, 5, 3, 1, 2, 4, 6, 8]
        std = run_standard_python(arr)
        vm = run_thiele_vm(arr)
        
        assert std['merge']['sorted'] == vm['merge']['sorted']
        assert std['merge']['comparisons'] == vm['merge']['comparisons']
    
    def test_efficient_sorts_fewer_comparisons(self):
        """Quick/Merge use fewer comparisons than Bubble (separation)."""
        from demos.standard_programs.sorting_algorithms import run_standard_python
        
        import random
        random.seed(42)
        arr = [random.randint(1, 100) for _ in range(30)]
        
        result = run_standard_python(arr)
        
        # Bubble: O(n²) ≈ 30*29/2 = 435
        # Quick/Merge: O(n log n) ≈ 30 * 5 = 150
        assert result['bubble']['comparisons'] > result['quick']['comparisons']
        assert result['bubble']['comparisons'] > result['merge']['comparisons']
    
    def test_thiele_tracks_mu_cost(self):
        """Thiele VM tracks μ-cost for each algorithm."""
        from demos.standard_programs.sorting_algorithms import run_thiele_vm
        
        arr = [5, 3, 1, 4, 2]
        result = run_thiele_vm(arr)
        
        # All should have μ-cost > 0
        assert result['bubble']['mu_cost'] > 0
        assert result['quick']['mu_cost'] > 0
        assert result['merge']['mu_cost'] > 0


class TestSudokuSolver:
    """Test Sudoku solver isomorphism."""
    
    def test_sudoku_classical_solves(self):
        """Classical solver finds correct solution."""
        from demos.standard_programs.sudoku_solver import solve_sudoku_classical
        
        puzzle = [
            [5, 3, 0, 0, 7, 0, 0, 0, 0],
            [6, 0, 0, 1, 9, 5, 0, 0, 0],
            [0, 9, 8, 0, 0, 0, 0, 6, 0],
            [8, 0, 0, 0, 6, 0, 0, 0, 3],
            [4, 0, 0, 8, 0, 3, 0, 0, 1],
            [7, 0, 0, 0, 2, 0, 0, 0, 6],
            [0, 6, 0, 0, 0, 0, 2, 8, 0],
            [0, 0, 0, 4, 1, 9, 0, 0, 5],
            [0, 0, 0, 0, 8, 0, 0, 7, 9],
        ]
        
        solved, solution, backtracks = solve_sudoku_classical(puzzle)
        
        assert solved is True
        # Verify solution is valid
        for row in solution:
            assert sorted(row) == list(range(1, 10))
    
    def test_sudoku_vm_matches_classical(self):
        """Thiele VM produces same solution as classical."""
        from demos.standard_programs.sudoku_solver import (
            solve_sudoku_classical, solve_with_thiele_blind
        )
        
        puzzle = [
            [5, 3, 0, 0, 7, 0, 0, 0, 0],
            [6, 0, 0, 1, 9, 5, 0, 0, 0],
            [0, 9, 8, 0, 0, 0, 0, 6, 0],
            [8, 0, 0, 0, 6, 0, 0, 0, 3],
            [4, 0, 0, 8, 0, 3, 0, 0, 1],
            [7, 0, 0, 0, 2, 0, 0, 0, 6],
            [0, 6, 0, 0, 0, 0, 2, 8, 0],
            [0, 0, 0, 4, 1, 9, 0, 0, 5],
            [0, 0, 0, 0, 8, 0, 0, 7, 9],
        ]
        
        classical = solve_sudoku_classical(puzzle)
        vm_result = solve_with_thiele_blind(puzzle)
        
        assert classical[0] == vm_result['solved']  # Both solved
        assert classical[1] == vm_result['solution']  # Same solution


class TestGraphColoring:
    """Test graph coloring isomorphism."""
    
    def test_petersen_graph_colorable(self):
        """Petersen graph is 3-colorable."""
        from demos.standard_programs.graph_coloring import (
            create_petersen_graph, color_graph_classical
        )
        
        graph = create_petersen_graph()
        success, coloring, backtracks = color_graph_classical(graph, 3)
        
        assert success is True
        # Verify no adjacent nodes have same color
        for node, neighbors in graph.items():
            for neighbor in neighbors:
                assert coloring[node] != coloring[neighbor]
    
    def test_bipartite_2_colorable(self):
        """Complete bipartite graph is 2-colorable."""
        from demos.standard_programs.graph_coloring import (
            create_bipartite_graph, color_graph_classical
        )
        
        graph = create_bipartite_graph(4)
        success, coloring, backtracks = color_graph_classical(graph, 2)
        
        assert success is True
    
    def test_graph_coloring_vm_matches_classical(self):
        """Thiele VM produces valid coloring like classical."""
        from demos.standard_programs.graph_coloring import (
            create_petersen_graph, color_graph_classical, color_with_thiele_blind
        )
        
        graph = create_petersen_graph()
        classical = color_graph_classical(graph, 3)
        vm_result = color_with_thiele_blind(graph, 3)
        
        # Both should succeed
        assert classical[0] == vm_result['success']
        
        # VM coloring should also be valid
        if vm_result['success']:
            for node, neighbors in graph.items():
                for neighbor in neighbors:
                    assert vm_result['coloring'][node] != vm_result['coloring'][neighbor]


class TestPasswordCracker:
    """Test password cracker isomorphism."""
    
    def test_classical_finds_password(self):
        """Classical brute force finds the password."""
        import hashlib
        from demos.standard_programs.password_cracker import crack_password_classical
        
        password = "ab"
        target = hashlib.sha256(password.encode()).hexdigest()
        
        found, attempts = crack_password_classical(target, "abcdef", 2)
        
        assert found == password
    
    def test_structured_fewer_attempts(self):
        """Structured search with known prefix uses fewer attempts."""
        import hashlib
        from demos.standard_programs.password_cracker import (
            crack_password_classical, crack_password_structured
        )
        
        password = "cat"
        target = hashlib.sha256(password.encode()).hexdigest()
        
        # Classical - no hint
        _, attempts_classical = crack_password_classical(target, "abcdefghijklmnopqrstuvwxyz", 3)
        
        # Structured - know first letter
        _, attempts_structured = crack_password_structured(
            target, "abcdefghijklmnopqrstuvwxyz", 3, known_prefix="c"
        )
        
        # Structured should use fewer attempts
        assert attempts_structured < attempts_classical


class TestIsomorphismProperties:
    """Test overall isomorphism properties."""
    
    def test_all_programs_import(self):
        """All standard programs can be imported."""
        from demos.standard_programs import number_guessing
        from demos.standard_programs import sorting_algorithms
        from demos.standard_programs import sudoku_solver
        from demos.standard_programs import graph_coloring
        from demos.standard_programs import password_cracker
        
        assert number_guessing is not None
        assert sorting_algorithms is not None
        assert sudoku_solver is not None
        assert graph_coloring is not None
        assert password_cracker is not None
    
    def test_vm_always_tracks_mu(self):
        """Thiele VM always tracks μ-cost, standard Python doesn't."""
        from demos.standard_programs.number_guessing import run_standard_python, run_thiele_vm
        
        std = run_standard_python(50, 1, 100)
        vm = run_thiele_vm(50, 1, 100)
        
        # Standard Python doesn't have μ-cost
        assert 'mu_cost' not in std['binary']
        
        # Thiele VM does
        assert 'mu_cost' in vm['binary']
        assert vm['binary']['mu_cost'] > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
