# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Sudoku Partition Solver - Educational Thiele Machine Program

Demonstrates partition logic for constraint propagation with real μ-spec v2.0 costs:

    μ_total(q, N, M) = 8|canon(q)| + log₂(N/M)

Key concepts:
- Each box (2x2 for 4x4, 3x3 for 9x9) is a module/partition
- Constraints propagate within modules first (local reasoning)
- Cross-module constraints use composite witnesses
- μ-cost tracks real information revealed

This is a NORMAL/EDUCATIONAL program showing basic Thiele concepts.
"""

from typing import List, Dict, Any, Set, Tuple
import hashlib
import math

# Import real μ-spec v2.0 implementation
try:
    from thielecpu.mu import (
        calculate_mu_cost,
        question_cost_bits,
        information_gain_bits,
        canonical_s_expression,
    )
except ImportError:
    # Fallback for standalone execution
    def canonical_s_expression(expr: str) -> str:
        tokens = []
        current = []
        for ch in expr:
            if ch in "()":
                if current:
                    tokens.append("".join(current))
                    current = []
                tokens.append(ch)
            elif ch.isspace():
                if current:
                    tokens.append("".join(current))
                    current = []
            else:
                current.append(ch)
        if current:
            tokens.append("".join(current))
        return " ".join(tokens)
    
    def question_cost_bits(expr: str) -> int:
        canonical = canonical_s_expression(expr)
        return len(canonical.encode("utf-8")) * 8
    
    def information_gain_bits(before: int, after: int) -> float:
        if before <= 0 or after <= 0 or after > before:
            return 0.0
        if after == before:
            return 0.0
        return math.log2(before / after)
    
    def calculate_mu_cost(expr: str, before: int, after: int) -> float:
        return question_cost_bits(expr) + information_gain_bits(before, after)


def _get_box_cells(box_idx: int, size: int, box_size: int) -> List[Tuple[int, int]]:
    """Get all cell coordinates in a box."""
    box_row = (box_idx // box_size) * box_size
    box_col = (box_idx % box_size) * box_size
    cells = []
    for r in range(box_size):
        for c in range(box_size):
            cells.append((box_row + r, box_col + c))
    return cells


def _get_candidates(puzzle: List[List[int]], row: int, col: int, size: int) -> Set[int]:
    """Get valid candidates for a cell."""
    if puzzle[row][col] != 0:
        return {puzzle[row][col]}
    
    used = set()
    
    # Row constraint
    for c in range(size):
        if puzzle[row][c] != 0:
            used.add(puzzle[row][c])
    
    # Column constraint
    for r in range(size):
        if puzzle[r][col] != 0:
            used.add(puzzle[r][col])
    
    # Box constraint
    box_size = int(math.sqrt(size))
    box_row = (row // box_size) * box_size
    box_col = (col // box_size) * box_size
    for r in range(box_size):
        for c in range(box_size):
            val = puzzle[box_row + r][box_col + c]
            if val != 0:
                used.add(val)
    
    return set(range(1, size + 1)) - used


def _propagate_in_partition(
    puzzle: List[List[int]], 
    box_idx: int, 
    size: int
) -> Tuple[bool, float, Dict[str, Any]]:
    """
    Propagate constraints within a single partition (box).
    
    Uses real μ-spec v2.0 costs:
        μ = 8|canon(question)| + log₂(candidates_before / candidates_after)
    
    Returns:
        (changed, mu_cost, certificate)
    """
    box_size = int(math.sqrt(size))
    cells = _get_box_cells(box_idx, size, box_size)
    
    changed = False
    mu_cost = 0.0
    assignments = []
    
    for row, col in cells:
        if puzzle[row][col] == 0:
            candidates = _get_candidates(puzzle, row, col, size)
            candidates_before = len(candidates) if len(candidates) > 0 else size
            
            if len(candidates) == 1:
                val = list(candidates)[0]
                puzzle[row][col] = val
                changed = True
                
                # Real μ-spec v2.0 cost calculation:
                # Question: "(assign cell[row,col] val)"
                question = f"(assign cell[{row},{col}] {val})"
                mu_question = question_cost_bits(question)
                
                # Information gain: log₂(candidates_before / 1)
                mu_info = information_gain_bits(candidates_before, 1) if candidates_before > 1 else 0.0
                
                step_mu = mu_question + mu_info
                mu_cost += step_mu
                
                assignments.append({
                    'cell': (row, col),
                    'value': val,
                    'candidates_before': candidates_before,
                    'candidates_after': 1,
                    'question': question,
                    'mu_question': mu_question,
                    'mu_information': mu_info,
                    'mu_total': step_mu
                })
            elif len(candidates) == 0:
                # Contradiction - unsolvable
                return False, mu_cost, {'status': 'UNSAT', 'box': box_idx}
    
    # Create certificate for this partition
    certificate = {
        'box_idx': box_idx,
        'assignments': assignments,
        'status': 'SAT' if changed else 'UNCHANGED',
        'hash': hashlib.sha256(str(assignments).encode()).hexdigest()[:16]
    }
    
    return changed, mu_cost, certificate


def solve_sudoku_partitioned(
    puzzle: List[List[int]], 
    size: int = 4
) -> Dict[str, Any]:
    """
    Solve Sudoku using partition logic.
    
    Each box is treated as a module. Constraint propagation happens
    within each module first, then composite witnesses join results.
    
    Args:
        puzzle: 2D list with 0 for empty cells
        size: Puzzle size (4 for 4x4, 9 for 9x9)
    
    Returns:
        Dictionary with solution, certificates, and μ-cost
    """
    # Make a copy to avoid modifying input
    grid = [row[:] for row in puzzle]
    
    box_size = int(math.sqrt(size))
    num_boxes = size  # size boxes in a size×size puzzle
    
    partition_certificates = []
    total_mu = 0
    iterations = 0
    max_iterations = size * size  # Safety limit
    
    while iterations < max_iterations:
        iterations += 1
        any_changed = False
        
        # Process each partition (box)
        for box_idx in range(num_boxes):
            changed, mu_cost, cert = _propagate_in_partition(grid, box_idx, size)
            
            if cert['status'] == 'UNSAT':
                return {
                    'solved': False,
                    'solution': None,
                    'partitions_used': len(partition_certificates),
                    'partition_certificates': partition_certificates,
                    'mu_total': total_mu,
                    'error': f'Contradiction in box {box_idx}'
                }
            
            if changed:
                any_changed = True
                total_mu += mu_cost
                partition_certificates.append(cert)
        
        # Check if solved
        if all(grid[r][c] != 0 for r in range(size) for c in range(size)):
            # Verify solution
            valid = _verify_solution(grid, size)
            
            # Create composite witness
            composite_hash = hashlib.sha256(
                ''.join(c['hash'] for c in partition_certificates).encode()
            ).hexdigest()[:32]
            
            return {
                'solved': valid,
                'solution': grid,
                'partitions_used': len(partition_certificates),
                'partition_certificates': partition_certificates,
                'composite_witness': composite_hash,
                'mu_total': total_mu,
                'iterations': iterations
            }
        
        if not any_changed:
            # Need to guess (backtracking) - simplified for demo
            # Find cell with fewest candidates
            best_cell = None
            best_candidates = None
            
            for r in range(size):
                for c in range(size):
                    if grid[r][c] == 0:
                        cands = _get_candidates(grid, r, c, size)
                        if best_cell is None or len(cands) < len(best_candidates):
                            best_cell = (r, c)
                            best_candidates = cands
            
            if best_cell is None or len(best_candidates) == 0:
                return {
                    'solved': False,
                    'solution': None,
                    'partitions_used': len(partition_certificates),
                    'partition_certificates': partition_certificates,
                    'mu_total': total_mu,
                    'error': 'No solution found'
                }
            
            # Try first candidate (simplified - full solver would backtrack)
            r, c = best_cell
            chosen_val = list(best_candidates)[0]
            grid[r][c] = chosen_val
            
            # Real μ-spec v2.0 cost for guessing:
            # Question cost + information gain from narrowing candidates
            guess_question = f"(guess cell[{r},{c}] {chosen_val})"
            mu_question = question_cost_bits(guess_question)
            mu_info = information_gain_bits(len(best_candidates), 1) if len(best_candidates) > 1 else 0.0
            total_mu += mu_question + mu_info
    
    return {
        'solved': False,
        'solution': None,
        'partitions_used': len(partition_certificates),
        'partition_certificates': partition_certificates,
        'mu_total': total_mu,
        'error': 'Max iterations reached'
    }


def _verify_solution(grid: List[List[int]], size: int) -> bool:
    """Verify a Sudoku solution is valid."""
    box_size = int(math.sqrt(size))
    
    # Check rows
    for r in range(size):
        if sorted(grid[r]) != list(range(1, size + 1)):
            return False
    
    # Check columns
    for c in range(size):
        col = [grid[r][c] for r in range(size)]
        if sorted(col) != list(range(1, size + 1)):
            return False
    
    # Check boxes
    for box_r in range(box_size):
        for box_c in range(box_size):
            box = []
            for r in range(box_size):
                for c in range(box_size):
                    box.append(grid[box_r * box_size + r][box_c * box_size + c])
            if sorted(box) != list(range(1, size + 1)):
                return False
    
    return True


# Example usage and Thiele program representation
SUDOKU_THIELE_PROGRAM = """; sudoku_partition_solver.thm
; Demonstrates partition logic for Sudoku solving

; Create partitions for each 2x2 box (in a 4x4 puzzle)
PNEW {0,1,4,5}     ; Box 0 (top-left)
PNEW {2,3,6,7}     ; Box 1 (top-right)
PNEW {8,9,12,13}   ; Box 2 (bottom-left)
PNEW {10,11,14,15} ; Box 3 (bottom-right)

; Propagate constraints in each partition
PYEXEC "propagate_box(0)"
PYEXEC "propagate_box(1)"
PYEXEC "propagate_box(2)"
PYEXEC "propagate_box(3)"

; Assert local consistency for each partition
LASSERT box0_consistent.smt2
LASSERT box1_consistent.smt2
LASSERT box2_consistent.smt2
LASSERT box3_consistent.smt2

; Create composite witness
LJOIN box0_cert box1_cert
LJOIN joined01 box2_cert
LJOIN joined012 box3_cert

; Accumulate μ-cost
MDLACC

; Emit solution
EMIT "Sudoku solved with partition logic"
"""


if __name__ == '__main__':
    # Demo: Solve a 4x4 Sudoku
    puzzle = [
        [1, 0, 0, 4],
        [0, 0, 3, 0],
        [0, 3, 0, 0],
        [4, 0, 0, 2],
    ]
    
    print("Input puzzle:")
    for row in puzzle:
        print(row)
    
    result = solve_sudoku_partitioned(puzzle, size=4)
    
    print(f"\nSolved: {result['solved']}")
    if result['solved']:
        print("Solution:")
        for row in result['solution']:
            print(row)
        print(f"Partitions used: {result['partitions_used']}")
        print(f"Total μ-cost: {result['mu_total']:.2f}")
        print(f"Composite witness: {result['composite_witness']}")
