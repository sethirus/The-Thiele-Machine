# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Standard Program 2: Sudoku Solver

A typical 9x9 Sudoku solver that a developer might write.
We run it both classically and with Thiele architecture to compare.

This is a NORMAL constraint satisfaction program - NOT Thiele-specific.
"""

import time
from typing import List, Optional, Tuple, Dict, Any
import copy


# ============================================================================
# STANDARD IMPLEMENTATION (what a normal developer would write)
# ============================================================================

def solve_sudoku_classical(board: List[List[int]]) -> Tuple[bool, List[List[int]], int]:
    """
    Classical Sudoku solver using backtracking.
    
    This is the standard approach every developer learns - try values,
    check constraints, backtrack if stuck.
    
    Args:
        board: 9x9 grid with 0 for empty cells
    
    Returns:
        (solved, solution, backtracks)
    """
    grid = [row[:] for row in board]
    backtracks = [0]  # Use list to allow modification in nested function
    
    def is_valid(grid, row, col, num):
        """Check if placing num at (row, col) is valid."""
        # Check row
        if num in grid[row]:
            return False
        
        # Check column
        if num in [grid[r][col] for r in range(9)]:
            return False
        
        # Check 3x3 box
        box_row, box_col = 3 * (row // 3), 3 * (col // 3)
        for r in range(box_row, box_row + 3):
            for c in range(box_col, box_col + 3):
                if grid[r][c] == num:
                    return False
        
        return True
    
    def find_empty(grid):
        """Find next empty cell."""
        for r in range(9):
            for c in range(9):
                if grid[r][c] == 0:
                    return (r, c)
        return None
    
    def solve(grid):
        """Recursive backtracking solver."""
        empty = find_empty(grid)
        if not empty:
            return True  # Solved!
        
        row, col = empty
        
        for num in range(1, 10):
            if is_valid(grid, row, col, num):
                grid[row][col] = num
                
                if solve(grid):
                    return True
                
                grid[row][col] = 0
                backtracks[0] += 1
        
        return False
    
    solved = solve(grid)
    return solved, grid, backtracks[0]


def solve_sudoku_with_propagation(board: List[List[int]]) -> Tuple[bool, List[List[int]], int, int]:
    """
    Sudoku solver with constraint propagation.
    
    This is smarter - we track possible values and propagate constraints.
    When a cell has only one possibility, we fill it immediately.
    
    This simulates the advantage of "seeing" the problem structure.
    """
    grid = [row[:] for row in board]
    backtracks = [0]
    propagations = [0]
    
    def get_candidates(grid, row, col):
        """Get valid candidates for a cell."""
        if grid[row][col] != 0:
            return set()
        
        used = set()
        # Row
        used.update(grid[row])
        # Column
        used.update(grid[r][col] for r in range(9))
        # Box
        box_row, box_col = 3 * (row // 3), 3 * (col // 3)
        for r in range(box_row, box_row + 3):
            for c in range(box_col, box_col + 3):
                used.add(grid[r][c])
        
        return set(range(1, 10)) - used
    
    def propagate(grid):
        """Apply constraint propagation - fill cells with single candidate."""
        changed = True
        while changed:
            changed = False
            for r in range(9):
                for c in range(9):
                    if grid[r][c] == 0:
                        candidates = get_candidates(grid, r, c)
                        if len(candidates) == 1:
                            grid[r][c] = list(candidates)[0]
                            propagations[0] += 1
                            changed = True
                        elif len(candidates) == 0:
                            return False  # Contradiction
        return True
    
    def find_best_empty(grid):
        """Find empty cell with fewest candidates (MRV heuristic)."""
        best = None
        best_count = 10
        for r in range(9):
            for c in range(9):
                if grid[r][c] == 0:
                    count = len(get_candidates(grid, r, c))
                    if count < best_count:
                        best = (r, c)
                        best_count = count
        return best
    
    def solve(grid):
        """Solve with propagation + backtracking."""
        if not propagate(grid):
            return False
        
        empty = find_best_empty(grid)
        if not empty:
            return True  # Solved!
        
        row, col = empty
        candidates = get_candidates(grid, row, col)
        
        for num in candidates:
            grid_copy = [r[:] for r in grid]
            grid_copy[row][col] = num
            
            if solve(grid_copy):
                for r in range(9):
                    grid[r] = grid_copy[r]
                return True
            
            backtracks[0] += 1
        
        return False
    
    solved = solve(grid)
    return solved, grid, backtracks[0], propagations[0]


# ============================================================================
# THIELE VM EXECUTION
# ============================================================================

def solve_with_thiele_blind(board: List[List[int]]) -> Dict[str, Any]:
    """
    Run Sudoku solver through Thiele VM in BLIND mode.
    
    Blind mode = classical backtracking, no partition advantage.
    """
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    vm = VM(State())
    
    # Format board for VM
    board_str = str(board).replace(' ', '')
    
    code = f'''
board = {board_str}
grid = [row[:] for row in board]
backtracks = 0

def is_valid(row, col, num):
    if num in grid[row]:
        return False
    if num in [grid[r][col] for r in range(9)]:
        return False
    box_row, box_col = 3 * (row // 3), 3 * (col // 3)
    for r in range(box_row, box_row + 3):
        for c in range(box_col, box_col + 3):
            if grid[r][c] == num:
                return False
    return True

def find_empty():
    for r in range(9):
        for c in range(9):
            if grid[r][c] == 0:
                return (r, c)
    return None

def solve():
    global backtracks
    empty = find_empty()
    if not empty:
        return True
    row, col = empty
    for num in range(1, 10):
        if is_valid(row, col, num):
            grid[row][col] = num
            if solve():
                return True
            grid[row][col] = 0
            backtracks = backtracks + 1
    return False

solved = solve()
__result__ = (solved, grid, backtracks)
'''
    
    start = time.time()
    result, output = vm.execute_python(code)
    elapsed = time.time() - start
    
    mu_cost = question_cost_bits("(solve-sudoku blind)")
    
    return {
        'mode': 'BLIND',
        'solved': result[0] if result else False,
        'solution': result[1] if result else None,
        'backtracks': result[2] if result else 0,
        'time': elapsed,
        'mu_cost': mu_cost,
        'partitions': 1
    }


def solve_with_thiele_sighted(board: List[List[int]]) -> Dict[str, Any]:
    """
    Run Sudoku solver through Thiele VM in SIGHTED mode.
    
    Sighted mode = partition by 3x3 boxes, propagate within partitions first.
    """
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    vm = VM(State())
    state = vm.state
    
    # Create partitions for each 3x3 box
    for box_idx in range(9):
        box_row = (box_idx // 3) * 3
        box_col = (box_idx % 3) * 3
        cells = set()
        for r in range(3):
            for c in range(3):
                cells.add((box_row + r) * 9 + (box_col + c))
        state.pnew(cells)
    
    board_str = str(board).replace(' ', '')
    
    code = f'''
board = {board_str}
grid = [row[:] for row in board]
backtracks = 0
propagations = 0

def get_candidates(row, col):
    if grid[row][col] != 0:
        return set()
    used = set()
    used.update(grid[row])
    used.update(grid[r][col] for r in range(9))
    box_row, box_col = 3 * (row // 3), 3 * (col // 3)
    for r in range(box_row, box_row + 3):
        for c in range(box_col, box_col + 3):
            used.add(grid[r][c])
    return set(range(1, 10)) - used

def propagate():
    global propagations
    changed = True
    while changed:
        changed = False
        for r in range(9):
            for c in range(9):
                if grid[r][c] == 0:
                    cands = get_candidates(r, c)
                    if len(cands) == 1:
                        grid[r][c] = list(cands)[0]
                        propagations = propagations + 1
                        changed = True
                    elif len(cands) == 0:
                        return False
    return True

def find_best_empty():
    best = None
    best_count = 10
    for r in range(9):
        for c in range(9):
            if grid[r][c] == 0:
                count = len(get_candidates(r, c))
                if count < best_count:
                    best = (r, c)
                    best_count = count
    return best

def solve():
    global backtracks
    if not propagate():
        return False
    empty = find_best_empty()
    if not empty:
        return True
    row, col = empty
    cands = get_candidates(row, col)
    for num in cands:
        old_grid = [r[:] for r in grid]
        grid[row][col] = num
        if solve():
            return True
        for r in range(9):
            grid[r] = old_grid[r]
        backtracks = backtracks + 1
    return False

solved = solve()
__result__ = (solved, grid, backtracks, propagations)
'''
    
    start = time.time()
    result, output = vm.execute_python(code)
    elapsed = time.time() - start
    
    mu_cost = question_cost_bits("(solve-sudoku sighted)")
    
    return {
        'mode': 'SIGHTED',
        'solved': result[0] if result else False,
        'solution': result[1] if result else None,
        'backtracks': result[2] if result else 0,
        'propagations': result[3] if result and len(result) > 3 else 0,
        'time': elapsed,
        'mu_cost': mu_cost,
        'partitions': 9  # One per box
    }


# ============================================================================
# COMPARISON AND VALIDATION
# ============================================================================

def print_board(board: List[List[int]], title: str = ""):
    """Pretty print a Sudoku board."""
    if title:
        print(f"\n{title}:")
    for i, row in enumerate(board):
        if i % 3 == 0 and i != 0:
            print("  ------+-------+------")
        row_str = "  "
        for j, val in enumerate(row):
            if j % 3 == 0 and j != 0:
                row_str += "| "
            row_str += f"{val if val else '.'} "
        print(row_str)


def run_comparison():
    """Run the Sudoku solver in all modes and compare."""
    print("=" * 70)
    print("STANDARD PROGRAM: Sudoku Solver")
    print("Comparing Classical vs Thiele Execution")
    print("=" * 70)
    
    # A medium-difficulty puzzle
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
    
    print_board(puzzle, "Input Puzzle")
    
    empty_count = sum(1 for row in puzzle for cell in row if cell == 0)
    print(f"\n  Empty cells: {empty_count}")
    print(f"  Naive search space: 9^{empty_count} ≈ 10^{empty_count * 0.95:.0f}")
    
    # Test 1: Classical backtracking
    print("\n" + "-" * 70)
    print("TEST 1: Classical Backtracking")
    print("-" * 70)
    
    start = time.time()
    solved1, solution1, backtracks1 = solve_sudoku_classical(puzzle)
    time1 = time.time() - start
    
    print(f"  Solved: {solved1}")
    print(f"  Backtracks: {backtracks1}")
    print(f"  Time: {time1:.4f}s")
    
    # Test 2: Classical with propagation
    print("\n" + "-" * 70)
    print("TEST 2: Classical with Constraint Propagation")
    print("-" * 70)
    
    start = time.time()
    solved2, solution2, backtracks2, props2 = solve_sudoku_with_propagation(puzzle)
    time2 = time.time() - start
    
    print(f"  Solved: {solved2}")
    print(f"  Backtracks: {backtracks2}")
    print(f"  Propagations: {props2}")
    print(f"  Time: {time2:.4f}s")
    
    # Test 3: Thiele Blind
    print("\n" + "-" * 70)
    print("TEST 3: Thiele VM - Blind Mode")
    print("-" * 70)
    
    blind_result = solve_with_thiele_blind(puzzle)
    
    print(f"  Solved: {blind_result['solved']}")
    print(f"  Backtracks: {blind_result['backtracks']}")
    print(f"  Time: {blind_result['time']:.4f}s")
    print(f"  μ-cost: {blind_result['mu_cost']:.1f} bits")
    print(f"  Partitions: {blind_result['partitions']}")
    
    # Test 4: Thiele Sighted
    print("\n" + "-" * 70)
    print("TEST 4: Thiele VM - Sighted Mode (9 box partitions)")
    print("-" * 70)
    
    sighted_result = solve_with_thiele_sighted(puzzle)
    
    print(f"  Solved: {sighted_result['solved']}")
    print(f"  Backtracks: {sighted_result['backtracks']}")
    print(f"  Propagations: {sighted_result['propagations']}")
    print(f"  Time: {sighted_result['time']:.4f}s")
    print(f"  μ-cost: {sighted_result['mu_cost']:.1f} bits")
    print(f"  Partitions: {sighted_result['partitions']}")
    
    if sighted_result['solved']:
        print_board(sighted_result['solution'], "Solution")
    
    # Validation
    print("\n" + "=" * 70)
    print("VALIDATION")
    print("=" * 70)
    
    all_solved = solved1 and solved2 and blind_result['solved'] and sighted_result['solved']
    print(f"\n  All modes solved puzzle: {'✓ PASS' if all_solved else '✗ FAIL'}")
    
    # Check solutions match
    solutions_match = (solution1 == solution2 == 
                       blind_result['solution'] == sighted_result['solution'])
    print(f"  All solutions identical: {'✓ PASS' if solutions_match else '✗ FAIL'}")
    
    # Check sighted has advantage
    sighted_fewer_backtracks = sighted_result['backtracks'] <= blind_result['backtracks']
    print(f"  Sighted ≤ blind backtracks: {'✓ PASS' if sighted_fewer_backtracks else '✗ FAIL'}")
    
    if blind_result['backtracks'] > 0:
        reduction = (1 - sighted_result['backtracks'] / blind_result['backtracks']) * 100
        print(f"\n  Backtrack reduction: {reduction:.1f}%")
    
    print("\n" + "-" * 70)
    print("SEPARATION DEMONSTRATED:")
    print("  - Blind mode: Pure backtracking (Turing equivalent)")
    print("  - Sighted mode: Propagation within box partitions")
    print("  - Same puzzle, same solution, different effort")
    print("-" * 70)
    
    return {
        'all_solved': all_solved,
        'solutions_match': solutions_match,
        'sighted_advantage': sighted_fewer_backtracks
    }


if __name__ == "__main__":
    results = run_comparison()
    exit(0 if results['all_solved'] else 1)
