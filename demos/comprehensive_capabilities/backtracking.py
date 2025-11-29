#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Backtracking and Constraint Satisfaction

Tests backtracking algorithms:
- N-Queens problem
- Sudoku solving
- Subset sum
- Permutation generation
- Combination generation
"""

import time
from typing import Dict, Any, List, Tuple, Optional


# =============================================================================
# BACKTRACKING ALGORITHMS (identical in both environments)
# =============================================================================

def n_queens(n: int) -> Tuple[List[List[int]], int]:
    """Solve N-Queens problem, return all solutions."""
    solutions = []
    backtracks = [0]
    
    def is_safe(board, row, col):
        # Check column
        for i in range(row):
            if board[i] == col:
                return False
        # Check diagonals
        for i in range(row):
            if abs(board[i] - col) == row - i:
                return False
        return True
    
    def solve(board, row):
        if row == n:
            solutions.append(board[:])
            return
        
        for col in range(n):
            backtracks[0] += 1
            if is_safe(board, row, col):
                board[row] = col
                solve(board, row + 1)
    
    solve([-1] * n, 0)
    return solutions, backtracks[0]


def sudoku_solve(board: List[List[int]]) -> Tuple[bool, int]:
    """Solve a Sudoku puzzle using backtracking."""
    backtracks = [0]
    
    def find_empty():
        for i in range(9):
            for j in range(9):
                if board[i][j] == 0:
                    return i, j
        return None
    
    def is_valid(num, row, col):
        # Check row
        if num in board[row]:
            return False
        # Check column
        for i in range(9):
            if board[i][col] == num:
                return False
        # Check 3x3 box
        box_row, box_col = 3 * (row // 3), 3 * (col // 3)
        for i in range(box_row, box_row + 3):
            for j in range(box_col, box_col + 3):
                if board[i][j] == num:
                    return False
        return True
    
    def solve():
        pos = find_empty()
        if pos is None:
            return True
        
        row, col = pos
        for num in range(1, 10):
            backtracks[0] += 1
            if is_valid(num, row, col):
                board[row][col] = num
                if solve():
                    return True
                board[row][col] = 0
        return False
    
    solved = solve()
    return solved, backtracks[0]


def subset_sum(nums: List[int], target: int) -> Tuple[Optional[List[int]], int]:
    """Find a subset that sums to target."""
    backtracks = [0]
    result = [None]
    
    def solve(index, current_sum, current_set):
        backtracks[0] += 1
        
        if current_sum == target:
            result[0] = current_set[:]
            return True
        
        if index >= len(nums) or current_sum > target:
            return False
        
        # Include current element
        current_set.append(nums[index])
        if solve(index + 1, current_sum + nums[index], current_set):
            return True
        current_set.pop()
        
        # Exclude current element
        if solve(index + 1, current_sum, current_set):
            return True
        
        return False
    
    solve(0, 0, [])
    return result[0], backtracks[0]


def generate_permutations(n: int) -> Tuple[List[List[int]], int]:
    """Generate all permutations of [0, 1, ..., n-1]."""
    permutations = []
    ops = [0]
    
    def permute(arr, start):
        if start == len(arr):
            ops[0] += 1
            permutations.append(arr[:])
            return
        
        for i in range(start, len(arr)):
            ops[0] += 1
            arr[start], arr[i] = arr[i], arr[start]
            permute(arr, start + 1)
            arr[start], arr[i] = arr[i], arr[start]
    
    permute(list(range(n)), 0)
    return permutations, ops[0]


def generate_combinations(n: int, k: int) -> Tuple[List[List[int]], int]:
    """Generate all k-combinations of [0, 1, ..., n-1]."""
    combinations = []
    ops = [0]
    
    def combine(start, current):
        if len(current) == k:
            ops[0] += 1
            combinations.append(current[:])
            return
        
        for i in range(start, n):
            ops[0] += 1
            current.append(i)
            combine(i + 1, current)
            current.pop()
    
    combine(0, [])
    return combinations, ops[0]


def knight_tour_count(n: int, max_moves: int = 100) -> Tuple[int, int]:
    """Count valid knight move sequences from (0,0) up to max_moves."""
    moves = [0]
    ops = [0]
    
    knight_moves = [
        (2, 1), (2, -1), (-2, 1), (-2, -1),
        (1, 2), (1, -2), (-1, 2), (-1, -2)
    ]
    
    def explore(x, y, depth, visited):
        ops[0] += 1
        if depth >= max_moves:
            return
        
        for dx, dy in knight_moves:
            nx, ny = x + dx, y + dy
            if 0 <= nx < n and 0 <= ny < n and (nx, ny) not in visited:
                moves[0] += 1
                visited.add((nx, ny))
                explore(nx, ny, depth + 1, visited)
                visited.remove((nx, ny))
    
    visited = {(0, 0)}
    explore(0, 0, 0, visited)
    return moves[0], ops[0]


# =============================================================================
# TEST RUNNER
# =============================================================================

def run_standard_python() -> Dict[str, Any]:
    """Run all backtracking tests with standard Python."""
    results = {'runtime': 'Standard Python', 'tests': []}
    
    test_cases = [
        # N-Queens
        ("4-Queens", lambda: n_queens(4)),
        ("5-Queens", lambda: n_queens(5)),
        ("6-Queens", lambda: n_queens(6)),
        
        # Subset sum
        ("Subset sum exists", lambda: subset_sum([3, 1, 4, 2, 5], 9)),
        ("Subset sum no solution", lambda: subset_sum([2, 4, 6], 7)),
        ("Subset sum exact", lambda: subset_sum([1, 2, 3, 4, 5], 15)),
        
        # Permutations
        ("Permutations n=3", lambda: generate_permutations(3)),
        ("Permutations n=4", lambda: generate_permutations(4)),
        
        # Combinations
        ("C(5,2)", lambda: generate_combinations(5, 2)),
        ("C(6,3)", lambda: generate_combinations(6, 3)),
        ("C(4,4)", lambda: generate_combinations(4, 4)),
        
        # Knight tour (limited)
        ("Knight 4x4 depth 10", lambda: knight_tour_count(4, 10)),
        ("Knight 5x5 depth 8", lambda: knight_tour_count(5, 8)),
    ]
    
    for name, test_fn in test_cases:
        start = time.time()
        result, ops = test_fn()
        elapsed = time.time() - start
        
        # Normalize result for comparison
        if isinstance(result, list) and len(result) > 0 and isinstance(result[0], list):
            result_summary = len(result)  # Count of solutions
        else:
            result_summary = result
        
        results['tests'].append({
            'name': name,
            'result': result_summary,
            'full_result': result,
            'operations': ops,
            'time': elapsed,
        })
    
    return results


def run_thiele_vm() -> Dict[str, Any]:
    """Run all backtracking tests through Thiele VM."""
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    results = {'runtime': 'Thiele VM', 'tests': []}
    
    test_cases = [
        # N-Queens
        ("4-Queens", '''
n = 4
solutions = []
backtracks = [0]

def is_safe(board, row, col):
    for i in range(row):
        if board[i] == col:
            return False
    for i in range(row):
        if abs(board[i] - col) == row - i:
            return False
    return True

def solve(board, row):
    if row == n:
        solutions.append(board[:])
        return
    for col in range(n):
        backtracks[0] = backtracks[0] + 1
        if is_safe(board, row, col):
            board[row] = col
            solve(board, row + 1)

solve([-1] * n, 0)
__result__ = (len(solutions), backtracks[0])
'''),
        ("5-Queens", '''
n = 5
solutions = []
backtracks = [0]

def is_safe(board, row, col):
    for i in range(row):
        if board[i] == col:
            return False
    for i in range(row):
        if abs(board[i] - col) == row - i:
            return False
    return True

def solve(board, row):
    if row == n:
        solutions.append(board[:])
        return
    for col in range(n):
        backtracks[0] = backtracks[0] + 1
        if is_safe(board, row, col):
            board[row] = col
            solve(board, row + 1)

solve([-1] * n, 0)
__result__ = (len(solutions), backtracks[0])
'''),
        ("6-Queens", '''
n = 6
solutions = []
backtracks = [0]

def is_safe(board, row, col):
    for i in range(row):
        if board[i] == col:
            return False
    for i in range(row):
        if abs(board[i] - col) == row - i:
            return False
    return True

def solve(board, row):
    if row == n:
        solutions.append(board[:])
        return
    for col in range(n):
        backtracks[0] = backtracks[0] + 1
        if is_safe(board, row, col):
            board[row] = col
            solve(board, row + 1)

solve([-1] * n, 0)
__result__ = (len(solutions), backtracks[0])
'''),
        # Subset sum
        ("Subset sum exists", '''
nums = [3, 1, 4, 2, 5]
target = 9
backtracks = [0]
result = [None]

def solve(index, current_sum, current_set):
    backtracks[0] = backtracks[0] + 1
    if current_sum == target:
        result[0] = current_set[:]
        return True
    if index >= len(nums) or current_sum > target:
        return False
    current_set.append(nums[index])
    if solve(index + 1, current_sum + nums[index], current_set):
        return True
    current_set.pop()
    if solve(index + 1, current_sum, current_set):
        return True
    return False

solve(0, 0, [])
__result__ = (result[0], backtracks[0])
'''),
        ("Subset sum no solution", '''
nums = [2, 4, 6]
target = 7
backtracks = [0]
result = [None]

def solve(index, current_sum, current_set):
    backtracks[0] = backtracks[0] + 1
    if current_sum == target:
        result[0] = current_set[:]
        return True
    if index >= len(nums) or current_sum > target:
        return False
    current_set.append(nums[index])
    if solve(index + 1, current_sum + nums[index], current_set):
        return True
    current_set.pop()
    if solve(index + 1, current_sum, current_set):
        return True
    return False

solve(0, 0, [])
__result__ = (result[0], backtracks[0])
'''),
        ("Subset sum exact", '''
nums = [1, 2, 3, 4, 5]
target = 15
backtracks = [0]
result = [None]

def solve(index, current_sum, current_set):
    backtracks[0] = backtracks[0] + 1
    if current_sum == target:
        result[0] = current_set[:]
        return True
    if index >= len(nums) or current_sum > target:
        return False
    current_set.append(nums[index])
    if solve(index + 1, current_sum + nums[index], current_set):
        return True
    current_set.pop()
    if solve(index + 1, current_sum, current_set):
        return True
    return False

solve(0, 0, [])
__result__ = (result[0], backtracks[0])
'''),
        # Permutations
        ("Permutations n=3", '''
n = 3
permutations = []
ops = [0]

def permute(arr, start):
    if start == len(arr):
        ops[0] = ops[0] + 1
        permutations.append(arr[:])
        return
    for i in range(start, len(arr)):
        ops[0] = ops[0] + 1
        arr[start], arr[i] = arr[i], arr[start]
        permute(arr, start + 1)
        arr[start], arr[i] = arr[i], arr[start]

permute(list(range(n)), 0)
__result__ = (len(permutations), ops[0])
'''),
        ("Permutations n=4", '''
n = 4
permutations = []
ops = [0]

def permute(arr, start):
    if start == len(arr):
        ops[0] = ops[0] + 1
        permutations.append(arr[:])
        return
    for i in range(start, len(arr)):
        ops[0] = ops[0] + 1
        arr[start], arr[i] = arr[i], arr[start]
        permute(arr, start + 1)
        arr[start], arr[i] = arr[i], arr[start]

permute(list(range(n)), 0)
__result__ = (len(permutations), ops[0])
'''),
        # Combinations
        ("C(5,2)", '''
n, k = 5, 2
combinations = []
ops = [0]

def combine(start, current):
    if len(current) == k:
        ops[0] = ops[0] + 1
        combinations.append(current[:])
        return
    for i in range(start, n):
        ops[0] = ops[0] + 1
        current.append(i)
        combine(i + 1, current)
        current.pop()

combine(0, [])
__result__ = (len(combinations), ops[0])
'''),
        ("C(6,3)", '''
n, k = 6, 3
combinations = []
ops = [0]

def combine(start, current):
    if len(current) == k:
        ops[0] = ops[0] + 1
        combinations.append(current[:])
        return
    for i in range(start, n):
        ops[0] = ops[0] + 1
        current.append(i)
        combine(i + 1, current)
        current.pop()

combine(0, [])
__result__ = (len(combinations), ops[0])
'''),
        ("C(4,4)", '''
n, k = 4, 4
combinations = []
ops = [0]

def combine(start, current):
    if len(current) == k:
        ops[0] = ops[0] + 1
        combinations.append(current[:])
        return
    for i in range(start, n):
        ops[0] = ops[0] + 1
        current.append(i)
        combine(i + 1, current)
        current.pop()

combine(0, [])
__result__ = (len(combinations), ops[0])
'''),
        # Knight tour
        ("Knight 4x4 depth 10", '''
n = 4
max_moves = 10
moves = [0]
ops = [0]
knight_moves = [(2, 1), (2, -1), (-2, 1), (-2, -1), (1, 2), (1, -2), (-1, 2), (-1, -2)]

def explore(x, y, depth, visited):
    ops[0] = ops[0] + 1
    if depth >= max_moves:
        return
    for dx, dy in knight_moves:
        nx, ny = x + dx, y + dy
        if 0 <= nx < n and 0 <= ny < n and (nx, ny) not in visited:
            moves[0] = moves[0] + 1
            visited.add((nx, ny))
            explore(nx, ny, depth + 1, visited)
            visited.remove((nx, ny))

visited = {(0, 0)}
explore(0, 0, 0, visited)
__result__ = (moves[0], ops[0])
'''),
        ("Knight 5x5 depth 8", '''
n = 5
max_moves = 8
moves = [0]
ops = [0]
knight_moves = [(2, 1), (2, -1), (-2, 1), (-2, -1), (1, 2), (1, -2), (-1, 2), (-1, -2)]

def explore(x, y, depth, visited):
    ops[0] = ops[0] + 1
    if depth >= max_moves:
        return
    for dx, dy in knight_moves:
        nx, ny = x + dx, y + dy
        if 0 <= nx < n and 0 <= ny < n and (nx, ny) not in visited:
            moves[0] = moves[0] + 1
            visited.add((nx, ny))
            explore(nx, ny, depth + 1, visited)
            visited.remove((nx, ny))

visited = {(0, 0)}
explore(0, 0, 0, visited)
__result__ = (moves[0], ops[0])
'''),
    ]
    
    for name, code in test_cases:
        vm = VM(State())
        start = time.time()
        res, _ = vm.execute_python(code)
        elapsed = time.time() - start
        
        result, ops = res if res else (None, 0)
        mu_cost = question_cost_bits(f"(backtrack {name})") + ops * 0.1
        
        results['tests'].append({
            'name': name,
            'result': result,
            'operations': ops,
            'time': elapsed,
            'mu_cost': mu_cost,
        })
    
    return results


def compare_and_report() -> Dict[str, Any]:
    """Run both and compare results."""
    print("=" * 70)
    print("BACKTRACKING AND CONSTRAINT SATISFACTION")
    print("=" * 70)
    
    std_results = run_standard_python()
    vm_results = run_thiele_vm()
    
    all_match = True
    comparison_results = []
    
    print(f"\n{'Test Name':<25} {'Std Result':<15} {'VM Result':<15} {'Ops Match':<10}")
    print("-" * 70)
    
    for std_test, vm_test in zip(std_results['tests'], vm_results['tests']):
        std_res = std_test['result']
        vm_res = vm_test['result']
        
        # Handle list comparison (count)
        if isinstance(std_res, list):
            std_res = len(std_res) if isinstance(std_res[0], list) else std_res
        
        result_match = std_res == vm_res
        ops_match = std_test['operations'] == vm_test['operations']
        match = result_match and ops_match
        if not match:
            all_match = False
        
        status = "✓" if match else "✗"
        ops_status = "✓" if ops_match else "✗"
        
        print(f"{std_test['name']:<25} {str(std_res)[:12]:<15} {str(vm_res)[:12]:<15} {ops_status:<10}")
        
        comparison_results.append({
            'name': std_test['name'],
            'std_result': std_res,
            'vm_result': vm_res,
            'std_ops': std_test['operations'],
            'vm_ops': vm_test['operations'],
            'match': match,
            'mu_cost': vm_test.get('mu_cost', 0),
        })
    
    print("\n" + "-" * 70)
    print(f"ISOMORPHISM: {'✓ ALL TESTS PASS' if all_match else '✗ SOME TESTS FAILED'}")
    print(f"Total tests: {len(comparison_results)}")
    print(f"Matching: {sum(1 for r in comparison_results if r['match'])}")
    
    return {
        'category': 'Backtracking and Constraint Satisfaction',
        'all_match': all_match,
        'comparisons': comparison_results,
    }


if __name__ == "__main__":
    compare_and_report()
