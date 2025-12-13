"""Standard Program: Sudoku Solver

A typical 9x9 Sudoku solver; includes a Thiele VM execution wrapper.
"""

from __future__ import annotations

import time
from typing import Any, Dict, List, Optional, Tuple


def solve_sudoku_classical(board: List[List[int]]) -> Tuple[bool, List[List[int]], int]:
    grid = [row[:] for row in board]
    backtracks = [0]

    def is_valid(grid_, row, col, num):
        if num in grid_[row]:
            return False
        if num in [grid_[r][col] for r in range(9)]:
            return False
        box_row, box_col = 3 * (row // 3), 3 * (col // 3)
        for r in range(box_row, box_row + 3):
            for c in range(box_col, box_col + 3):
                if grid_[r][c] == num:
                    return False
        return True

    def find_empty(grid_):
        for r in range(9):
            for c in range(9):
                if grid_[r][c] == 0:
                    return (r, c)
        return None

    def solve(grid_):
        empty = find_empty(grid_)
        if not empty:
            return True
        row, col = empty
        for num in range(1, 10):
            if is_valid(grid_, row, col, num):
                grid_[row][col] = num
                if solve(grid_):
                    return True
                grid_[row][col] = 0
                backtracks[0] += 1
        return False

    solved = solve(grid)
    return solved, grid, backtracks[0]


def solve_sudoku_with_propagation(board: List[List[int]]) -> Tuple[bool, List[List[int]], int, int]:
    grid = [row[:] for row in board]
    backtracks = [0]
    propagations = [0]

    def get_candidates(grid_, row, col):
        if grid_[row][col] != 0:
            return set()
        used = set()
        used.update(grid_[row])
        used.update(grid_[r][col] for r in range(9))
        box_row, box_col = 3 * (row // 3), 3 * (col // 3)
        for r in range(box_row, box_row + 3):
            for c in range(box_col, box_col + 3):
                used.add(grid_[r][c])
        return set(range(1, 10)) - used

    def propagate(grid_):
        changed = True
        while changed:
            changed = False
            for r in range(9):
                for c in range(9):
                    if grid_[r][c] == 0:
                        candidates = get_candidates(grid_, r, c)
                        if len(candidates) == 1:
                            grid_[r][c] = list(candidates)[0]
                            propagations[0] += 1
                            changed = True
                        elif len(candidates) == 0:
                            return False
        return True

    def find_best_empty(grid_):
        best = None
        best_count = 10
        for r in range(9):
            for c in range(9):
                if grid_[r][c] == 0:
                    count = len(get_candidates(grid_, r, c))
                    if count < best_count:
                        best = (r, c)
                        best_count = count
        return best

    def solve(grid_):
        if not propagate(grid_):
            return False
        empty = find_best_empty(grid_)
        if not empty:
            return True
        row, col = empty
        candidates = get_candidates(grid_, row, col)
        for num in candidates:
            grid_copy = [r[:] for r in grid_]
            grid_copy[row][col] = num
            if solve(grid_copy):
                for r in range(9):
                    grid_[r] = grid_copy[r]
                return True
            backtracks[0] += 1
        return False

    solved = solve(grid)
    return solved, grid, backtracks[0], propagations[0]


def solve_with_thiele_blind(board: List[List[int]]) -> Dict[str, Any]:
    from thielecpu.mu import question_cost_bits
    from thielecpu.state import State
    from thielecpu.vm import VM

    vm = VM(State())
    board_str = str(board).replace(" ", "")

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
    result, _ = vm.execute_python(code)
    elapsed = time.time() - start

    mu_cost = question_cost_bits("(solve-sudoku blind)")
    return {
        "mode": "BLIND",
        "solved": result[0] if result else False,
        "solution": result[1] if result else None,
        "backtracks": result[2] if result else 0,
        "time": elapsed,
        "mu_cost": mu_cost,
        "partitions": 1,
    }


def solve_with_thiele_sighted(board: List[List[int]]) -> Dict[str, Any]:
    from thielecpu.mu import question_cost_bits
    from thielecpu.state import State
    from thielecpu.vm import VM

    vm = VM(State())
    state = vm.state

    for box_idx in range(9):
        box_row = (box_idx // 3) * 3
        box_col = (box_idx % 3) * 3
        cells = set()
        for r in range(3):
            for c in range(3):
                cells.add((box_row + r) * 9 + (box_col + c))
        state.pnew(cells)

    board_str = str(board).replace(" ", "")

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
        for rr in range(9):
            grid[rr] = old_grid[rr]
        backtracks = backtracks + 1
    return False

solved = solve()
__result__ = (solved, grid, backtracks, propagations)
'''

    start = time.time()
    result, _ = vm.execute_python(code)
    elapsed = time.time() - start

    mu_cost = question_cost_bits("(solve-sudoku sighted)")
    return {
        "mode": "SIGHTED",
        "solved": result[0] if result else False,
        "solution": result[1] if result else None,
        "backtracks": result[2] if result else 0,
        "propagations": result[3] if result and len(result) > 3 else 0,
        "time": elapsed,
        "mu_cost": mu_cost,
        "partitions": 9,
    }
