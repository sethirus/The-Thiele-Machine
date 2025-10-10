# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import time
from typing import List, Optional

# Simple Sudoku puzzle and its solution (0 denotes empty cell)
PUZZLE: List[List[int]] = [
    [5, 3, 0, 0, 7, 0, 0, 0, 0],
    [6, 0, 0, 1, 9, 5, 0, 0, 0],
    [0, 9, 8, 0, 0, 0, 0, 6, 0],
    [8, 0, 0, 0, 6, 0, 0, 0, 3],
    [4, 0, 0, 8, 0, 3, 0, 0, 1],
    [7, 0, 0, 0, 2, 0, 0, 0, 6],
    [0, 6, 0, 0, 0, 0, 2, 8, 0],
    [0, 0, 0, 4, 1, 9, 0, 0, 5],
    [0, 0, 0, 0, 8, 6, 0, 7, 9],
]

SOLUTION: List[List[int]] = [
    [5, 3, 4, 6, 7, 8, 9, 1, 2],
    [6, 7, 2, 1, 9, 5, 3, 4, 8],
    [1, 9, 8, 3, 4, 2, 5, 6, 7],
    [8, 5, 9, 7, 6, 1, 4, 2, 3],
    [4, 2, 6, 8, 5, 3, 7, 9, 1],
    [7, 1, 3, 9, 2, 4, 8, 5, 6],
    [9, 6, 1, 5, 3, 7, 2, 8, 4],
    [2, 8, 7, 4, 1, 9, 6, 3, 5],
    [3, 4, 5, 2, 8, 6, 1, 7, 9],
]

Grid = List[List[int]]


def is_valid(grid: Grid, r: int, c: int, val: int) -> bool:
    """Check whether placing val at (r,c) obeys Sudoku rules."""
    if any(grid[r][i] == val for i in range(9)):
        return False
    if any(grid[i][c] == val for i in range(9)):
        return False
    br, bc = 3 * (r // 3), 3 * (c // 3)
    for i in range(br, br + 3):
        for j in range(bc, bc + 3):
            if grid[i][j] == val:
                return False
    return True


def turing_solve(grid: Grid) -> bool:
    """Brute-force search for a satisfying assignment (Turing style)."""
    for r in range(9):
        for c in range(9):
            if grid[r][c] == 0:
                for val in range(1, 10):
                    if is_valid(grid, r, c, val):
                        grid[r][c] = val
                        # Explore this branch
                        if turing_solve(grid):
                            return True
                        # Backtrack
                        grid[r][c] = 0
                return False
    return True


def thiele_solve(puzzle: Grid, solution: Grid) -> bool:
    """Sighted check: verify solution against puzzle without search.
    The Thiele demo checks a provided solution; it does not find one."""
    # Ensure solution respects puzzle clues
    for r in range(9):
        for c in range(9):
            if puzzle[r][c] != 0 and puzzle[r][c] != solution[r][c]:
                return False
    # Validate rows and columns
    for i in range(9):
        if len(set(solution[i])) != 9:
            return False
        if len({solution[r][i] for r in range(9)}) != 9:
            return False
    # Validate 3x3 boxes
    for br in range(0, 9, 3):
        for bc in range(0, 9, 3):
            block = set()
            for r in range(br, br + 3):
                for c in range(bc, bc + 3):
                    block.add(solution[r][c])
            if len(block) != 9:
                return False
    return True


def format_grid(grid: Grid) -> str:
    return "\n".join(" ".join(str(n) for n in row) for row in grid)


def main() -> None:
    import copy

    # Turing-style solving
    grid = copy.deepcopy(PUZZLE)
    start = time.time()
    turing_solve(grid)
    turing_time = time.time() - start
    print("Turing solver result:")
    print(format_grid(grid))
    print(f"Turing time: {turing_time:.4f} seconds")

    # Thiele-style solving
    start = time.time()
    ok = thiele_solve(PUZZLE, SOLUTION)
    thiele_time = time.time() - start
    print("Thiele check result:", ok)
    print(f"Thiele time: {thiele_time:.6f} seconds")


if __name__ == "__main__":
    main()
