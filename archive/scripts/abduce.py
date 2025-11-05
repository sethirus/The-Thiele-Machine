# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import time
import sys
from scripts.sudoku_cnf_provider import SudokuCnfProvider
from thielecpu.vm import VM
from thielecpu.state import State
import ast

def load_completed_grid_from_file(filename):
    """Load completed Sudoku grid from file"""
    try:
        with open(filename, 'r') as f:
            lines = f.readlines()
        
        grid = [[0]*10 for _ in range(10)]
        for i, line in enumerate(lines[:9]):
            numbers = line.strip().split()
            if len(numbers) != 9:
                raise ValueError(f"Invalid line {i+1}: expected 9 numbers")
            for j, num in enumerate(numbers):
                grid[i+1][j+1] = int(num)
        return grid
    except FileNotFoundError:
        print(f"Error: File {filename} not found")
        sys.exit(1)
    except ValueError as e:
        print(f"Error parsing grid file: {e}")
        sys.exit(1)

def extract_possible_clues(grid):
    """Extract non-zero positions as possible clues"""
    clues = []
    for r in range(1, 10):
        for c in range(1, 10):
            if grid[r][c] != 0:
                clues.append((r, c))
    return clues

def grid_to_puzzle_string(grid):
    return ''.join(str(grid[r][c]) for r in range(1,10) for c in range(1,10))

def solve_with_vm(provider, assumptions=None):
    clauses = provider.get_all_clauses()
    if assumptions:
        for assumption in assumptions:
            clauses.append([assumption])
    code = f"""
from pysat.solvers import Glucose4

clauses = {clauses}

solver = Glucose4()
for cls in clauses:
    solver.add_clause(cls)

if solver.solve():
    model = solver.get_model()
    print('SAT')
    print(repr(model))
else:
    print('UNSAT')
"""
    vm = VM(State())
    _, output = vm.execute_python(code)
    if 'SAT' in output:
        lines = output.strip().split('\n')
        for line in lines:
            if line.startswith('[') and line.endswith(']'):
                model = ast.literal_eval(line)
                return model
    return None

def is_unique_solution(clues, completed_grid):
    # Temporarily set non-clue cells to 0
    temp_grid = [[0]*10 for _ in range(10)]
    for r in range(1,10):
        for c in range(1,10):
            temp_grid[r][c] = completed_grid[r][c] if (r, c) in clues else 0
    temp_puzzle = grid_to_puzzle_string(temp_grid)
    
    provider = SudokuCnfProvider(temp_puzzle)
    model1 = solve_with_vm(provider)
    if not model1:
        return False  # No solution
    
    # Add negation of the solution
    forbid_clause = []
    for r in range(1,10):
        for c in range(1,10):
            d = completed_grid[r][c]
            var = provider.get_var(r, c, d)
            forbid_clause.append(-var)
    provider.add_clause(forbid_clause)  # Forbid this assignment
    
    model2 = solve_with_vm(provider)
    return model2 is None  # If no second solution, unique

def find_minimal_clues(possible_clues, completed_grid, max_iterations=1000):
    current_clues = set(possible_clues)
    print(f"Starting with {len(current_clues)} clues")
    
    iteration = 0
    while iteration < max_iterations:
        removed = False
        for clue in list(current_clues):
            temp_clues = current_clues - {clue}
            if is_unique_solution(temp_clues, completed_grid):
                current_clues = temp_clues
                print(f"Removed clue {clue}, now {len(current_clues)} clues")
                removed = True
                break
        if not removed:
            break
        iteration += 1
    
    if iteration >= max_iterations:
        print(f"Warning: Reached maximum iterations ({max_iterations})")
    
    return current_clues

def main():
    if len(sys.argv) != 2:
        print("Usage: python abduce.py <completed_grid_file>")
        print("The file should contain a 9x9 Sudoku grid with numbers 1-9")
        sys.exit(1)
    
    grid_file = sys.argv[1]
    
    start_time = time.time()
    
    print("="*60)
    print("Thiele Machine: Abductive Reasoning for Sudoku")
    print("="*60)
    print(f"Loading completed grid from: {grid_file}")
    
    completed_grid = load_completed_grid_from_file(grid_file)
    possible_clues = extract_possible_clues(completed_grid)
    
    print(f"Found {len(possible_clues)} possible clues")
    
    minimal_clues = find_minimal_clues(possible_clues, completed_grid)
    
    end_time = time.time()
    
    print(f"\nMinimal set of clues found: {len(minimal_clues)}")
    print("Clue positions:", sorted(minimal_clues))
    
    # Display the minimal puzzle
    minimal_grid = [['.' for _ in range(9)] for _ in range(9)]
    for r, c in minimal_clues:
        minimal_grid[r-1][c-1] = str(completed_grid[r][c])
    
    print("\nMinimal Sudoku puzzle:")
    for row in minimal_grid:
        print(" ".join(row))
    
    print(f"\nTotal Time: {end_time - start_time:.4f} seconds.")

if __name__ == "__main__":
    main()