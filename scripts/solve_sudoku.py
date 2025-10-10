# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import time
from scripts.sudoku_cnf_provider import SudokuCnfProvider
from thielecpu.vm import VM
from thielecpu.state import State
import ast

# The "World's Hardest Sudoku"
puzzle_string = "800000000003600000070090200050007000000045700000100030001000068008500010090000400"

def print_solution(model, prov):
    # A function to beautifully print the final 9x9 grid
    board = [['.' for _ in range(9)] for _ in range(9)]
    if model:
        pos = {v for v in model if v > 0}
        for r in range(1, 10):
            for c in range(1, 10):
                for d in range(1, 10):
                    if prov.get_var(r, c, d) in pos:
                        board[r-1][c-1] = str(d)
    
    for row in board:
        print(" ".join(row))

start_time = time.time()

print("="*40)
print("Thiele Machine vs. The World's Hardest Sudoku")
print("="*40)

provider = SudokuCnfProvider(puzzle_string)

print("Loading puzzle and rules into the engine...")
# Solve using the virtual machine
clauses = provider.get_all_clauses()
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
            solution_model = ast.literal_eval(line)
            break
else:
    solution_model = None

end_time = time.time()

if solution_model:
    print("\n>>> DEDUCTIVE COLLAPSE COMPLETE. SOLUTION FOUND. <<<")
    print(f"Total Time: {end_time - start_time:.4f} seconds.\n")
    print_solution(solution_model, provider)
else:
    print("\n>>> MISSION FAILED. NO SOLUTION FOUND. <<<")