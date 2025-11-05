# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
SAT Solver for CNF benchmarks
Uses pysat library to solve SAT problems from CNF files
"""

import sys
import time
from pysat.solvers import Glucose4
from pysat.formula import CNF

def solve_cnf(filename):
    """Solve a CNF SAT problem from file"""

    print(f"Loading CNF file: {filename}")

    # Load the CNF formula
    cnf = CNF(from_file=filename)

    print(f"Problem statistics:")
    print(f"  Variables: {cnf.nv}")
    print(f"  Clauses: {len(cnf.clauses)}")

    # Create solver
    solver = Glucose4()

    # Add all clauses
    for clause in cnf.clauses:
        solver.add_clause(clause)

    print("Solving...")

    start_time = time.time()
    result = solver.solve()
    solve_time = time.time() - start_time

    if result:
        print("✅ SATISFIABLE")
        model = solver.get_model()
        print(f"Found satisfying assignment with {len(model)} variables")
        print(".2f")
    else:
        print("❌ UNSATISFIABLE")
        print(".2f")

    solver.delete()

    return result

def main():
    if len(sys.argv) != 2:
        print("Usage: python solve_cnf.py <cnf_file>")
        sys.exit(1)

    cnf_file = sys.argv[1]

    try:
        result = solve_cnf(cnf_file)
        sys.exit(0 if result else 1)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()