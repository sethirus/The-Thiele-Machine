#!/usr/bin/env python3
"""
Random 3-SAT Generator

Generates random 3-SAT instances for baseline experiments.
"""

import random
import sys
from typing import List

def generate_random_3sat(n_vars: int, alpha: float, seed: int) -> str:
    """
    Generate a random 3-SAT instance

    Args:
        n_vars: Number of variables
        alpha: Clause-to-variable ratio
        seed: Random seed

    Returns:
        DIMACS CNF string
    """
    random.seed(seed)

    # Calculate number of clauses
    n_clauses = int(alpha * n_vars)

    clauses = []
    for _ in range(n_clauses):
        # Generate random 3-literal clause
        literals = []
        vars_used = set()

        while len(literals) < 3:
            var = random.randint(1, n_vars)
            if var not in vars_used:
                vars_used.add(var)
                sign = random.choice([1, -1])
                literals.append(var * sign)

        clauses.append(literals)

    # Generate DIMACS format
    dimacs_lines = [f"p cnf {n_vars} {n_clauses}"]
    for clause in clauses:
        dimacs_lines.append(" ".join(map(str, clause)) + " 0")

    return "\n".join(dimacs_lines)

def main():
    """Command line interface"""
    if len(sys.argv) != 4:
        print("Usage: python gen_random_3sat.py <n_vars> <alpha> <seed>")
        sys.exit(1)

    n_vars = int(sys.argv[1])
    alpha = float(sys.argv[2])
    seed = int(sys.argv[3])

    dimacs = generate_random_3sat(n_vars, alpha, seed)

    # Save to file
    filename = f"random_{n_vars}_{alpha}_{seed}.cnf"
    with open(filename, 'w') as f:
        f.write(dimacs)

    print(f"Generated: {filename}")
    print(f"Variables: {n_vars}")
    print(f"Clauses: {int(alpha * n_vars)}")
    print(f"Ratio: {alpha}")

if __name__ == "__main__":
    main()