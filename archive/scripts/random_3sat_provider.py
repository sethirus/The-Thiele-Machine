# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import random

def generate_random_3sat(n, alpha=4.2):
    """
    Generate random 3-SAT instance with n variables, at phase transition (alpha ≈ 4.2).
    """
    num_clauses = int(alpha * n)
    clauses = []
    for _ in range(num_clauses):
        vars = random.sample(range(1, n+1), 3)
        signs = [random.choice([1, -1]) for _ in range(3)]
        clause = [sign * var for sign, var in zip(signs, vars)]
        clauses.append(clause)
    return clauses

if __name__ == "__main__":
    n = 50
    clauses = generate_random_3sat(n)
    print(f"Random 3-SAT for n={n}: {len(clauses)} clauses")