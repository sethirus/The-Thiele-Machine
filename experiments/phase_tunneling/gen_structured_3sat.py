#!/usr/bin/env python3
"""
Structured 3-SAT Generator

Generates 3-SAT instances with hidden separator structure for Thiele VM experiments.
Creates two dense clusters connected by a small separator set.
"""

import random
import sys
from typing import List, Tuple, Dict, Any

def generate_structured_3sat(n_total: int, s_size: int, alpha_local: float, seed: int, ensure_sat: bool = False) -> Tuple[str, Dict[str, Any]]:
    """
    Generate a structured 3-SAT instance with separator

    Args:
        n_total: Total number of variables
        s_size: Size of separator set
        alpha_local: Local clause density within clusters
        seed: Random seed
        ensure_sat: Whether to ensure the instance is satisfiable

    Returns:
        Tuple of (DIMACS string, metadata dict)
    """
    random.seed(seed)

    # Calculate cluster sizes
    n_per_cluster = (n_total - s_size) // 2
    cluster_a_vars = list(range(1, n_per_cluster + 1))
    cluster_b_vars = list(range(n_per_cluster + 1, 2 * n_per_cluster + 1))
    separator_vars = list(range(2 * n_per_cluster + 1, 2 * n_per_cluster + s_size + 1))

    # Generate clauses within clusters
    clauses = []

    # Cluster A clauses
    n_clauses_a = int(alpha_local * n_per_cluster)
    for _ in range(n_clauses_a):
        clause = generate_random_clause(cluster_a_vars, 3)
        clauses.append(clause)

    # Cluster B clauses
    n_clauses_b = int(alpha_local * n_per_cluster)
    for _ in range(n_clauses_b):
        clause = generate_random_clause(cluster_b_vars, 3)
        clauses.append(clause)

    # Separator clauses (connect clusters)
    for _ in range(s_size):
        # Create clauses that involve both clusters via separator
        clause = []
        # Pick one var from each cluster and one from separator
        a_var = random.choice(cluster_a_vars)
        b_var = random.choice(cluster_b_vars)
        s_var = random.choice(separator_vars)

        # Random signs
        clause = [
            a_var * random.choice([1, -1]),
            b_var * random.choice([1, -1]),
            s_var * random.choice([1, -1])
        ]
        clauses.append(clause)

    # Shuffle variable IDs to hide structure
    var_mapping = list(range(1, n_total + 1))
    random.shuffle(var_mapping)
    var_mapping = {old: new for old, new in enumerate(var_mapping, 1)}

    # Apply mapping to clauses
    shuffled_clauses = []
    for clause in clauses:
        new_clause = []
        for lit in clause:
            var = abs(lit)
            sign = 1 if lit > 0 else -1
            new_var = var_mapping[var]
            new_clause.append(new_var * sign)
        shuffled_clauses.append(new_clause)

    # Generate DIMACS
    n_clauses_total = len(shuffled_clauses)
    dimacs_lines = [f"p cnf {n_total} {n_clauses_total}"]
    for clause in shuffled_clauses:
        dimacs_lines.append(" ".join(map(str, clause)) + " 0")

    dimacs = "\n".join(dimacs_lines)

    # Metadata for validation
    metadata = {
        "n_total": n_total,
        "s_size": s_size,
        "n_per_cluster": n_per_cluster,
        "cluster_a_original": cluster_a_vars,
        "cluster_b_original": cluster_b_vars,
        "separator_original": separator_vars,
        "var_mapping": var_mapping,
        "alpha_local": alpha_local,
        "n_clauses_a": n_clauses_a,
        "n_clauses_b": n_clauses_b,
        "n_separator_clauses": s_size
    }

    return dimacs, metadata

def generate_random_clause(vars_pool: List[int], width: int) -> List[int]:
    """Generate a random clause from variable pool"""
    selected_vars = random.sample(vars_pool, width)
    clause = []
    for var in selected_vars:
        sign = random.choice([1, -1])
        clause.append(var * sign)
    return clause

def main():
    """Command line interface"""
    if len(sys.argv) != 4:
        print("Usage: python gen_structured_3sat.py <n_total> <alpha> <seed>")
        sys.exit(1)

    n_total = int(sys.argv[1])
    alpha = float(sys.argv[2])
    seed = int(sys.argv[3])

    # For structured instances, use fixed separator size and derive local alpha
    s_size = max(2, n_total // 20)  # Small separator
    alpha_local = alpha * 0.8  # Slightly lower local density

    dimacs, metadata = generate_structured_3sat(n_total, s_size, alpha_local, seed)

    # Save to file
    filename = f"structured_{n_total}_{alpha}_{seed}.cnf"
    with open(filename, 'w') as f:
        f.write(dimacs)

    # Save metadata
    metadata_filename = f"structured_{n_total}_{alpha}_{seed}_metadata.json"
    import json
    with open(metadata_filename, 'w') as f:
        json.dump(metadata, f, indent=2)

    print(f"Generated: {filename}")
    print(f"Variables: {n_total}")
    print(f"Clauses: {len(dimacs.split('p cnf')[1].split('0\n')) - 1}")
    print(f"Separator size: {s_size}")
    print(f"Local alpha: {alpha_local:.2f}")
    print(f"Metadata: {metadata_filename}")

if __name__ == "__main__":
    main()