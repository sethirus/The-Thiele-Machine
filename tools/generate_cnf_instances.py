#!/usr/bin/env python3
"""
CNF Test Instance Generator - B1.3 Support
===========================================

Generate structured CNF instances for testing H2 hypothesis.

TYPES:
    1. Modular - Multiple independent components
    2. Chain - Linear dependency chain
    3. Tree - Hierarchical structure
    4. Random - No structure (negative control)

USAGE:
    python tools/generate_cnf_instances.py --type modular --vars 50 --modules 5
    python tools/generate_cnf_instances.py --type random --vars 50
"""

import argparse
import random
from pathlib import Path
from typing import List, Tuple, Set


def generate_modular_cnf(num_vars: int, num_modules: int, clauses_per_var: int = 4) -> Tuple[int, List[List[int]]]:
    """
    Generate modular CNF with independent modules.
    Each module has internal structure but no inter-module dependencies.
    
    This should show H2 advantage: partition discovery finds modules,
    solving is parallelizable.
    """
    vars_per_module = num_vars // num_modules
    clauses = []
    
    for module_id in range(num_modules):
        start_var = module_id * vars_per_module + 1
        end_var = start_var + vars_per_module
        
        # Create clauses within this module
        module_vars = list(range(start_var, end_var))
        
        # Add some XOR-like constraints within module
        for _ in range(len(module_vars) * clauses_per_var):
            # Pick 3 random variables from this module
            if len(module_vars) >= 3:
                v1, v2, v3 = random.sample(module_vars, 3)
                # XOR constraint: (v1 v2 v3) (v1 v2 -v3) (v1 -v2 v3) (-v1 v2 v3)
                clauses.append([v1, v2, v3])
                clauses.append([v1, v2, -v3])
                clauses.append([v1, -v2, v3])
                clauses.append([-v1, v2, v3])
    
    return num_vars, clauses


def generate_chain_cnf(num_vars: int, chain_length: int = 3) -> Tuple[int, List[List[int]]]:
    """
    Generate chain CNF with linear dependencies.
    Variables form a chain: x1 -> x2 -> x3 -> ...
    
    This should show moderate H2 advantage.
    """
    clauses = []
    
    # Create chain constraints
    for i in range(1, num_vars):
        # x_i -> x_{i+1}
        clauses.append([-i, i+1])
        # Add some additional constraints for each variable
        clauses.append([i, i+1])
        if i > 1:
            clauses.append([-i, -i+1, i-1])
    
    return num_vars, clauses


def generate_tree_cnf(num_vars: int, branching: int = 2) -> Tuple[int, List[List[int]]]:
    """
    Generate tree-structured CNF.
    Variables form a tree with given branching factor.
    
    This should show H2 advantage with hierarchical partitioning.
    """
    clauses = []
    
    # Build tree structure
    for parent in range(1, num_vars):
        for child_offset in range(1, branching + 1):
            child = parent * branching + child_offset
            if child <= num_vars:
                # Parent -> Child constraint
                clauses.append([-parent, child])
                clauses.append([parent, -child])
                # Add some additional clauses
                if child + 1 <= num_vars:
                    clauses.append([child, child + 1])
    
    return num_vars, clauses


def generate_random_cnf(num_vars: int, clauses_per_var: int = 4, clause_size: int = 3) -> Tuple[int, List[List[int]]]:
    """
    Generate random 3-SAT CNF with no structure.
    
    This is the negative control: should show NO H2 advantage.
    """
    num_clauses = num_vars * clauses_per_var
    clauses = []
    
    for _ in range(num_clauses):
        # Pick random variables
        vars_in_clause = random.sample(range(1, num_vars + 1), min(clause_size, num_vars))
        # Random polarities
        clause = [v if random.random() > 0.5 else -v for v in vars_in_clause]
        clauses.append(clause)
    
    return num_vars, clauses


def write_dimacs(filepath: Path, num_vars: int, clauses: List[List[int]], comment: str = ""):
    """Write CNF in DIMACS format."""
    with open(filepath, 'w') as f:
        if comment:
            f.write(f"c {comment}\n")
        f.write(f"c Generated CNF instance\n")
        f.write(f"p cnf {num_vars} {len(clauses)}\n")
        for clause in clauses:
            f.write(" ".join(map(str, clause)) + " 0\n")


def main():
    parser = argparse.ArgumentParser(description="Generate structured CNF test instances")
    parser.add_argument('--type', choices=['modular', 'chain', 'tree', 'random'], 
                       required=True, help='Type of CNF instance')
    parser.add_argument('--vars', type=int, required=True, help='Number of variables')
    parser.add_argument('--modules', type=int, default=5, help='Number of modules (for modular)')
    parser.add_argument('--output', type=Path, required=True, help='Output .cnf file')
    parser.add_argument('--seed', type=int, default=42, help='Random seed')
    
    args = parser.parse_args()
    random.seed(args.seed)
    
    # Generate CNF based on type
    if args.type == 'modular':
        num_vars, clauses = generate_modular_cnf(args.vars, args.modules)
        comment = f"Modular CNF with {args.modules} modules"
    elif args.type == 'chain':
        num_vars, clauses = generate_chain_cnf(args.vars)
        comment = "Chain-structured CNF"
    elif args.type == 'tree':
        num_vars, clauses = generate_tree_cnf(args.vars)
        comment = "Tree-structured CNF"
    elif args.type == 'random':
        num_vars, clauses = generate_random_cnf(args.vars)
        comment = "Random 3-SAT CNF (no structure)"
    
    # Ensure output directory exists
    args.output.parent.mkdir(parents=True, exist_ok=True)
    
    # Write to file
    write_dimacs(args.output, num_vars, clauses, comment)
    print(f"Generated {args.type} CNF: {args.output}")
    print(f"  Variables: {num_vars}")
    print(f"  Clauses: {len(clauses)}")


if __name__ == '__main__':
    main()
