#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Compute Classical Bound

Computes the exact classical (local deterministic) bound for a Bell functional
by enumerating all deterministic strategies.

For shape (X, Y, A, B):
- Alice has A^X deterministic strategies (one output per input)
- Bob has B^Y deterministic strategies
- Total: A^X * B^Y joint strategies

Usage:
    python tools/compute_classical_bound.py --functional artifacts/functional.json
    python tools/compute_classical_bound.py --shape 2,2,2,2 --chsh
"""

import argparse
import json
import sys
from itertools import product
from pathlib import Path
from typing import Tuple

import numpy as np

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from tools.search_bell_functionals import BellFunctional, make_chsh_functional


def enumerate_deterministic_strategies(X: int, A: int) -> list:
    """
    Enumerate all deterministic strategies for one party.
    
    Args:
        X: Number of inputs
        A: Number of outputs
    
    Returns:
        List of strategies, each is a tuple of length X with values in range(A)
    """
    return list(product(range(A), repeat=X))


def make_deterministic_box(
    alice_strategy: Tuple[int, ...],
    bob_strategy: Tuple[int, ...],
    shape: Tuple[int, int, int, int]
) -> np.ndarray:
    """
    Create a deterministic (local) box from two strategies.
    
    Args:
        alice_strategy: Tuple of Alice's outputs for each input
        bob_strategy: Tuple of Bob's outputs for each input
        shape: (X, Y, A, B)
    
    Returns:
        Probability distribution P(a,b|x,y) where P = 1 for deterministic outcomes, 0 otherwise
    """
    X, Y, A, B = shape
    P = np.zeros((X, Y, A, B))
    
    for x in range(X):
        for y in range(Y):
            a = alice_strategy[x]
            b = bob_strategy[y]
            P[x, y, a, b] = 1.0
    
    return P


def compute_classical_bound_exact(functional: BellFunctional) -> Tuple[float, np.ndarray]:
    """
    Compute exact classical bound by enumerating all deterministic strategies.
    
    Args:
        functional: Bell functional to evaluate
    
    Returns:
        (max_value, optimal_box) tuple
    """
    X, Y, A, B = functional.shape
    
    alice_strategies = enumerate_deterministic_strategies(X, A)
    bob_strategies = enumerate_deterministic_strategies(Y, B)
    
    max_value = -np.inf
    optimal_box = None
    
    total_strategies = len(alice_strategies) * len(bob_strategies)
    
    for alice_strat in alice_strategies:
        for bob_strat in bob_strategies:
            P = make_deterministic_box(alice_strat, bob_strat, functional.shape)
            value = functional.evaluate(P)
            
            if value > max_value:
                max_value = value
                optimal_box = P
    
    return max_value, optimal_box


def main():
    parser = argparse.ArgumentParser(description="Compute classical bound for Bell functional")
    parser.add_argument("--functional", help="Path to functional JSON file")
    parser.add_argument("--shape", help="Shape as X,Y,A,B (e.g., 2,2,2,2)")
    parser.add_argument("--chsh", action="store_true", help="Use CHSH functional")
    parser.add_argument("--output", help="Output file for optimal box")
    parser.add_argument("--verbose", action="store_true", help="Verbose output")
    args = parser.parse_args()
    
    # Load or create functional
    if args.functional:
        with open(args.functional, 'r') as f:
            data = json.load(f)
        functional = BellFunctional.from_dict(data)
    elif args.chsh:
        functional = make_chsh_functional()
    elif args.shape:
        shape_parts = [int(x.strip()) for x in args.shape.split(',')]
        if len(shape_parts) != 4:
            print("ERROR: Shape must have 4 components (X,Y,A,B)")
            sys.exit(1)
        functional = make_chsh_functional()  # Default to CHSH
    else:
        print("ERROR: Must specify --functional, --chsh, or --shape")
        sys.exit(1)
    
    if args.verbose:
        print(f"Computing classical bound for functional: {functional.name}")
        print(f"  Shape: {functional.shape}")
        X, Y, A, B = functional.shape
        alice_count = A ** X
        bob_count = B ** Y
        total = alice_count * bob_count
        print(f"  Alice strategies: {alice_count}")
        print(f"  Bob strategies: {bob_count}")
        print(f"  Total strategies: {total}")
    
    # Compute bound
    max_value, optimal_box = compute_classical_bound_exact(functional)
    
    print(f"\nClassical Bound (exact): {max_value:.10f}")
    
    if args.verbose:
        print(f"\nOptimal deterministic box:")
        X, Y, A, B = functional.shape
        for x in range(X):
            for y in range(Y):
                outcomes = [(a, b, optimal_box[x, y, a, b]) 
                           for a in range(A) for b in range(B) 
                           if optimal_box[x, y, a, b] > 0]
                print(f"  P(a,b|{x},{y}): {outcomes}")
    
    # Save optimal box if requested
    if args.output:
        output_data = {
            "shape": list(functional.shape),
            "functional_name": functional.name,
            "classical_bound": float(max_value),
            "optimal_box": optimal_box.tolist()
        }
        with open(args.output, 'w') as f:
            json.dump(output_data, f, indent=2)
        print(f"\nOptimal box saved to: {args.output}")


if __name__ == "__main__":
    main()
