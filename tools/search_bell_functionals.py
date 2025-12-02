#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Search Bell Functionals

Search for Bell functionals (linear combinations of probabilities) that:
- Maximize violation for a given box
- Distinguish between classes of boxes
- Have interesting algebraic structure

Usage:
    python search_bell_functionals.py --box artifacts/nl_search/box.json
    python search_bell_functionals.py --shape 2,2,2,2 --random
"""

import argparse
import hashlib
import json
import random
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
import numpy as np


@dataclass
class BellFunctional:
    """A Bell functional (linear combination of probabilities)."""
    coefficients: np.ndarray
    shape: Tuple[int, int, int, int]
    name: str = ""
    classical_bound: float = 0.0
    quantum_bound: float = 0.0
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def evaluate(self, P: np.ndarray) -> float:
        """Evaluate the functional on a probability distribution."""
        return np.sum(self.coefficients * P)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "coefficients": self.coefficients.tolist(),
            "shape": list(self.shape),
            "name": self.name,
            "classical_bound": self.classical_bound,
            "quantum_bound": self.quantum_bound,
            "metadata": self.metadata
        }
    
    @staticmethod
    def from_dict(d: Dict[str, Any]) -> 'BellFunctional':
        return BellFunctional(
            coefficients=np.array(d["coefficients"]),
            shape=tuple(d["shape"]),
            name=d.get("name", ""),
            classical_bound=d.get("classical_bound", 0.0),
            quantum_bound=d.get("quantum_bound", 0.0),
            metadata=d.get("metadata", {})
        )


def make_chsh_functional() -> BellFunctional:
    """Create the standard CHSH functional."""
    coefficients = np.zeros((2, 2, 2, 2))
    
    # CHSH = E(0,0) + E(0,1) + E(1,0) - E(1,1)
    # where E(x,y) = P(a=b|x,y) - P(a≠b|x,y)
    
    # E(x,y) = P(0,0|x,y) + P(1,1|x,y) - P(0,1|x,y) - P(1,0|x,y)
    for x in range(2):
        for y in range(2):
            sign = 1 if (x, y) != (1, 1) else -1
            coefficients[x, y, 0, 0] = sign
            coefficients[x, y, 1, 1] = sign
            coefficients[x, y, 0, 1] = -sign
            coefficients[x, y, 1, 0] = -sign
    
    return BellFunctional(
        coefficients=coefficients,
        shape=(2, 2, 2, 2),
        name="CHSH",
        classical_bound=2.0,
        quantum_bound=2.0 * np.sqrt(2)
    )


def make_random_functional(shape: Tuple[int, int, int, int], rng: random.Random) -> BellFunctional:
    """Create a random Bell functional."""
    X, Y, A, B = shape
    coefficients = np.array([[[[rng.uniform(-1, 1) for _ in range(B)]
                               for _ in range(A)]
                              for _ in range(Y)]
                             for _ in range(X)])
    
    # Normalize
    norm = np.linalg.norm(coefficients)
    if norm > 0:
        coefficients /= norm
    
    return BellFunctional(
        coefficients=coefficients,
        shape=shape,
        name=f"random_{hashlib.sha256(coefficients.tobytes()).hexdigest()[:8]}",
        classical_bound=0.0,  # Not computed
        quantum_bound=0.0     # Not computed
    )


def compute_classical_bound(functional: BellFunctional) -> float:
    """Compute the classical bound for a Bell functional.
    
    The classical bound is the maximum over all local deterministic strategies.
    """
    X, Y, A, B = functional.shape
    max_value = float('-inf')
    
    # Enumerate all deterministic strategies
    # Alice: a = f(x), Bob: b = g(y)
    for alice_strategy in range(A ** X):
        for bob_strategy in range(B ** Y):
            # Decode strategies
            alice_outputs = [(alice_strategy // (A ** x)) % A for x in range(X)]
            bob_outputs = [(bob_strategy // (B ** y)) % B for y in range(Y)]
            
            # Compute value
            value = 0.0
            for x in range(X):
                for y in range(Y):
                    a = alice_outputs[x]
                    b = bob_outputs[y]
                    value += functional.coefficients[x, y, a, b]
            
            max_value = max(max_value, value)
    
    return max_value


def search_maximizing_functional(box: np.ndarray, num_iterations: int = 100, rng: Optional[random.Random] = None) -> BellFunctional:
    """Search for a Bell functional that maximizes violation on a given box."""
    if rng is None:
        rng = random.Random(42)
    
    shape = box.shape
    best_functional = None
    best_violation = float('-inf')
    
    for _ in range(num_iterations):
        # Generate random functional
        functional = make_random_functional(shape, rng)
        
        # Evaluate on box
        value = functional.evaluate(box)
        
        # Compute classical bound
        classical_bound = compute_classical_bound(functional)
        functional.classical_bound = classical_bound
        
        # Compute violation
        violation = value - classical_bound
        
        if violation > best_violation:
            best_violation = violation
            best_functional = functional
            best_functional.metadata["box_value"] = value
            best_functional.metadata["violation"] = violation
    
    return best_functional


def search_discriminating_functional(box1: np.ndarray, box2: np.ndarray, 
                                     num_iterations: int = 100, 
                                     rng: Optional[random.Random] = None) -> BellFunctional:
    """Search for a Bell functional that best discriminates between two boxes."""
    if rng is None:
        rng = random.Random(42)
    
    assert box1.shape == box2.shape, "Boxes must have the same shape"
    shape = box1.shape
    
    best_functional = None
    best_discrimination = float('-inf')
    
    for _ in range(num_iterations):
        functional = make_random_functional(shape, rng)
        
        value1 = functional.evaluate(box1)
        value2 = functional.evaluate(box2)
        
        discrimination = abs(value1 - value2)
        
        if discrimination > best_discrimination:
            best_discrimination = discrimination
            best_functional = functional
            best_functional.metadata["box1_value"] = value1
            best_functional.metadata["box2_value"] = value2
            best_functional.metadata["discrimination"] = discrimination
    
    return best_functional


def main():
    parser = argparse.ArgumentParser(description="Search for Bell functionals")
    parser.add_argument(
        "--box",
        type=Path,
        default=None,
        help="Path to box JSON file"
    )
    parser.add_argument(
        "--shape",
        type=str,
        default="2,2,2,2",
        help="Box shape for random search"
    )
    parser.add_argument(
        "--random",
        action="store_true",
        help="Generate random functionals"
    )
    parser.add_argument(
        "--count",
        type=int,
        default=10,
        help="Number of functionals to generate"
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=42,
        help="Random seed"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Output path for functionals"
    )
    parser.add_argument(
        "--chsh",
        action="store_true",
        help="Output the standard CHSH functional"
    )
    
    args = parser.parse_args()
    
    rng = random.Random(args.seed)
    shape = tuple(map(int, args.shape.split(",")))
    
    functionals = []
    
    if args.chsh:
        print("CHSH Functional:")
        chsh = make_chsh_functional()
        print(f"  Classical bound: {chsh.classical_bound}")
        print(f"  Quantum bound: {chsh.quantum_bound:.4f}")
        functionals.append(chsh)
    
    if args.box:
        if not args.box.exists():
            print(f"Error: Box file not found: {args.box}")
            return 1
        
        with open(args.box, 'r', encoding='utf-8') as f:
            box_data = json.load(f)
        
        box = np.array(box_data.get("probs", []))
        if box.size == 0:
            print("Error: No probability data in box file")
            return 1
        
        print(f"\nSearching for maximizing functional on box...")
        functional = search_maximizing_functional(box, num_iterations=args.count * 10, rng=rng)
        
        print(f"  Best functional: {functional.name}")
        print(f"  Classical bound: {functional.classical_bound:.4f}")
        print(f"  Box value: {functional.metadata.get('box_value', 0):.4f}")
        print(f"  Violation: {functional.metadata.get('violation', 0):.4f}")
        
        functionals.append(functional)
    
    if args.random:
        print(f"\nGenerating {args.count} random functionals for shape {shape}...")
        for i in range(args.count):
            functional = make_random_functional(shape, rng)
            functional.classical_bound = compute_classical_bound(functional)
            functional.metadata["index"] = i
            functionals.append(functional)
            print(f"  {functional.name}: classical_bound={functional.classical_bound:.4f}")
    
    if args.output and functionals:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        output_data = {
            "functionals": [f.to_dict() for f in functionals]
        }
        args.output.write_text(json.dumps(output_data, indent=2), encoding='utf-8')
        print(f"\nFunctionals saved to: {args.output}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
