#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Nonlocal Box Search

Systematic search for nonlocal boxes with interesting properties:
- Extremal boxes (vertices of the NS polytope)
- Super-quantum boxes (violate Tsirelson bound)
- Structured boxes (exhibit specific symmetries)

Usage:
    python nonlocal_box_search.py --shape 2,2,2,2 --method random --count 100
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
class SearchConfig:
    """Configuration for nonlocal box search."""
    shape: Tuple[int, int, int, int] = (2, 2, 2, 2)
    method: str = "random"
    count: int = 100
    seed: int = 42
    output_dir: Path = Path("artifacts/nl_search")
    filter_extremal: bool = True
    filter_superquantum: bool = False
    min_bell_value: float = 2.0  # Classical bound


@dataclass
class BoxCandidate:
    """A candidate nonlocal box."""
    probs: np.ndarray
    shape: Tuple[int, int, int, int]
    bell_value: float = 0.0
    canonical_hash: str = ""
    is_extremal: bool = False
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "probs": self.probs.tolist(),
            "shape": list(self.shape),
            "bell_value": self.bell_value,
            "canonical_hash": self.canonical_hash,
            "is_extremal": self.is_extremal,
            "metadata": self.metadata
        }


def generate_random_ns_box(shape: Tuple[int, int, int, int], rng: random.Random) -> np.ndarray:
    """Generate a random NS (no-signaling) box."""
    X, Y, A, B = shape
    
    # Start with random positive values
    P = np.zeros((X, Y, A, B))
    for x in range(X):
        for y in range(Y):
            # Random distribution over outputs
            vals = np.array([rng.random() for _ in range(A * B)])
            vals = vals / vals.sum()  # Normalize
            P[x, y] = vals.reshape(A, B)
    
    return P


def project_to_ns(P: np.ndarray) -> np.ndarray:
    """Project a box onto the NS polytope."""
    X, Y, A, B = P.shape
    
    # Ensure non-negativity
    P = np.maximum(P, 0)
    
    # Normalize each (x,y) slice
    for x in range(X):
        for y in range(Y):
            total = P[x, y].sum()
            if total > 0:
                P[x, y] /= total
    
    # NS constraints: marginals should be consistent
    # For each x: sum_b P(a,b|x,y) should be independent of y
    # For each y: sum_a P(a,b|x,y) should be independent of x
    
    # Simple averaging to enforce NS approximately
    for _ in range(10):  # Iterate to converge
        # Alice marginals
        for x in range(X):
            alice_marginal = np.zeros(A)
            for y in range(Y):
                alice_marginal += P[x, y].sum(axis=1)
            alice_marginal /= Y
            for y in range(Y):
                current = P[x, y].sum(axis=1)
                if np.any(current > 0):
                    scale = alice_marginal / np.maximum(current, 1e-10)
                    P[x, y] *= scale.reshape(-1, 1)
        
        # Bob marginals
        for y in range(Y):
            bob_marginal = np.zeros(B)
            for x in range(X):
                bob_marginal += P[x, y].sum(axis=0)
            bob_marginal /= X
            for x in range(X):
                current = P[x, y].sum(axis=0)
                if np.any(current > 0):
                    scale = bob_marginal / np.maximum(current, 1e-10)
                    P[x, y] *= scale
        
        # Re-normalize
        for x in range(X):
            for y in range(Y):
                total = P[x, y].sum()
                if total > 0:
                    P[x, y] /= total
    
    return P


def compute_chsh_value(P: np.ndarray) -> float:
    """Compute the CHSH value for a 2x2x2x2 box."""
    if P.shape != (2, 2, 2, 2):
        return 0.0
    
    # CHSH: E(0,0) + E(0,1) + E(1,0) - E(1,1)
    # where E(x,y) = P(a=b|x,y) - P(a≠b|x,y)
    
    def expectation(x, y):
        return (P[x, y, 0, 0] + P[x, y, 1, 1] - P[x, y, 0, 1] - P[x, y, 1, 0])
    
    return expectation(0, 0) + expectation(0, 1) + expectation(1, 0) - expectation(1, 1)


def compute_canonical_hash(P: np.ndarray) -> str:
    """Compute a canonical hash for a box."""
    # Round to avoid floating point issues
    P_rounded = np.round(P, decimals=8)
    data = P_rounded.tobytes()
    return hashlib.sha256(data).hexdigest()[:16]


def check_extremality_heuristic(P: np.ndarray) -> bool:
    """Heuristic check if a box might be extremal."""
    # Count near-zero entries
    near_zero = np.sum(np.abs(P) < 1e-8)
    total = P.size
    
    # Extremal boxes typically have many zeros
    return near_zero / total > 0.3


def search_random(config: SearchConfig) -> List[BoxCandidate]:
    """Random search for nonlocal boxes."""
    rng = random.Random(config.seed)
    candidates = []
    
    for i in range(config.count):
        # Generate random NS box
        P = generate_random_ns_box(config.shape, rng)
        P = project_to_ns(P)
        
        # Compute properties
        bell_value = compute_chsh_value(P) if config.shape == (2, 2, 2, 2) else 0.0
        canonical_hash = compute_canonical_hash(P)
        is_extremal = check_extremality_heuristic(P)
        
        # Filter
        if config.filter_extremal and not is_extremal:
            continue
        if config.filter_superquantum and bell_value <= 2 * np.sqrt(2):
            continue
        if bell_value < config.min_bell_value:
            continue
        
        candidate = BoxCandidate(
            probs=P,
            shape=config.shape,
            bell_value=bell_value,
            canonical_hash=canonical_hash,
            is_extremal=is_extremal,
            metadata={"method": "random", "iteration": i}
        )
        candidates.append(candidate)
    
    return candidates


def search_perturbation(config: SearchConfig, base_box: Optional[np.ndarray] = None) -> List[BoxCandidate]:
    """Search by perturbing a base box."""
    rng = random.Random(config.seed)
    candidates = []
    
    if base_box is None:
        # Start from PR box if 2x2x2x2
        if config.shape == (2, 2, 2, 2):
            base_box = np.zeros((2, 2, 2, 2))
            # PR box: P(a⊕b=xy) = 1/2
            for x in range(2):
                for y in range(2):
                    for a in range(2):
                        for b in range(2):
                            if (a ^ b) == (x * y):
                                base_box[x, y, a, b] = 0.5
        else:
            base_box = generate_random_ns_box(config.shape, rng)
            base_box = project_to_ns(base_box)
    
    for i in range(config.count):
        # Perturb
        perturbation = np.array([[[[rng.gauss(0, 0.1) for _ in range(config.shape[3])]
                                   for _ in range(config.shape[2])]
                                  for _ in range(config.shape[1])]
                                 for _ in range(config.shape[0])])
        P = base_box + perturbation
        P = project_to_ns(P)
        
        # Compute properties
        bell_value = compute_chsh_value(P) if config.shape == (2, 2, 2, 2) else 0.0
        canonical_hash = compute_canonical_hash(P)
        is_extremal = check_extremality_heuristic(P)
        
        # Filter
        if config.filter_extremal and not is_extremal:
            continue
        if bell_value < config.min_bell_value:
            continue
        
        candidate = BoxCandidate(
            probs=P,
            shape=config.shape,
            bell_value=bell_value,
            canonical_hash=canonical_hash,
            is_extremal=is_extremal,
            metadata={"method": "perturbation", "iteration": i}
        )
        candidates.append(candidate)
    
    return candidates


def run_search(config: SearchConfig) -> List[BoxCandidate]:
    """Run the search with the given configuration."""
    if config.method == "random":
        return search_random(config)
    elif config.method == "perturbation":
        return search_perturbation(config)
    else:
        print(f"Unknown search method: {config.method}")
        return []


def save_results(candidates: List[BoxCandidate], output_dir: Path):
    """Save search results to output directory."""
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Save summary
    summary = {
        "total_candidates": len(candidates),
        "candidates": [
            {
                "hash": c.canonical_hash,
                "bell_value": float(c.bell_value),
                "is_extremal": bool(c.is_extremal)
            }
            for c in candidates
        ]
    }
    
    summary_path = output_dir / "search_results.json"
    summary_path.write_text(json.dumps(summary, indent=2), encoding='utf-8')
    
    # Save individual boxes
    for i, candidate in enumerate(candidates):
        box_dict = candidate.to_dict()
        # Ensure JSON serializability
        box_dict['bell_value'] = float(box_dict['bell_value'])
        box_dict['is_extremal'] = bool(box_dict['is_extremal'])
        box_path = output_dir / f"box_{i:04d}_{candidate.canonical_hash}.json"
        box_path.write_text(json.dumps(box_dict, indent=2), encoding='utf-8')
    
    return summary_path


def main():
    parser = argparse.ArgumentParser(description="Search for nonlocal boxes")
    parser.add_argument(
        "--shape",
        type=str,
        default="2,2,2,2",
        help="Box shape as X,Y,A,B"
    )
    parser.add_argument(
        "--method",
        type=str,
        choices=["random", "perturbation"],
        default="random",
        help="Search method"
    )
    parser.add_argument(
        "--count",
        type=int,
        default=100,
        help="Number of boxes to generate"
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
        default=Path("artifacts/nl_search"),
        help="Output directory"
    )
    parser.add_argument(
        "--min-bell",
        type=float,
        default=2.0,
        help="Minimum Bell value to keep"
    )
    parser.add_argument(
        "--no-filter-extremal",
        action="store_true",
        help="Don't filter for extremal boxes"
    )
    
    args = parser.parse_args()
    
    shape = tuple(map(int, args.shape.split(",")))
    if len(shape) != 4:
        parser.error("Shape must have exactly 4 components")
    
    config = SearchConfig(
        shape=shape,
        method=args.method,
        count=args.count,
        seed=args.seed,
        output_dir=args.output,
        filter_extremal=not args.no_filter_extremal,
        min_bell_value=args.min_bell
    )
    
    print(f"Searching for nonlocal boxes...")
    print(f"  Shape: {config.shape}")
    print(f"  Method: {config.method}")
    print(f"  Count: {config.count}")
    print(f"  Seed: {config.seed}")
    
    candidates = run_search(config)
    
    print(f"\nFound {len(candidates)} candidates")
    
    if candidates:
        summary_path = save_results(candidates, config.output_dir)
        print(f"Results saved to: {summary_path}")
        
        # Show top candidates
        sorted_candidates = sorted(candidates, key=lambda c: c.bell_value, reverse=True)
        print("\nTop candidates by Bell value:")
        for c in sorted_candidates[:5]:
            print(f"  {c.canonical_hash}: Bell={c.bell_value:.4f}, extremal={c.is_extremal}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
