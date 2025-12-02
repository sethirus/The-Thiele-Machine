#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Classify Box Against Known

Classify a candidate box against known extremal boxes and structures:
- PR box and generalizations
- Tsirelson box (quantum optimal)
- Local deterministic boxes
- Known extremal vertices

Usage:
    python classify_box_against_known.py --box artifacts/nl_search/box.json
"""

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
import numpy as np


@dataclass
class KnownBox:
    """A known reference box."""
    name: str
    probs: np.ndarray
    category: str  # "local", "quantum", "superquantum", "extremal"
    bell_value: float
    description: str = ""


def make_pr_box() -> KnownBox:
    """Create the PR (Popescu-Rohrlich) box."""
    P = np.zeros((2, 2, 2, 2))
    for x in range(2):
        for y in range(2):
            for a in range(2):
                for b in range(2):
                    if (a ^ b) == (x * y):
                        P[x, y, a, b] = 0.5
    
    return KnownBox(
        name="PR Box",
        probs=P,
        category="superquantum",
        bell_value=4.0,
        description="Maximally nonlocal NS box, CHSH=4"
    )


def make_tsirelson_box() -> KnownBox:
    """Create the Tsirelson box (quantum optimal)."""
    # Quantum optimal state: |ψ⟩ = (|00⟩ + |11⟩)/√2
    # With optimal measurements
    
    cos_pi_8 = np.cos(np.pi / 8)
    sin_pi_8 = np.sin(np.pi / 8)
    
    P = np.zeros((2, 2, 2, 2))
    
    # P(a,b|x,y) for Tsirelson measurements
    for x in range(2):
        for y in range(2):
            # Alice angle: θ_x = x * π/4
            # Bob angle: φ_y = (2y-1) * π/8
            for a in range(2):
                for b in range(2):
                    # Probability from quantum mechanics
                    # This is a simplified approximation
                    theta_diff = (x * np.pi/4) - ((2*y - 1) * np.pi/8)
                    if a == b:
                        P[x, y, a, b] = 0.5 * np.cos(theta_diff/2)**2
                    else:
                        P[x, y, a, b] = 0.5 * np.sin(theta_diff/2)**2
    
    # Normalize each slice
    for x in range(2):
        for y in range(2):
            total = P[x, y].sum()
            if total > 0:
                P[x, y] /= total
    
    return KnownBox(
        name="Tsirelson Box",
        probs=P,
        category="quantum",
        bell_value=2.0 * np.sqrt(2),
        description="Quantum optimal for CHSH"
    )


def make_classical_box(alice_strategy: List[int], bob_strategy: List[int]) -> KnownBox:
    """Create a local deterministic box."""
    X, Y = len(alice_strategy), len(bob_strategy)
    A = max(alice_strategy) + 1
    B = max(bob_strategy) + 1
    
    P = np.zeros((X, Y, A, B))
    for x in range(X):
        for y in range(Y):
            a = alice_strategy[x]
            b = bob_strategy[y]
            P[x, y, a, b] = 1.0
    
    # Compute CHSH value
    bell_value = 0.0
    if (X, Y, A, B) == (2, 2, 2, 2):
        for x in range(2):
            for y in range(2):
                sign = 1 if (x, y) != (1, 1) else -1
                a = alice_strategy[x]
                b = bob_strategy[y]
                if a == b:
                    bell_value += sign
                else:
                    bell_value -= sign
    
    strategy_name = f"Alice={alice_strategy}, Bob={bob_strategy}"
    return KnownBox(
        name=f"Local({strategy_name})",
        probs=P,
        category="local",
        bell_value=bell_value,
        description=f"Local deterministic: {strategy_name}"
    )


def make_pr_lift_3x3() -> KnownBox:
    """Create a PR-lift to 3x3x2x2 scenario.
    
    This lifts the 2x2 PR box to a 3x3 scenario by embedding
    it in a sub-block and extending with uniform distributions.
    """
    P = np.zeros((3, 3, 2, 2))
    
    # Embed 2x2 PR box in upper-left corner
    for x in range(2):
        for y in range(2):
            for a in range(2):
                for b in range(2):
                    if (a ^ b) == (x * y):
                        P[x, y, a, b] = 0.5
    
    # Fill remaining cells with uniform distribution
    for x in range(3):
        for y in range(3):
            if x >= 2 or y >= 2:
                P[x, y, :, :] = 0.25  # Uniform over 2x2
    
    return KnownBox(
        name="PR-Lift-3x3",
        probs=P,
        category="pr_lift_like",
        bell_value=4.0,  # Inherited from embedded PR
        description="PR box lifted to 3x3 scenario via sub-block embedding"
    )


def make_local_3x3(alice_strategy: List[int], bob_strategy: List[int]) -> KnownBox:
    """Create a local deterministic box for 3x3x2x2."""
    P = np.zeros((3, 3, 2, 2))
    for x in range(3):
        for y in range(3):
            a = alice_strategy[x]
            b = bob_strategy[y]
            P[x, y, a, b] = 1.0
    
    strategy_name = f"Alice={alice_strategy}, Bob={bob_strategy}"
    return KnownBox(
        name=f"Local-3x3({strategy_name})",
        probs=P,
        category="local",
        bell_value=0.0,  # No CHSH for 3x3
        description=f"Local deterministic 3x3: {strategy_name}"
    )


def get_known_boxes_3x3() -> List[KnownBox]:
    """Get the list of known reference boxes for 3x3x2x2."""
    boxes = []
    
    # PR-lift
    boxes.append(make_pr_lift_3x3())
    
    # All local deterministic boxes for 3x3x2x2
    for a0 in range(2):
        for a1 in range(2):
            for a2 in range(2):
                for b0 in range(2):
                    for b1 in range(2):
                        for b2 in range(2):
                            boxes.append(make_local_3x3([a0, a1, a2], [b0, b1, b2]))
    
    return boxes


def get_known_boxes(shape: Tuple[int, ...] = (2, 2, 2, 2)) -> List[KnownBox]:
    """Get the list of known reference boxes for the given shape."""
    if shape == (3, 3, 2, 2):
        return get_known_boxes_3x3()
    
    # Default: 2x2x2x2 boxes
    boxes = []
    
    # PR box
    boxes.append(make_pr_box())
    
    # Tsirelson box
    boxes.append(make_tsirelson_box())
    
    # All local deterministic boxes for 2x2x2x2
    for a0 in range(2):
        for a1 in range(2):
            for b0 in range(2):
                for b1 in range(2):
                    boxes.append(make_classical_box([a0, a1], [b0, b1]))
    
    return boxes


def compute_distance(P1: np.ndarray, P2: np.ndarray) -> float:
    """Compute the L2 distance between two boxes."""
    if P1.shape != P2.shape:
        return float('inf')
    return np.linalg.norm(P1 - P2)


def compute_fidelity(P1: np.ndarray, P2: np.ndarray) -> float:
    """Compute a fidelity-like measure between two boxes."""
    if P1.shape != P2.shape:
        return 0.0
    # Use cosine similarity
    norm1 = np.linalg.norm(P1)
    norm2 = np.linalg.norm(P2)
    if norm1 == 0 or norm2 == 0:
        return 0.0
    return np.sum(P1 * P2) / (norm1 * norm2)


def classify_box(box: np.ndarray, known_boxes: Optional[List[KnownBox]] = None) -> Dict[str, Any]:
    """Classify a box against known reference boxes."""
    if known_boxes is None:
        known_boxes = get_known_boxes(box.shape)
    
    result = {
        "shape": list(box.shape),
        "matches": [],
        "closest_known": None,
        "category": "unknown",
        "distances": {}
    }
    
    best_distance = float('inf')
    best_match = None
    
    for known in known_boxes:
        if known.probs.shape != box.shape:
            continue
        
        distance = compute_distance(box, known.probs)
        fidelity = compute_fidelity(box, known.probs)
        
        match_info = {
            "name": known.name,
            "category": known.category,
            "distance": distance,
            "fidelity": fidelity,
            "bell_value": known.bell_value
        }
        
        result["matches"].append(match_info)
        result["distances"][known.name] = distance
        
        if distance < best_distance:
            best_distance = distance
            best_match = known
        
        # Check for exact or near-exact match
        if distance < 1e-6:
            result["exact_match"] = known.name
            result["category"] = known.category
    
    if best_match:
        result["closest_known"] = best_match.name
        result["closest_distance"] = best_distance
        result["closest_category"] = best_match.category
    
    # Sort matches by distance
    result["matches"] = sorted(result["matches"], key=lambda m: m["distance"])
    
    # Determine category if not exact match
    if result["category"] == "unknown" and best_match:
        if best_distance < 0.1:
            result["category"] = f"near_{best_match.category}"
        elif best_match.category == "local":
            result["category"] = "nonlocal"  # Far from all local boxes
    
    return result


def main():
    parser = argparse.ArgumentParser(description="Classify box against known boxes")
    parser.add_argument(
        "--box",
        type=Path,
        required=True,
        help="Path to box JSON file"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Output path for classification report"
    )
    parser.add_argument(
        "--top-n",
        type=int,
        default=5,
        help="Number of top matches to show"
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress detailed output"
    )
    
    args = parser.parse_args()
    
    if not args.box.exists():
        print(f"Error: Box file not found: {args.box}")
        return 1
    
    with open(args.box, 'r', encoding='utf-8') as f:
        box_data = json.load(f)
    
    probs = box_data.get("probs", [])
    if not probs:
        print("Error: No probability data in box file")
        return 1
    
    box = np.array(probs)
    
    # Reshape if needed
    shape = box_data.get("shape", [2, 2, 2, 2])
    if len(shape) == 4:
        try:
            box = box.reshape(tuple(shape))
        except ValueError:
            pass
    
    result = classify_box(box)
    result["box_hash"] = box_data.get("canonical_hash", "unknown")
    result["claimed_bell_value"] = box_data.get("bell_value", 0.0)
    
    if not args.quiet:
        print("=" * 60)
        print("BOX CLASSIFICATION")
        print("=" * 60)
        print(f"Box: {args.box}")
        print(f"Hash: {result['box_hash']}")
        print(f"Shape: {result['shape']}")
        print(f"Claimed Bell value: {result['claimed_bell_value']:.4f}")
        print()
        
        if "exact_match" in result:
            print(f"✓ EXACT MATCH: {result['exact_match']}")
        else:
            print(f"Closest known box: {result.get('closest_known', 'unknown')}")
            print(f"  Distance: {result.get('closest_distance', float('inf')):.6f}")
            print(f"  Category: {result.get('closest_category', 'unknown')}")
        
        print(f"\nOverall category: {result['category']}")
        
        print(f"\n--- Top {args.top_n} Matches ---")
        for match in result["matches"][:args.top_n]:
            print(f"  {match['name']}")
            print(f"    Distance: {match['distance']:.6f}")
            print(f"    Fidelity: {match['fidelity']:.4f}")
            print(f"    Category: {match['category']}")
    
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        # Convert numpy values for JSON
        result_json = json.loads(json.dumps(result, default=lambda x: float(x) if isinstance(x, np.floating) else x))
        args.output.write_text(json.dumps(result_json, indent=2), encoding='utf-8')
        if not args.quiet:
            print(f"\nReport saved to: {args.output}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
