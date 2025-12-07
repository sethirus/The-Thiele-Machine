#!/usr/bin/env python3
"""
Verify the supra-quantum 16/5 distribution.

This script validates that:
1. The CSV distribution is valid (normalized, no-signaling)
2. The CHSH value matches 16/5 = 3.2
3. The distribution exceeds the Tsirelson bound of 2√2 ≈ 2.828

This provides the Python verification side of the isomorphism with the
Coq proof in coq/sandboxes/AbstractPartitionCHSH.v (theorem sighted_is_supra_quantum).

IMPORTANT CLARIFICATION:
- The 16/5 distribution achieves CHSH = 3.2, which EXCEEDS the quantum bound (2√2 ≈ 2.828)
- This is NOT the maximum achievable value (the PR-box achieves S = 4)
- The hierarchy is: Classical (2) < Quantum (2.828) < Our dist (3.2) < PR-box (4)
"""

from __future__ import annotations

import csv
import math
from fractions import Fraction
from pathlib import Path
from typing import Dict, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = REPO_ROOT / "artifacts" / "bell" / "supra_quantum_16_5.csv"

# The Tsirelson bound squared: (2√2)² = 8
TSIRELSON_BOUND_SQUARED = 8


def load_distribution(path: Path) -> Dict[Tuple[int, int, int, int], Fraction]:
    """Load the probability distribution from CSV."""
    probabilities: Dict[Tuple[int, int, int, int], Fraction] = {}
    
    with path.open("r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            x = int(row["x"])
            y = int(row["y"])
            a = int(row["a"])
            b = int(row["b"])
            prob_str = row["probability"].strip()
            
            try:
                if "/" in prob_str:
                    num, denom = prob_str.split("/")
                    prob = Fraction(int(num), int(denom))
                else:
                    prob = Fraction(int(prob_str), 1)
            except ValueError as e:
                raise ValueError(f"Invalid probability format '{prob_str}' at ({x},{y},{a},{b}): {e}")
            
            probabilities[(x, y, a, b)] = prob
    
    return probabilities


def verify_normalization(probs: Dict[Tuple[int, int, int, int], Fraction]) -> bool:
    """Verify that probabilities sum to 1 for each (x, y) setting."""
    for x in [0, 1]:
        for y in [0, 1]:
            total = sum(probs.get((x, y, a, b), Fraction(0))
                       for a in [0, 1] for b in [0, 1])
            if total != Fraction(1):
                raise ValueError(f"Normalization failed for (x={x}, y={y}): sum={total}")
    return True


def verify_no_signaling_alice(probs: Dict[Tuple[int, int, int, int], Fraction]) -> bool:
    """Verify Alice's no-signaling: P(a|x, y) independent of y."""
    for x in [0, 1]:
        for a in [0, 1]:
            marginal_y0 = sum(probs.get((x, 0, a, b), Fraction(0)) for b in [0, 1])
            marginal_y1 = sum(probs.get((x, 1, a, b), Fraction(0)) for b in [0, 1])
            if marginal_y0 != marginal_y1:
                raise ValueError(
                    f"No-signaling (Alice) failed for (x={x}, a={a}): "
                    f"P(a|y=0)={marginal_y0}, P(a|y=1)={marginal_y1}"
                )
    return True


def verify_no_signaling_bob(probs: Dict[Tuple[int, int, int, int], Fraction]) -> bool:
    """Verify Bob's no-signaling: P(b|x, y) independent of x."""
    for y in [0, 1]:
        for b in [0, 1]:
            marginal_x0 = sum(probs.get((0, y, a, b), Fraction(0)) for a in [0, 1])
            marginal_x1 = sum(probs.get((1, y, a, b), Fraction(0)) for a in [0, 1])
            if marginal_x0 != marginal_x1:
                raise ValueError(
                    f"No-signaling (Bob) failed for (y={y}, b={b}): "
                    f"P(b|x=0)={marginal_x0}, P(b|x=1)={marginal_x1}"
                )
    return True


def sign(bit: int) -> int:
    """Map bit to ±1: 0 -> -1, 1 -> +1."""
    return 1 if bit == 1 else -1


def compute_expectation(probs: Dict[Tuple[int, int, int, int], Fraction], x: int, y: int) -> Fraction:
    """Compute E(x, y) = sum_{a,b} (-1)^(a+b) P(a,b|x,y)."""
    total = Fraction(0)
    for a in [0, 1]:
        for b in [0, 1]:
            total += sign(a) * sign(b) * probs.get((x, y, a, b), Fraction(0))
    return total


def compute_chsh(probs: Dict[Tuple[int, int, int, int], Fraction]) -> Fraction:
    """
    Compute CHSH value using the Coq convention from BellInequality.v:
    S = E(1,1) + E(1,0) + E(0,1) - E(0,0)
    
    This matches the Coq definition:
    Definition S (B : Box) : Q := E B B1 B1 + E B B1 B0 + E B B0 B1 - E B B0 B0.
    
    Note: This is equivalent to the standard CHSH but with a sign flip.
    """
    e00 = compute_expectation(probs, 0, 0)
    e01 = compute_expectation(probs, 0, 1)
    e10 = compute_expectation(probs, 1, 0)
    e11 = compute_expectation(probs, 1, 1)
    return e11 + e10 + e01 - e00


def exceeds_tsirelson(chsh: Fraction) -> bool:
    """
    Check if CHSH value exceeds the Tsirelson bound of 2√2.
    We check this by comparing chsh² > 8 (since (2√2)² = 8).
    
    This matches the Coq lemma supra_quantum_exceeds_tsirelson:
    Lemma supra_quantum_exceeds_tsirelson : 8 < (16/5) * (16/5).
    """
    chsh_squared = chsh * chsh
    return chsh_squared > Fraction(8)


def verify_distribution(path: Path = CSV_PATH) -> dict:
    """
    Verify the complete supra-quantum distribution.
    
    Returns a dictionary with verification results.
    """
    probs = load_distribution(path)
    
    # Verify validity
    verify_normalization(probs)
    verify_no_signaling_alice(probs)
    verify_no_signaling_bob(probs)
    
    # Compute CHSH and expectations
    e00 = compute_expectation(probs, 0, 0)
    e01 = compute_expectation(probs, 0, 1)
    e10 = compute_expectation(probs, 1, 0)
    e11 = compute_expectation(probs, 1, 1)
    chsh = compute_chsh(probs)
    
    # Verify specific values matching Coq proof
    expected_chsh = Fraction(16, 5)
    if chsh != expected_chsh:
        raise ValueError(f"CHSH value mismatch: got {chsh}, expected {expected_chsh}")
    
    exceeds = exceeds_tsirelson(chsh)
    if not exceeds:
        raise ValueError(f"CHSH value {chsh} does not exceed Tsirelson bound")
    
    return {
        "valid": True,
        "normalized": True,
        "no_signaling": True,
        "expectations": {
            "E(0,0)": str(e00),
            "E(0,1)": str(e01),
            "E(1,0)": str(e10),
            "E(1,1)": str(e11),
        },
        "chsh": str(chsh),
        "chsh_float": float(chsh),
        "exceeds_tsirelson": exceeds,
        "tsirelson_bound": 2 * math.sqrt(2),
    }


def main() -> None:
    """Run verification and print results."""
    print("=" * 70)
    print("Supra-Quantum 16/5 Distribution Verification")
    print("=" * 70)
    print()
    
    try:
        result = verify_distribution()
        
        print("Validity checks:")
        print(f"  ✓ Normalization: {result['normalized']}")
        print(f"  ✓ No-signaling: {result['no_signaling']}")
        print()
        
        print("Expectation values:")
        for key, value in result["expectations"].items():
            print(f"  {key} = {value}")
        print()
        
        print("CHSH value:")
        print(f"  S = {result['chsh']} = {result['chsh_float']:.4f}")
        print(f"  Tsirelson bound 2√2 ≈ {result['tsirelson_bound']:.6f}")
        print(f"  S > 2√2: {result['exceeds_tsirelson']}")
        print()
        
        # Bounds hierarchy
        print("Bounds hierarchy:")
        print(f"  Classical (local realism):  |S| ≤ 2")
        print(f"  Quantum (Tsirelson):        |S| ≤ 2√2 ≈ 2.828")
        print(f"  Our distribution:           S = {result['chsh']} = {result['chsh_float']:.4f}  ← SUPRA-QUANTUM")
        print(f"  PR-box (no-signaling max):  S = 4")
        print()
        
        # Gap analysis
        tsirelson = result['tsirelson_bound']
        gap = result['chsh_float'] - tsirelson
        gap_percent = gap / tsirelson * 100
        print(f"Analysis:")
        print(f"  Gap above Tsirelson: {gap:.6f}")
        print(f"  Percentage above quantum: {gap_percent:.2f}%")
        print()
        
        print("Coq isomorphism:")
        print("  The Python verification matches the Coq proof:")
        print("    - Theorem sighted_is_supra_quantum in AbstractPartitionCHSH.v")
        print("    - chsh_ns supra_quantum_ns = 16/5")
        print("    - 8 < (chsh_ns supra_quantum_ns) * (chsh_ns supra_quantum_ns)")
        print()
        
        print("IMPORTANT CLARIFICATION:")
        print("  The 16/5 value is what this specific sighted Thiele protocol achieves.")
        print("  It is NOT the theoretical maximum (the PR-box achieves S = 4).")
        print()
        
        print("=" * 70)
        print("✓ All verifications passed!")
        print("=" * 70)
        
    except Exception as e:
        print(f"✗ Verification failed: {e}")
        raise


if __name__ == "__main__":
    main()
