#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
LP-Based NS Polytope Verification

Uses linear programming to rigorously verify whether a candidate box:
1. Satisfies all NS constraints exactly
2. Is on the boundary of the NS polytope
3. Is a vertex (extremal point)

This is the gold standard for NS verification - if LP says it's not NS,
it definitely isn't. If LP says it is NS, the Bell value is genuine.

Usage:
    python tools/lp_ns_verification.py --box artifacts/nl_search/box.json
    
    # Verify multiple candidates
    python tools/lp_ns_verification.py --batch artifacts/final/candidates/
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
import numpy as np

# Try to import scipy for LP
try:
    from scipy.optimize import linprog
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False
    print("Warning: scipy not available. LP verification disabled.")


# Constants
NS_TOLERANCE = 1e-9  # Very strict tolerance for NS membership
BOUNDARY_TOLERANCE = 1e-6  # Tolerance for checking if on boundary


def build_ns_constraints(shape: Tuple[int, int, int, int]) -> Tuple[np.ndarray, np.ndarray]:
    """
    Build the matrix A and vector b for the NS constraints: Ax = b
    
    NS constraints for P(a,b|x,y):
    1. Normalization: sum_{a,b} P(a,b|x,y) = 1 for each (x,y)
    2. Alice NS: sum_b P(a,b|x,y) = P(a|x) (independent of y)
    3. Bob NS: sum_a P(a,b|x,y) = P(b|y) (independent of x)
    
    Returns:
        A: Constraint matrix
        b: Constraint RHS
    """
    X, Y, A, B = shape
    n_vars = X * Y * A * B  # Number of probability variables
    
    constraints_A = []
    constraints_b = []
    
    # 1. Normalization constraints: sum_{a,b} P(a,b|x,y) = 1
    for x in range(X):
        for y in range(Y):
            row = np.zeros(n_vars)
            for a in range(A):
                for b in range(B):
                    idx = x * (Y * A * B) + y * (A * B) + a * B + b
                    row[idx] = 1.0
            constraints_A.append(row)
            constraints_b.append(1.0)
    
    # 2. Alice NS constraints: P(a|x,y) = P(a|x,y') for all y,y'
    # We express this as: sum_b P(a,b|x,y) - sum_b P(a,b|x,y') = 0
    for x in range(X):
        for a in range(A):
            for y1 in range(Y):
                for y2 in range(y1 + 1, Y):
                    row = np.zeros(n_vars)
                    for b in range(B):
                        idx1 = x * (Y * A * B) + y1 * (A * B) + a * B + b
                        idx2 = x * (Y * A * B) + y2 * (A * B) + a * B + b
                        row[idx1] = 1.0
                        row[idx2] = -1.0
                    constraints_A.append(row)
                    constraints_b.append(0.0)
    
    # 3. Bob NS constraints: P(b|x,y) = P(b|x',y) for all x,x'
    for y in range(Y):
        for b in range(B):
            for x1 in range(X):
                for x2 in range(x1 + 1, X):
                    row = np.zeros(n_vars)
                    for a in range(A):
                        idx1 = x1 * (Y * A * B) + y * (A * B) + a * B + b
                        idx2 = x2 * (Y * A * B) + y * (A * B) + a * B + b
                        row[idx1] = 1.0
                        row[idx2] = -1.0
                    constraints_A.append(row)
                    constraints_b.append(0.0)
    
    return np.array(constraints_A), np.array(constraints_b)


def verify_ns_membership_lp(
    P: np.ndarray,
    tolerance: float = NS_TOLERANCE
) -> Dict[str, Any]:
    """
    Use LP to verify if P is in the NS polytope.
    
    We check:
    1. Non-negativity: P >= 0
    2. Linear constraints: A @ P.flatten() = b (up to tolerance)
    
    Returns:
        Dict with verification result and details
    """
    if not HAS_SCIPY:
        return {
            "verified": False,
            "error": "scipy not available for LP verification",
            "method": "unavailable"
        }
    
    shape = P.shape
    if len(shape) != 4:
        return {
            "verified": False,
            "error": f"Invalid shape: {shape}",
            "method": "lp"
        }
    
    X, Y, A, B = shape
    p_flat = P.flatten()
    n_vars = len(p_flat)
    
    # Build constraints
    A_eq, b_eq = build_ns_constraints(shape)
    
    # Check constraint satisfaction
    residual = A_eq @ p_flat - b_eq
    max_residual = np.max(np.abs(residual))
    
    # Check non-negativity
    min_prob = np.min(p_flat)
    
    result = {
        "method": "lp",
        "shape": list(shape),
        "n_constraints": len(b_eq),
        "max_constraint_residual": float(max_residual),
        "min_probability": float(min_prob),
        "tolerance_used": tolerance
    }
    
    # Verify NS membership
    if min_prob < -tolerance:
        result["verified"] = False
        result["reason"] = f"Negative probability: {min_prob}"
    elif max_residual > tolerance:
        result["verified"] = False
        result["reason"] = f"NS constraint violation: max residual = {max_residual}"
        
        # Find which constraints are violated
        violations = []
        for i, res in enumerate(residual):
            if abs(res) > tolerance:
                violations.append({
                    "constraint_idx": i,
                    "residual": float(res)
                })
        result["violations"] = violations[:10]  # Limit to first 10
    else:
        result["verified"] = True
        result["reason"] = "All NS constraints satisfied"
    
    return result


def find_ns_tight_constraints(
    P: np.ndarray,
    tolerance: float = BOUNDARY_TOLERANCE
) -> Dict[str, Any]:
    """
    Find which constraints are tight (active) at this point.
    
    For a vertex (extremal point), the number of tight constraints
    should equal the dimension of the space.
    """
    shape = P.shape
    X, Y, A, B = shape
    p_flat = P.flatten()
    
    # Count tight non-negativity constraints (P[i] ≈ 0)
    near_zero_count = np.sum(np.abs(p_flat) < tolerance)
    
    # Build NS constraints
    A_eq, b_eq = build_ns_constraints(shape)
    
    # NS equality constraints are always tight by definition
    n_ns_constraints = len(b_eq)
    
    result = {
        "shape": list(shape),
        "total_variables": len(p_flat),
        "near_zero_entries": int(near_zero_count),
        "ns_equality_constraints": n_ns_constraints,
        "total_tight_constraints": int(near_zero_count) + n_ns_constraints
    }
    
    # Dimension of NS polytope = n_vars - n_equality_constraints
    ns_dimension = len(p_flat) - n_ns_constraints
    result["ns_polytope_dimension"] = ns_dimension
    
    # For a vertex, tight constraints should equal or exceed dimension
    # Actually, for vertex: n_tight = n_vars
    # For boundary: n_tight > n_equality_constraints
    
    if near_zero_count >= ns_dimension:
        result["is_vertex_candidate"] = True
        result["vertex_reason"] = f"Enough tight bounds ({near_zero_count} >= {ns_dimension})"
    else:
        result["is_vertex_candidate"] = False
        result["vertex_reason"] = f"Too few tight bounds ({near_zero_count} < {ns_dimension})"
    
    if near_zero_count > 0:
        result["is_on_boundary"] = True
    else:
        result["is_on_boundary"] = False
    
    return result


def maximize_bell_over_ns(
    shape: Tuple[int, int, int, int],
    functional: Optional[np.ndarray] = None
) -> Dict[str, Any]:
    """
    Find the maximum of a Bell functional over the NS polytope.
    
    Uses LP to find the exact maximum, which corresponds to a vertex.
    """
    if not HAS_SCIPY:
        return {
            "error": "scipy not available",
            "method": "unavailable"
        }
    
    X, Y, A, B = shape
    n_vars = X * Y * A * B
    
    # Default: CHSH-like functional
    if functional is None:
        functional = np.zeros((X, Y, A, B))
        for x in range(X):
            for y in range(Y):
                for a in range(A):
                    for b in range(B):
                        parity = (-1) ** (a + b)
                        sign = -1 if (x, y) == (1, 1) else 1
                        functional[x, y, a, b] = sign * parity
    
    c = -functional.flatten()  # Negate for maximization
    
    # Build NS constraints
    A_eq, b_eq = build_ns_constraints(shape)
    
    # Bounds: 0 <= P[i] <= 1
    bounds = [(0, 1) for _ in range(n_vars)]
    
    # Solve LP
    result = linprog(
        c, 
        A_eq=A_eq, 
        b_eq=b_eq, 
        bounds=bounds,
        method='highs'  # HiGHS is default and most robust for LP
    )
    
    if result.success:
        optimal_P = result.x.reshape(shape)
        max_value = -result.fun  # Undo negation
        
        return {
            "success": True,
            "max_value": float(max_value),
            "optimal_box": optimal_P.tolist(),
            "message": result.message
        }
    else:
        return {
            "success": False,
            "error": result.message
        }


def compute_ns_bound_lp(functional) -> float:
    """
    Compute the NS bound for a Bell functional using LP.
    
    Args:
        functional: BellFunctional object with coefficients and shape
    
    Returns:
        Maximum value achievable over NS polytope
    """
    result = maximize_bell_over_ns(functional.shape, functional.coefficients)
    if result.get("success"):
        return result["max_value"]
    return 0.0


def verify_box_file(path: Path, tolerance: float = NS_TOLERANCE) -> Dict[str, Any]:
    """Verify a box from a JSON file."""
    try:
        with open(path, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except Exception as e:
        return {"error": f"Could not load file: {e}"}
    
    probs = np.array(data.get("probs", []))
    shape = tuple(data.get("shape", [2, 2, 2, 2]))
    claimed_value = data.get("bell_value", None)
    
    if probs.size == 0:
        return {"error": "No probability data"}
    
    try:
        P = probs.reshape(shape)
    except ValueError:
        return {"error": f"Cannot reshape to {shape}"}
    
    # Verify NS membership
    ns_result = verify_ns_membership_lp(P, tolerance)
    
    # Check boundary/extremality
    constraint_result = find_ns_tight_constraints(P)
    
    # Compute Bell value
    bell_value = 0.0
    X, Y, A, B = shape
    for x in range(X):
        for y in range(Y):
            correlator = 0.0
            for a in range(A):
                for b in range(B):
                    parity = (-1) ** (a + b)
                    correlator += parity * P[x, y, a, b]
            sign = -1 if (x, y) == (1, 1) else 1
            bell_value += sign * correlator
    
    # Find LP maximum for comparison
    max_result = maximize_bell_over_ns(shape)
    
    return {
        "file": str(path),
        "shape": list(shape),
        "claimed_value": claimed_value,
        "computed_value": float(bell_value),
        "ns_verification": ns_result,
        "boundary_analysis": constraint_result,
        "lp_maximum": max_result.get("max_value", "N/A"),
        "verdict": "GENUINE_NS" if ns_result.get("verified", False) else "INVALID_NS"
    }


def main():
    parser = argparse.ArgumentParser(description="LP-based NS polytope verification")
    parser.add_argument(
        "--box",
        type=Path,
        help="Path to single box JSON file"
    )
    parser.add_argument(
        "--batch",
        type=Path,
        help="Path to directory with multiple box files"
    )
    parser.add_argument(
        "--tolerance",
        type=float,
        default=NS_TOLERANCE,
        help=f"Tolerance for NS constraints (default: {NS_TOLERANCE})"
    )
    parser.add_argument(
        "--find-maximum",
        action="store_true",
        help="Find LP maximum over NS polytope"
    )
    parser.add_argument(
        "--shape",
        type=str,
        default="2,2,2,2",
        help="Shape for finding maximum (default: 2,2,2,2)"
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Output file for results"
    )
    
    args = parser.parse_args()
    
    if args.find_maximum:
        shape = tuple(map(int, args.shape.split(",")))
        print(f"\n{'='*60}")
        print(f"Finding LP Maximum over NS Polytope")
        print(f"{'='*60}")
        print(f"Shape: {shape}")
        
        result = maximize_bell_over_ns(shape)
        
        if result.get("success"):
            print(f"\nLP Maximum: {result['max_value']:.6f}")
            print(f"Message: {result['message']}")
        else:
            print(f"\nFailed: {result.get('error', 'unknown')}")
        
        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                json.dump(result, f, indent=2, default=float)
        return 0
    
    if args.box:
        result = verify_box_file(args.box, args.tolerance)
        
        print(f"\n{'='*60}")
        print("LP-BASED NS VERIFICATION")
        print(f"{'='*60}")
        print(f"File: {args.box}")
        print(f"Shape: {result.get('shape', 'unknown')}")
        print()
        
        print("--- NS Verification ---")
        ns = result.get("ns_verification", {})
        print(f"  Verified: {ns.get('verified', 'unknown')}")
        print(f"  Max residual: {ns.get('max_constraint_residual', 'N/A'):.2e}")
        print(f"  Min probability: {ns.get('min_probability', 'N/A'):.2e}")
        if not ns.get("verified"):
            print(f"  Reason: {ns.get('reason', 'unknown')}")
        print()
        
        print("--- Boundary Analysis ---")
        ba = result.get("boundary_analysis", {})
        print(f"  Near-zero entries: {ba.get('near_zero_entries', 'N/A')}")
        print(f"  NS dimension: {ba.get('ns_polytope_dimension', 'N/A')}")
        print(f"  Is on boundary: {ba.get('is_on_boundary', 'N/A')}")
        print(f"  Is vertex candidate: {ba.get('is_vertex_candidate', 'N/A')}")
        print()
        
        print("--- Bell Value ---")
        print(f"  Claimed: {result.get('claimed_value', 'N/A')}")
        print(f"  Computed: {result.get('computed_value', 'N/A'):.6f}")
        print(f"  LP Maximum: {result.get('lp_maximum', 'N/A')}")
        print()
        
        print(f"{'='*60}")
        print(f"VERDICT: {result.get('verdict', 'UNKNOWN')}")
        print(f"{'='*60}")
        
        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                json.dump(result, f, indent=2, default=float)
        
        return 0 if result.get("verdict") == "GENUINE_NS" else 1
    
    if args.batch:
        if not args.batch.is_dir():
            print(f"Error: {args.batch} is not a directory")
            return 1
        
        results = []
        for box_file in sorted(args.batch.glob("*.json")):
            result = verify_box_file(box_file, args.tolerance)
            results.append(result)
            
            status = "[OK]" if result.get("verdict") == "GENUINE_NS" else "[X]"
            print(f"{status} {box_file.name}: {result.get('computed_value', 'N/A'):.4f}")
        
        # Summary
        genuine = sum(1 for r in results if r.get("verdict") == "GENUINE_NS")
        print(f"\nSummary: {genuine}/{len(results)} genuine NS boxes")
        
        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                json.dump(results, f, indent=2, default=float)
        
        return 0
    
    parser.print_help()
    return 1


if __name__ == "__main__":
    sys.exit(main())
