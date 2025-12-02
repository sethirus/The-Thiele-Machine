#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Verify Bell Value

Rigorous verification of Bell inequality values for NS boxes.
Determines if a claimed Bell value is:
1. Theoretically possible (within NS polytope bounds)
2. Properly computed (using correct functional)
3. Actually achieved (NS constraints satisfied)

This tool is specifically designed to nail down whether a candidate
extremal box truly beats the standard bounds.

Usage:
    python tools/verify_bell_value.py --box artifacts/nl_search/box.json
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
import numpy as np


# Constants for thresholds
NEAR_DETERMINISTIC_THRESHOLD = 0.9  # |E| > 0.9 is near-deterministic
PR_LIFT_BOUND_3X3 = 4.0  # Maximum for genuine NS boxes in 3x3x2x2
MIN_SUSPICIOUS_CORRELATORS = 4  # Threshold for suspicious near-deterministic count


def load_box(path: Path) -> Dict[str, Any]:
    """Load box from JSON file."""
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)


def check_ns_constraints_strict(P: np.ndarray, tol: float = 1e-8) -> Tuple[bool, List[str], Dict[str, float]]:
    """
    Strictly check all no-signaling constraints.
    
    Returns:
        - bool: Whether all constraints are satisfied
        - list: List of violations found
        - dict: Quantitative metrics of constraint satisfaction
    """
    shape = P.shape
    if len(shape) != 4:
        return False, ["Invalid shape: expected 4D tensor"], {}
    
    X, Y, A, B = shape
    violations = []
    metrics = {}
    
    # 1. Check non-negativity
    min_prob = P.min()
    max_neg = abs(min(0, min_prob))
    metrics["min_probability"] = float(min_prob)
    metrics["max_negativity"] = float(max_neg)
    if min_prob < -tol:
        violations.append(f"Negative probability: min = {min_prob:.10f}")
    
    # 2. Check normalization for each (x,y)
    max_norm_error = 0.0
    for x in range(X):
        for y in range(Y):
            total = P[x, y].sum()
            error = abs(total - 1.0)
            max_norm_error = max(max_norm_error, error)
            if error > tol:
                violations.append(f"Normalization error at ({x},{y}): sum = {total:.10f}")
    metrics["max_normalization_error"] = float(max_norm_error)
    
    # 3. Check Alice's NS constraint: sum_b P(a,b|x,y) = P(a|x) for all y
    max_alice_ns_error = 0.0
    for x in range(X):
        # Get reference marginal from y=0
        ref_marginal = P[x, 0].sum(axis=1)  # sum over b
        for y in range(1, Y):
            current_marginal = P[x, y].sum(axis=1)
            error = np.max(np.abs(ref_marginal - current_marginal))
            max_alice_ns_error = max(max_alice_ns_error, error)
            if error > tol:
                violations.append(f"Alice NS error at x={x}: y=0 marginal differs from y={y} by {error:.10f}")
    metrics["max_alice_ns_error"] = float(max_alice_ns_error)
    
    # 4. Check Bob's NS constraint: sum_a P(a,b|x,y) = P(b|y) for all x
    max_bob_ns_error = 0.0
    for y in range(Y):
        # Get reference marginal from x=0
        ref_marginal = P[0, y].sum(axis=0)  # sum over a
        for x in range(1, X):
            current_marginal = P[x, y].sum(axis=0)
            error = np.max(np.abs(ref_marginal - current_marginal))
            max_bob_ns_error = max(max_bob_ns_error, error)
            if error > tol:
                violations.append(f"Bob NS error at y={y}: x=0 marginal differs from x={x} by {error:.10f}")
    metrics["max_bob_ns_error"] = float(max_bob_ns_error)
    
    # Overall NS satisfaction
    metrics["is_ns_valid"] = len(violations) == 0
    metrics["total_violations"] = len(violations)
    
    return len(violations) == 0, violations, metrics


def compute_chsh_functional_value(P: np.ndarray) -> Dict[str, Any]:
    """
    Compute the CHSH-like functional value for any shape.
    
    For shape (X, Y, 2, 2), the functional is:
    F = sum_{x,y} sign(x,y) * E(x,y)
    where E(x,y) = P(a=b|x,y) - P(a≠b|x,y)
    and sign(x,y) = -1 if (x,y) = (1,1) else +1
    """
    shape = P.shape
    if len(shape) != 4:
        return {"error": "Invalid shape"}
    
    X, Y, A, B = shape
    
    result = {
        "shape": [X, Y, A, B],
        "correlators": [],
        "total_value": 0.0,
        "breakdown": {}
    }
    
    total = 0.0
    for x in range(X):
        for y in range(Y):
            # Compute correlator E(x,y) = sum_{a,b} (-1)^{a+b} P(a,b|x,y)
            correlator = 0.0
            for a in range(A):
                for b in range(B):
                    parity = (-1) ** (a + b)
                    correlator += parity * P[x, y, a, b]
            
            # Determine sign
            sign = -1 if (x, y) == (1, 1) else 1
            contribution = sign * correlator
            
            result["correlators"].append({
                "x": x, "y": y,
                "E": float(correlator),
                "sign": sign,
                "contribution": float(contribution)
            })
            result["breakdown"][f"({x},{y})"] = float(contribution)
            total += contribution
    
    result["total_value"] = float(total)
    return result


def compute_theoretical_bounds(shape: Tuple[int, int, int, int]) -> Dict[str, float]:
    """
    Compute theoretical bounds for the CHSH-like functional on given shape.
    
    Returns:
        - classical_bound: Maximum for local deterministic boxes
        - quantum_bound: Maximum for quantum boxes (Tsirelson)
        - ns_bound: Maximum for any NS box (PR box limit)
        - algebraic_max: Absolute algebraic maximum (all correlators = ±1)
    """
    X, Y, A, B = shape
    
    if shape == (2, 2, 2, 2):
        # Standard CHSH
        return {
            "classical_bound": 2.0,
            "quantum_bound": 2.0 * np.sqrt(2),  # ~2.828
            "ns_bound": 4.0,  # PR box
            "algebraic_max": 4.0,
        }
    elif X == 3 and Y == 3:
        # For 3x3 scenario with CHSH-like functional:
        # We have 9 input pairs, 8 with +sign, 1 with -sign (1,1)
        # 
        # Classical bound: Each correlator is in [-1, 1] for deterministic,
        # but with NS constraints, we can achieve higher by using PR-lift.
        #
        # The PR-lift achieves 4.0 (only 2x2 subblock is PR, rest is uniform)
        # 
        # Can we do better? The NS polytope for 3x3x2x2 is complex.
        # But since uniform distributions give E=0, the extra inputs
        # don't naturally boost the value beyond the 2x2 subblock.
        #
        # However, if we use different (x,y) pairs strategically...
        # The theoretical NS maximum for 3x3 is NOT simply 9 (all ±1).
        #
        # Key insight: For inputs outside the 2x2 core, achieving
        # |E(x,y)| = 1 requires deterministic output, but this
        # conflicts with NS constraints if the 2x2 core is PR-like.
        
        return {
            "classical_bound": 2.0,  # Local deterministic achieves ≤2 on CHSH subblock
            "quantum_bound": 2.0 * np.sqrt(2),  # Quantum on 2x2 subblock
            "ns_bound": 4.0,  # PR-lift is still the best known NS box
            "algebraic_max": 9.0,  # If all 9 correlators were ±1 with right signs
            "pr_lift_value": PR_LIFT_BOUND_3X3,  # What PR-lift actually achieves
            "note": "Values > 4.0 in 3x3x2x2 scenario require rigorous LP verification - often numerical artifacts"
        }
    else:
        # Generic bounds
        num_terms = X * Y
        return {
            "classical_bound": 2.0,
            "ns_bound": 4.0,  # PR-lift
            "algebraic_max": float(num_terms),  # Upper bound if all |E|=1
        }


def verify_bell_value(
    box_path: Path,
    tolerance: float = 1e-6
) -> Dict[str, Any]:
    """
    Comprehensive verification of a claimed Bell value.
    
    Returns a detailed report including:
    - NS constraint satisfaction
    - Recomputed Bell value
    - Comparison to theoretical bounds
    - Verdict: REAL, NUMERIC_GARBAGE, or SUSPICIOUS
    """
    result = {
        "box_path": str(box_path),
        "verdict": "UNKNOWN",
        "details": {}
    }
    
    # Load box
    try:
        box_data = load_box(box_path)
    except Exception as e:
        result["verdict"] = "ERROR"
        result["error"] = f"Could not load box: {e}"
        return result
    
    # Extract data
    probs = np.array(box_data.get("probs", []))
    shape = tuple(box_data.get("shape", [2, 2, 2, 2]))
    claimed_value = box_data.get("bell_value", None)
    claimed_hash = box_data.get("canonical_hash", "unknown")
    
    if probs.size == 0:
        result["verdict"] = "ERROR"
        result["error"] = "No probability data"
        return result
    
    # Reshape if needed
    try:
        probs = probs.reshape(shape)
    except ValueError:
        result["verdict"] = "ERROR"
        result["error"] = f"Cannot reshape {probs.shape} to {shape}"
        return result
    
    result["claimed_value"] = claimed_value
    result["claimed_hash"] = claimed_hash
    result["shape"] = list(shape)
    
    # Step 1: Check NS constraints strictly
    ns_valid, violations, ns_metrics = check_ns_constraints_strict(probs, tolerance)
    result["ns_constraints"] = {
        "valid": ns_valid,
        "violations": violations[:10] if len(violations) > 10 else violations,  # Limit output
        "num_violations": len(violations),
        "metrics": ns_metrics
    }
    
    # Step 2: Recompute Bell value
    bell_result = compute_chsh_functional_value(probs)
    recomputed_value = bell_result["total_value"]
    result["recomputed_value"] = recomputed_value
    result["bell_breakdown"] = bell_result
    
    # Step 3: Get theoretical bounds
    bounds = compute_theoretical_bounds(shape)
    result["theoretical_bounds"] = bounds
    
    # Step 4: Determine verdict
    if not ns_valid:
        if ns_metrics["max_alice_ns_error"] > 0.01 or ns_metrics["max_bob_ns_error"] > 0.01:
            result["verdict"] = "NUMERIC_GARBAGE"
            result["reason"] = "Severe NS constraint violations - box is not a valid NS box"
        else:
            result["verdict"] = "SUSPICIOUS"
            result["reason"] = "Minor NS violations - may be numerical precision issue"
    elif claimed_value is not None:
        diff = abs(claimed_value - recomputed_value)
        result["value_difference"] = diff
        
        if diff > tolerance:
            result["verdict"] = "COMPUTATION_ERROR"
            result["reason"] = f"Claimed value {claimed_value} differs from recomputed {recomputed_value}"
        elif recomputed_value > bounds.get("algebraic_max", float('inf')) + tolerance:
            result["verdict"] = "NUMERIC_GARBAGE"
            result["reason"] = f"Value {recomputed_value} exceeds algebraic maximum {bounds['algebraic_max']}"
        elif shape == (3, 3, 2, 2) and recomputed_value > bounds.get("pr_lift_value", PR_LIFT_BOUND_3X3) + tolerance:
            # For 3x3 scenario, values > PR-lift need special scrutiny
            result["verdict"] = "SUSPICIOUS"
            result["reason"] = (
                f"Value {recomputed_value:.4f} exceeds PR-lift bound ({bounds.get('pr_lift_value', PR_LIFT_BOUND_3X3)}). "
                "This is theoretically possible but rare. "
                "Requires rigorous LP verification to confirm."
            )
        elif recomputed_value > bounds.get("ns_bound", 4.0):
            result["verdict"] = "SUPER_PR"
            result["reason"] = f"Value {recomputed_value} exceeds standard PR bound - requires verification"
        elif recomputed_value > bounds.get("quantum_bound", 2.828):
            result["verdict"] = "SUPER_QUANTUM"
            result["reason"] = f"Value {recomputed_value} exceeds quantum bound but is within NS bounds"
        elif recomputed_value > bounds.get("classical_bound", 2.0):
            result["verdict"] = "NONLOCAL"
            result["reason"] = f"Value {recomputed_value} exceeds classical bound - genuine nonlocality"
        else:
            result["verdict"] = "LOCAL"
            result["reason"] = f"Value {recomputed_value} is within classical bounds"
    else:
        result["verdict"] = "COMPUTED"
        result["reason"] = "No claimed value to compare"
    
    # Step 5: Specific analysis for 3x3 scenario
    if shape == (3, 3, 2, 2):
        # Analyze where the value is coming from
        correlator_analysis = []
        for corr in bell_result["correlators"]:
            x, y = corr["x"], corr["y"]
            E = corr["E"]
            
            # Is this from the 2x2 PR subblock or extended?
            is_core = (x < 2) and (y < 2)
            
            correlator_analysis.append({
                "input": f"({x},{y})",
                "is_core_2x2": is_core,
                "correlator_E": E,
                "contribution": corr["contribution"],
                "magnitude": abs(E),
                "is_near_deterministic": abs(E) > NEAR_DETERMINISTIC_THRESHOLD
            })
        
        result["correlator_analysis"] = correlator_analysis
        
        # Count how many correlators are near-deterministic
        near_det_count = sum(1 for c in correlator_analysis if c["is_near_deterministic"])
        result["near_deterministic_count"] = near_det_count
        
        if near_det_count > MIN_SUSPICIOUS_CORRELATORS and recomputed_value > bounds.get("pr_lift_value", PR_LIFT_BOUND_3X3):
            result["analysis_note"] = (
                f"{near_det_count}/9 correlators are near-deterministic (|E|>{NEAR_DETERMINISTIC_THRESHOLD}). "
                "This pattern is unusual for a genuine NS extremal box and "
                "suggests the optimization pushed toward invalid deterministic corners."
            )
    
    return result


def main():
    parser = argparse.ArgumentParser(description="Rigorously verify Bell value for NS box")
    parser.add_argument(
        "--box",
        type=Path,
        required=True,
        help="Path to box JSON file"
    )
    parser.add_argument(
        "--tolerance",
        type=float,
        default=1e-6,
        help="Tolerance for numerical comparisons"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Output path for verification report"
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
    
    result = verify_bell_value(args.box, args.tolerance)
    
    if not args.quiet:
        print("=" * 70)
        print("BELL VALUE VERIFICATION REPORT")
        print("=" * 70)
        print(f"Box: {args.box}")
        print(f"Hash: {result.get('claimed_hash', 'unknown')}")
        print(f"Shape: {result.get('shape', 'unknown')}")
        print()
        
        print("--- Claimed vs Recomputed Value ---")
        print(f"  Claimed:    {result.get('claimed_value', 'N/A')}")
        print(f"  Recomputed: {result.get('recomputed_value', 'N/A'):.6f}")
        if 'value_difference' in result:
            print(f"  Difference: {result['value_difference']:.10f}")
        print()
        
        print("--- NS Constraints ---")
        ns = result.get("ns_constraints", {})
        print(f"  Valid: {ns.get('valid', 'unknown')}")
        metrics = ns.get("metrics", {})
        print(f"  Max Alice NS error: {metrics.get('max_alice_ns_error', 'N/A'):.10f}")
        print(f"  Max Bob NS error: {metrics.get('max_bob_ns_error', 'N/A'):.10f}")
        print(f"  Max normalization error: {metrics.get('max_normalization_error', 'N/A'):.10f}")
        if ns.get("violations"):
            print(f"  Violations ({ns.get('num_violations', 0)}):")
            for v in ns.get("violations", [])[:5]:
                print(f"    - {v}")
        print()
        
        print("--- Theoretical Bounds ---")
        bounds = result.get("theoretical_bounds", {})
        for key, val in bounds.items():
            if isinstance(val, float):
                print(f"  {key}: {val:.4f}")
            else:
                print(f"  {key}: {val}")
        print()
        
        print("--- Analysis ---")
        if "near_deterministic_count" in result:
            print(f"  Near-deterministic correlators: {result['near_deterministic_count']}/9")
        if "analysis_note" in result:
            print(f"  Note: {result['analysis_note']}")
        print()
        
        # Verdict with explanation
        verdict = result.get("verdict", "UNKNOWN")
        reason = result.get("reason", "")
        
        # Use ASCII-safe indicators for terminal compatibility
        verdict_symbols = {
            "NUMERIC_GARBAGE": "[X]",
            "SUSPICIOUS": "[?]",
            "SUPER_QUANTUM": "[OK]",
            "SUPER_PR": "[OK]", 
            "NONLOCAL": "[OK]",
            "LOCAL": "[--]",
            "COMPUTED": "[i]",
            "ERROR": "[!]",
            "UNKNOWN": "[?]"
        }
        
        print("=" * 70)
        symbol = verdict_symbols.get(verdict, "[?]")
        if verdict == "NUMERIC_GARBAGE":
            print(f"{symbol} VERDICT: {verdict}")
            print(f"    The claimed value is NOT REAL - it's a numerical artifact.")
        elif verdict == "SUSPICIOUS":
            print(f"{symbol} VERDICT: {verdict}")
            print(f"    The value requires additional verification.")
        elif verdict in ["SUPER_QUANTUM", "SUPER_PR", "NONLOCAL"]:
            print(f"{symbol} VERDICT: {verdict}")
            print(f"    The value appears to be genuine.")
        else:
            print(f"{symbol} VERDICT: {verdict}")
        
        print(f"    Reason: {reason}")
        print("=" * 70)
    
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, default=float), encoding='utf-8')
        if not args.quiet:
            print(f"\nReport saved to: {args.output}")
    
    # Return exit code based on verdict
    if verdict in ["NUMERIC_GARBAGE", "ERROR", "COMPUTATION_ERROR"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
