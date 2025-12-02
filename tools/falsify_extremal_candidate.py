#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Falsify Extremal Candidate

Attempts to falsify a candidate extremal box by:
1. Checking NS constraints are satisfied
2. Testing if box is in the interior of the NS polytope
3. Verifying the claimed Bell violation value
4. Checking against known extremal boxes

Usage:
    python falsify_extremal_candidate.py --box artifacts/nl_search/box.json
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
import numpy as np


def load_box(path: Path) -> Dict[str, Any]:
    """Load box from JSON file."""
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)


def check_ns_constraints(box: Dict[str, Any]) -> Tuple[bool, List[str]]:
    """Check that box satisfies no-signaling constraints."""
    errors = []
    probs = box.get('probs', [])
    
    if not probs:
        errors.append("No probability data found in box")
        return False, errors
    
    # Convert to numpy array if possible
    try:
        P = np.array(probs)
    except (ValueError, TypeError) as e:
        errors.append(f"Could not convert probs to array: {e}")
        return False, errors
    
    # Check non-negativity
    if np.any(P < -1e-10):
        errors.append(f"Negative probabilities found: min = {P.min()}")
    
    # Check normalization (sum to 1 for each input pair)
    shape = box.get('shape', [2, 2, 2, 2])
    if len(shape) == 4:
        X, Y, A, B = shape
        try:
            P_reshaped = P.reshape(X, Y, A, B)
            for x in range(X):
                for y in range(Y):
                    total = P_reshaped[x, y, :, :].sum()
                    if abs(total - 1.0) > 1e-6:
                        errors.append(f"Normalization violation at ({x},{y}): sum = {total}")
        except ValueError as e:
            errors.append(f"Could not reshape probabilities: {e}")
    
    return len(errors) == 0, errors


def check_interior_test(box: Dict[str, Any]) -> Tuple[bool, str]:
    """Check if box appears to be in the interior of the NS polytope.
    
    Returns (is_boundary, reason) where is_boundary=True means likely extremal.
    """
    probs = box.get('probs', [])
    if not probs:
        return False, "No probability data"
    
    P = np.array(probs)
    
    # Count zeros and near-zeros (vertices/edges have many zeros)
    near_zero_count = np.sum(np.abs(P) < 1e-8)
    total_count = P.size
    zero_ratio = near_zero_count / total_count
    
    # Extremal boxes typically have many zero entries
    if zero_ratio > 0.3:
        return True, f"High zero ratio ({zero_ratio:.2%}) suggests boundary point"
    else:
        return False, f"Low zero ratio ({zero_ratio:.2%}) suggests interior point"


def check_bell_violation(box: Dict[str, Any], functional: Optional[Dict] = None) -> Tuple[bool, float, str]:
    """Verify the claimed Bell violation value."""
    claimed_value = box.get('bell_value', None)
    
    if claimed_value is None:
        return False, 0.0, "No Bell value claimed"
    
    # Classical bound for CHSH is 2
    classical_bound = 2.0
    quantum_bound = 2.0 * np.sqrt(2)  # ~2.828
    pr_bound = 4.0  # PR box bound
    
    if claimed_value <= classical_bound:
        return False, claimed_value, f"Value {claimed_value} is within classical bound"
    elif claimed_value <= quantum_bound:
        return True, claimed_value, f"Value {claimed_value} is super-classical but sub-quantum"
    elif claimed_value <= pr_bound:
        return True, claimed_value, f"Value {claimed_value} is super-quantum"
    else:
        return False, claimed_value, f"Value {claimed_value} exceeds PR bound (impossible for NS box)"


def falsify_candidate(box_path: Path, functional_path: Optional[Path] = None) -> Dict[str, Any]:
    """Run all falsification tests on a candidate extremal box."""
    result = {
        "box_path": str(box_path),
        "tests": {},
        "is_falsified": False,
        "falsification_reasons": []
    }
    
    # Load box
    try:
        box = load_box(box_path)
        result["box_hash"] = box.get('canonical_hash', 'unknown')
    except Exception as e:
        result["is_falsified"] = True
        result["falsification_reasons"].append(f"Could not load box: {e}")
        return result
    
    # Load functional if provided
    functional = None
    if functional_path and functional_path.exists():
        try:
            with open(functional_path, 'r', encoding='utf-8') as f:
                functional = json.load(f)
        except Exception:
            pass
    
    # Test 1: NS constraints
    ns_valid, ns_errors = check_ns_constraints(box)
    result["tests"]["ns_constraints"] = {
        "passed": ns_valid,
        "errors": ns_errors
    }
    if not ns_valid:
        result["is_falsified"] = True
        result["falsification_reasons"].extend(ns_errors)
    
    # Test 2: Interior test
    is_boundary, boundary_reason = check_interior_test(box)
    result["tests"]["interior_test"] = {
        "is_boundary_point": is_boundary,
        "reason": boundary_reason
    }
    if not is_boundary:
        result["falsification_reasons"].append(f"Interior point: {boundary_reason}")
    
    # Test 3: Bell violation
    bell_valid, bell_value, bell_reason = check_bell_violation(box, functional)
    result["tests"]["bell_violation"] = {
        "valid": bell_valid,
        "value": bell_value,
        "reason": bell_reason
    }
    if not bell_valid and "classical bound" not in bell_reason:
        result["is_falsified"] = True
        result["falsification_reasons"].append(bell_reason)
    
    # Summary
    result["summary"] = {
        "ns_valid": ns_valid,
        "is_boundary": is_boundary,
        "bell_valid": bell_valid,
        "candidate_status": "FALSIFIED" if result["is_falsified"] else ("EXTREMAL_CANDIDATE" if is_boundary and bell_valid else "INCONCLUSIVE")
    }
    
    return result


def main():
    parser = argparse.ArgumentParser(description="Falsify extremal box candidate")
    parser.add_argument(
        "--box",
        type=Path,
        required=True,
        help="Path to box JSON file"
    )
    parser.add_argument(
        "--functional",
        type=Path,
        default=None,
        help="Path to Bell functional JSON file (optional)"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Output path for falsification report"
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
    
    result = falsify_candidate(args.box, args.functional)
    
    if not args.quiet:
        print("=" * 60)
        print("EXTREMAL CANDIDATE FALSIFICATION")
        print("=" * 60)
        print(f"Box: {args.box}")
        print(f"Hash: {result.get('box_hash', 'unknown')}")
        print()
        
        print("--- Test Results ---")
        for test_name, test_result in result["tests"].items():
            passed = test_result.get("passed", test_result.get("valid", False))
            status = "✓" if passed else "❌"
            print(f"  {status} {test_name}")
            if "reason" in test_result:
                print(f"      {test_result['reason']}")
        
        print()
        summary = result["summary"]
        print(f"--- Summary ---")
        print(f"  NS Valid: {summary['ns_valid']}")
        print(f"  Boundary Point: {summary['is_boundary']}")
        print(f"  Bell Valid: {summary['bell_valid']}")
        print(f"  Status: {summary['candidate_status']}")
        
        if result["is_falsified"]:
            print()
            print("❌ CANDIDATE FALSIFIED")
            for reason in result["falsification_reasons"]:
                print(f"  - {reason}")
        elif summary["candidate_status"] == "EXTREMAL_CANDIDATE":
            print()
            print("✓ CANDIDATE NOT FALSIFIED - Remains extremal candidate")
    
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2), encoding='utf-8')
        if not args.quiet:
            print(f"\nReport saved to: {args.output}")
    
    return 0 if not result["is_falsified"] else 1


if __name__ == "__main__":
    sys.exit(main())
