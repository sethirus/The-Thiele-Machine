#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Verify CHSH Calibration

Runs calibration checks for CHSH functional and compares to known values.
Exits with non-zero status if any check fails.

Usage:
    python tools/verify_chsh_calibration.py
"""

import sys
from pathlib import Path

import numpy as np

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from tools.compute_classical_bound import compute_classical_bound_exact
from tools.lp_ns_verification import compute_ns_bound_lp
from tools.search_bell_functionals import make_chsh_functional


def main():
    print("=" * 60)
    print("CHSH Calibration Verification")
    print("=" * 60)
    
    functional = make_chsh_functional()
    
    print(f"\nFunctional: {functional.name}")
    print(f"Shape: {functional.shape}")
    
    # Compute classical bound
    print("\n1. Computing classical (local deterministic) bound...")
    classical_bound, _ = compute_classical_bound_exact(functional)
    print(f"   Classical bound: {classical_bound:.10f}")
    
    # Check against known value
    expected_classical = 2.0
    delta_classical = abs(classical_bound - expected_classical)
    print(f"   Expected: {expected_classical}")
    print(f"   Delta: {delta_classical:.2e}")
    
    if delta_classical > 1e-6:
        print(f"   ✗ FAIL: Classical bound off by more than 1e-6")
        return 1
    else:
        print(f"   ✓ PASS")
    
    # Compute NS bound
    print("\n2. Computing NS (no-signaling) bound via LP...")
    ns_bound = compute_ns_bound_lp(functional)
    print(f"   NS bound: {ns_bound:.10f}")
    
    # Check against known value
    expected_ns = 4.0
    delta_ns = abs(ns_bound - expected_ns)
    print(f"   Expected: {expected_ns}")
    print(f"   Delta: {delta_ns:.2e}")
    
    if delta_ns > 1e-6:
        print(f"   ✗ FAIL: NS bound off by more than 1e-6")
        return 1
    else:
        print(f"   ✓ PASS")
    
    # Reference quantum bound (Tsirelson)
    print("\n3. Reference quantum bound (Tsirelson)...")
    quantum_bound = 2.0 * np.sqrt(2)
    print(f"   Quantum bound: {quantum_bound:.10f}")
    print(f"   (This is a known mathematical result, not computed)")
    
    # Check ordering
    print("\n4. Verifying bounds ordering...")
    print(f"   Classical: {classical_bound:.6f}")
    print(f"   Quantum:   {quantum_bound:.6f}")
    print(f"   NS:        {ns_bound:.6f}")
    
    if not (classical_bound < quantum_bound < ns_bound):
        print(f"   ✗ FAIL: Bounds not in expected order")
        return 1
    else:
        print(f"   ✓ PASS: Classical < Quantum < NS")
    
    print("\n" + "=" * 60)
    print("✓ ALL CALIBRATION CHECKS PASSED")
    print("=" * 60)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
