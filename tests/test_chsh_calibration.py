#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Test CHSH Calibration

Verifies that classical and NS bounds for CHSH match known values:
- Classical (local deterministic): 2.0
- Quantum (Tsirelson): 2√2 ≈ 2.828
- NS (no-signaling): 4.0

This test ensures our bound computation tools are working correctly.
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from tools.compute_classical_bound import compute_classical_bound_exact
from tools.lp_ns_verification import compute_ns_bound_lp
from tools.search_bell_functionals import make_chsh_functional


def test_chsh_classical_bound():
    """Test that CHSH classical bound is exactly 2.0."""
    functional = make_chsh_functional()
    classical_bound, _ = compute_classical_bound_exact(functional)
    
    assert abs(classical_bound - 2.0) < 1e-10, \
        f"CHSH classical bound should be 2.0, got {classical_bound}"


def test_chsh_ns_bound():
    """Test that CHSH NS bound is exactly 4.0."""
    functional = make_chsh_functional()
    ns_bound = compute_ns_bound_lp(functional)
    
    assert abs(ns_bound - 4.0) < 1e-6, \
        f"CHSH NS bound should be 4.0, got {ns_bound}"


def test_chsh_quantum_bound():
    """Test that quantum bound (Tsirelson) is 2√2."""
    # This is a reference test - we don't compute quantum bounds here,
    # just document the known value
    expected_quantum = 2.0 * np.sqrt(2)
    
    # Verify the constant is correct
    assert abs(expected_quantum - 2.828427124746) < 1e-10
    
    # Quantum bound should be between classical and NS
    classical = 2.0
    ns = 4.0
    
    assert classical < expected_quantum < ns


def test_bounds_ordering():
    """Test that bounds follow expected ordering: Classical < Quantum < NS."""
    classical = 2.0
    quantum = 2.0 * np.sqrt(2)
    ns = 4.0
    
    assert classical < quantum, "Classical bound should be less than quantum"
    assert quantum < ns, "Quantum bound should be less than NS"


if __name__ == "__main__":
    # Run tests
    test_chsh_classical_bound()
    print("✓ CHSH classical bound: 2.0")
    
    test_chsh_ns_bound()
    print("✓ CHSH NS bound: 4.0")
    
    test_chsh_quantum_bound()
    print("✓ CHSH quantum bound: 2√2 ≈ 2.828")
    
    test_bounds_ordering()
    print("✓ Bounds ordering: Classical < Quantum < NS")
    
    print("\n✓ All CHSH calibration tests passed")
