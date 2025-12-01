#!/usr/bin/env python3
"""
Wave Equation Falsification Test

This script implements an automated falsification test for the wave equation
derivation via Thiele Machine. It:

1. Regenerates raw wave evolution data
2. Recomputes the optimal partition Π*
3. Re-extracts coefficients
4. Recomputes PDE constant c²
5. Verifies RMS error < threshold
6. Outputs PASS/FAIL

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Optional, Sequence

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.wave_equation_derivation import (
    WaveModel,
    enumerate_partitions,
    fit_partition,
    select_best_partition,
    extract_discrete_rule,
    discrete_to_pde,
    validate_rule,
)


def run_falsification_test(
    lattice_size: int = 64,
    timesteps: int = 100,
    wave_speed: float = 0.5,
    seed: int = 42,
    rms_threshold: float = 1e-6,
    c_squared_tolerance: float = 0.01,
    verbose: bool = True
) -> bool:
    """
    Run the falsification test for wave equation derivation.
    
    Args:
        lattice_size: Number of spatial lattice points
        timesteps: Number of time steps
        wave_speed: True wave speed for simulation
        seed: Random seed
        rms_threshold: Maximum allowed RMS error
        c_squared_tolerance: Tolerance for c² extraction accuracy
        verbose: Print detailed output
    
    Returns:
        True if all tests pass, False otherwise
    """
    import numpy as np
    np.random.seed(seed)
    
    tests_passed = True
    
    if verbose:
        print("=" * 60)
        print("WAVE EQUATION FALSIFICATION TEST")
        print("=" * 60)
    
    # Step 1: Regenerate raw data
    if verbose:
        print("\n[1] Regenerating raw data...")
    
    model = WaveModel(lattice_size=lattice_size, wave_speed=wave_speed)
    initial = model.initial_packet()
    evolution = model.generate_evolution(timesteps, initial)
    
    if verbose:
        print(f"    Generated {timesteps} timesteps on {lattice_size}-site lattice")
        print(f"    True c = {wave_speed}, c² = {wave_speed**2}")
    
    # Step 2: Recompute Π*
    if verbose:
        print("\n[2] Recomputing optimal partition Π*...")
    
    partitions = enumerate_partitions()
    results = []
    for partition in partitions:
        result = fit_partition(evolution, partition)
        results.append(result)
    
    best_result = select_best_partition(results)
    
    if verbose:
        print(f"    Selected partition: {best_result.partition.name}")
        print(f"    μ_total = {best_result.mu_total:.2f} bits")
    
    # Step 3: Re-extract coefficients
    if verbose:
        print("\n[3] Re-extracting coefficients...")
    
    rule = extract_discrete_rule(best_result)
    
    if verbose:
        print(f"    coeff_u_t = {rule.coeff_u_t:.6f}")
        print(f"    coeff_u_tm1 = {rule.coeff_u_tm1:.6f}")
        print(f"    coeff_u_xp = {rule.coeff_u_xp:.6f}")
        print(f"    coeff_u_xm = {rule.coeff_u_xm:.6f}")
    
    # Step 4: Recompute PDE constant
    if verbose:
        print("\n[4] Recomputing PDE constant c²...")
    
    pde = discrete_to_pde(rule)
    
    if verbose:
        print(f"    Extracted c² = {pde.wave_speed_squared:.6f}")
        print(f"    True c² = {wave_speed**2:.6f}")
    
    # Step 5: Verify RMS error
    if verbose:
        print("\n[5] Verifying RMS error...")
    
    validation_rms, validation_max = validate_rule(evolution, rule)
    
    if verbose:
        print(f"    RMS error = {validation_rms:.2e}")
        print(f"    Threshold = {rms_threshold:.2e}")
    
    # Check 1: RMS error below threshold
    rms_pass = validation_rms < rms_threshold
    if not rms_pass:
        tests_passed = False
        if verbose:
            print(f"    ❌ FAIL: RMS error {validation_rms:.2e} >= threshold {rms_threshold:.2e}")
    else:
        if verbose:
            print(f"    ✓ PASS: RMS error below threshold")
    
    # Check 2: c² accuracy
    c_squared_error = abs(pde.wave_speed_squared - wave_speed**2) / wave_speed**2
    c_squared_pass = c_squared_error < c_squared_tolerance
    
    if not c_squared_pass:
        tests_passed = False
        if verbose:
            print(f"    ❌ FAIL: c² relative error {c_squared_error:.4f} >= tolerance {c_squared_tolerance}")
    else:
        if verbose:
            print(f"    ✓ PASS: c² extracted with relative error {c_squared_error:.6f}")
    
    # Check 3: Coefficient sanity
    # For the wave equation, we expect:
    # coeff_u_t ≈ 2 - 2c²
    # coeff_u_tm1 ≈ -1
    # coeff_u_xp ≈ c²
    # coeff_u_xm ≈ c²
    expected_coeff_u_t = 2 - 2 * wave_speed**2
    expected_coeff_u_tm1 = -1.0
    expected_coeff_neighbors = wave_speed**2
    
    coeff_tolerance = 1e-4
    
    coeff_u_t_pass = abs(rule.coeff_u_t - expected_coeff_u_t) < coeff_tolerance
    coeff_u_tm1_pass = abs(rule.coeff_u_tm1 - expected_coeff_u_tm1) < coeff_tolerance
    coeff_neighbors_pass = (
        abs(rule.coeff_u_xp - expected_coeff_neighbors) < coeff_tolerance and
        abs(rule.coeff_u_xm - expected_coeff_neighbors) < coeff_tolerance
    )
    
    if not coeff_u_t_pass:
        if verbose:
            print(f"    ⚠ WARNING: coeff_u_t {rule.coeff_u_t:.6f} != expected {expected_coeff_u_t:.6f}")
    
    if not coeff_u_tm1_pass:
        if verbose:
            print(f"    ⚠ WARNING: coeff_u_tm1 {rule.coeff_u_tm1:.6f} != expected {expected_coeff_u_tm1:.6f}")
    
    if not coeff_neighbors_pass:
        if verbose:
            print(f"    ⚠ WARNING: neighbor coefficients don't match expected {expected_coeff_neighbors:.6f}")
    
    # Step 6: Final verdict
    if verbose:
        print("\n" + "=" * 60)
        print("FALSIFICATION TEST RESULTS")
        print("=" * 60)
    
    if tests_passed:
        if verbose:
            print("\n✓✓✓ PASS ✓✓✓")
            print(f"All verification checks passed.")
            print(f"  - RMS error: {validation_rms:.2e} < {rms_threshold:.2e}")
            print(f"  - c² accuracy: {c_squared_error:.6f} < {c_squared_tolerance}")
        return True
    else:
        if verbose:
            print("\n✗✗✗ FAIL ✗✗✗")
            print("One or more verification checks failed.")
        return False


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Wave Equation Falsification Test"
    )
    parser.add_argument(
        "--lattice-size", type=int, default=64,
        help="Number of spatial lattice points"
    )
    parser.add_argument(
        "--timesteps", type=int, default=100,
        help="Number of time steps to simulate"
    )
    parser.add_argument(
        "--wave-speed", type=float, default=0.5,
        help="Wave propagation speed c"
    )
    parser.add_argument(
        "--seed", type=int, default=42,
        help="Random seed for reproducibility"
    )
    parser.add_argument(
        "--rms-threshold", type=float, default=1e-6,
        help="Maximum allowed RMS error"
    )
    parser.add_argument(
        "--c-squared-tolerance", type=float, default=0.01,
        help="Tolerance for c² extraction accuracy"
    )
    parser.add_argument(
        "--quiet", "-q", action="store_true",
        help="Suppress output, only exit with status code"
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    """Main entry point."""
    args = parse_args(argv)
    
    passed = run_falsification_test(
        lattice_size=args.lattice_size,
        timesteps=args.timesteps,
        wave_speed=args.wave_speed,
        seed=args.seed,
        rms_threshold=args.rms_threshold,
        c_squared_tolerance=args.c_squared_tolerance,
        verbose=not args.quiet
    )
    
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
