#!/usr/bin/env python3
"""
Schrödinger Equation Falsification Test

This script implements an automated falsification test for the Schrödinger equation
derivation via Thiele Machine. It:

1. Generates data with known mass m and potential V
2. Runs the derivation pipeline
3. Asserts that:
   - Selected model == "full_schrodinger"
   - |m_hat - m_true| / m_true < tolerance
   - RMS re-simulation error < threshold

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Optional, Sequence

# Import from same package - works when run as module or script
try:
    from tools.schrodinger_equation_derivation import (
        SchrodingerModel,
        enumerate_models,
        fit_model,
        select_best_model,
        extract_pde_parameters,
        validate_model,
    )
except ImportError:
    # Fallback for direct script execution
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from tools.schrodinger_equation_derivation import (
        SchrodingerModel,
        enumerate_models,
        fit_model,
        select_best_model,
        extract_pde_parameters,
        validate_model,
    )

# Tolerance for mass verification
MASS_TOLERANCE = 0.1  # 10% relative error tolerance
RMS_THRESHOLD = 1e-4  # Maximum allowed RMS error


def run_falsification_test(
    lattice_size: int = 64,
    timesteps: int = 200,
    mass: float = 1.0,
    dt: float = 0.01,
    dx: float = 1.0,
    potential_kind: str = "harmonic",
    omega: float = 0.2,
    seed: int = 42,
    rms_threshold: float = RMS_THRESHOLD,
    mass_tolerance: float = MASS_TOLERANCE,
    verbose: bool = True
) -> bool:
    """
    Run the falsification test for Schrödinger equation derivation.
    
    Args:
        lattice_size: Number of spatial lattice points
        timesteps: Number of time steps
        mass: True particle mass
        dt: Time step
        dx: Spatial step
        potential_kind: Type of potential ("harmonic" or "free")
        omega: Frequency for harmonic potential
        seed: Random seed
        rms_threshold: Maximum allowed RMS error
        mass_tolerance: Tolerance for mass extraction accuracy
        verbose: Print detailed output
    
    Returns:
        True if all tests pass, False otherwise
    """
    import numpy as np
    np.random.seed(seed)
    
    tests_passed = True
    
    if verbose:
        print("=" * 60)
        print("SCHRÖDINGER EQUATION FALSIFICATION TEST")
        print("=" * 60)
    
    # Step 1: Generate data
    if verbose:
        print("\n[1] Generating data with known parameters...")
    
    model = SchrodingerModel(
        lattice_size=lattice_size,
        mass=mass,
        dt=dt,
        dx=dx,
        potential_kind=potential_kind,
        omega=omega
    )
    evolution = model.generate_evolution(timesteps, seed=seed)
    V = model.get_potential()
    
    if verbose:
        print(f"    Generated {timesteps} timesteps on {lattice_size}-site lattice")
        print(f"    True mass m = {mass}")
        print(f"    Potential: {potential_kind}")
    
    # Step 2: Run derivation
    if verbose:
        print("\n[2] Running model selection...")
    
    models = enumerate_models()
    results = []
    for candidate in models:
        result = fit_model(evolution, V, dx, candidate)
        results.append(result)
    
    best_result = select_best_model(results)
    
    if verbose:
        print(f"    Selected model: {best_result.model.name}")
        print(f"    μ_total = {best_result.mu_total:.2f} bits")
    
    # Check 1: Selected model should be full_schrodinger
    model_pass = best_result.model.name == "full_schrodinger"
    if not model_pass:
        tests_passed = False
        if verbose:
            print(f"    ❌ FAIL: Selected model '{best_result.model.name}' != expected 'full_schrodinger'")
    else:
        if verbose:
            print(f"    ✓ PASS: Correct model selected")
    
    # Step 3: Extract PDE parameters
    if verbose:
        print("\n[3] Extracting PDE parameters...")
    
    pde = extract_pde_parameters(best_result, dt, dx)
    
    if verbose:
        print(f"    Extracted mass m = {pde.mass:.6f}")
        print(f"    True mass m = {mass:.6f}")
    
    # Check 2: Mass extraction accuracy
    mass_error = float('nan')  # Default value
    if not np.isnan(pde.mass) and mass > 0:
        mass_error = abs(pde.mass - mass) / mass
        mass_pass = mass_error < mass_tolerance
        
        if not mass_pass:
            tests_passed = False
            if verbose:
                print(f"    ❌ FAIL: Mass relative error {mass_error:.4f} >= tolerance {mass_tolerance}")
        else:
            if verbose:
                print(f"    ✓ PASS: Mass extracted with relative error {mass_error:.6f}")
    else:
        mass_pass = False
        tests_passed = False
        if verbose:
            print(f"    ❌ FAIL: Could not extract valid mass")
    
    # Step 4: Validate by re-simulation
    if verbose:
        print("\n[4] Validating by re-simulation...")
    
    validation_rms, validation_max = validate_model(evolution, V, dx, best_result)
    
    if verbose:
        print(f"    RMS error = {validation_rms:.2e}")
        print(f"    Threshold = {rms_threshold:.2e}")
    
    # Check 3: RMS error below threshold
    rms_pass = validation_rms < rms_threshold
    if not rms_pass:
        tests_passed = False
        if verbose:
            print(f"    ❌ FAIL: RMS error {validation_rms:.2e} >= threshold {rms_threshold:.2e}")
    else:
        if verbose:
            print(f"    ✓ PASS: RMS error below threshold")
    
    # Final verdict
    if verbose:
        print("\n" + "=" * 60)
        print("FALSIFICATION TEST RESULTS")
        print("=" * 60)
    
    if tests_passed:
        if verbose:
            print("\n✓✓✓ PASS ✓✓✓")
            print("All verification checks passed:")
            print(f"  - Model selected: {best_result.model.name}")
            print(f"  - Mass accuracy: {mass_error:.6f} < {mass_tolerance}")
            print(f"  - RMS error: {validation_rms:.2e} < {rms_threshold:.2e}")
        return True
    else:
        if verbose:
            print("\n✗✗✗ FAIL ✗✗✗")
            print("One or more verification checks failed.")
        return False


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Schrödinger Equation Falsification Test"
    )
    parser.add_argument(
        "--lattice-size", type=int, default=64,
        help="Number of spatial lattice points"
    )
    parser.add_argument(
        "--timesteps", type=int, default=200,
        help="Number of time steps to simulate"
    )
    parser.add_argument(
        "--mass", type=float, default=1.0,
        help="Particle mass m"
    )
    parser.add_argument(
        "--dt", type=float, default=0.01,
        help="Time step"
    )
    parser.add_argument(
        "--dx", type=float, default=1.0,
        help="Spatial step"
    )
    parser.add_argument(
        "--potential", type=str, default="harmonic",
        choices=["harmonic", "free"],
        help="Type of potential"
    )
    parser.add_argument(
        "--omega", type=float, default=0.2,
        help="Frequency for harmonic potential"
    )
    parser.add_argument(
        "--seed", type=int, default=42,
        help="Random seed for reproducibility"
    )
    parser.add_argument(
        "--rms-threshold", type=float, default=RMS_THRESHOLD,
        help="Maximum allowed RMS error"
    )
    parser.add_argument(
        "--mass-tolerance", type=float, default=MASS_TOLERANCE,
        help="Tolerance for mass extraction accuracy"
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
        mass=args.mass,
        dt=args.dt,
        dx=args.dx,
        potential_kind=args.potential,
        omega=args.omega,
        seed=args.seed,
        rms_threshold=args.rms_threshold,
        mass_tolerance=args.mass_tolerance,
        verbose=not args.quiet
    )
    
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
