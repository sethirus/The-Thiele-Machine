#!/usr/bin/env python3
"""
Test suite for improved quantum PDE fitting.

This script validates the improved complex-valued fitting approach against
the original Schrödinger equation derivation code.
"""

import sys
from pathlib import Path

import numpy as np

# Add tools to path
sys.path.insert(0, str(Path(__file__).parent))

from quantum_pde_fitter import (
    fit_schrodinger_advanced,
    fit_with_unitary_evolution,
    fit_hamiltonian_parameters
)

# Import from original schrodinger derivation
try:
    from schrodinger_equation_derivation import SchrodingerModel, init_state, step
except ImportError:
    print("Warning: Could not import from schrodinger_equation_derivation")
    SchrodingerModel = None


def test_observable_fitting():
    """Test the observable-based fitting approach."""
    print("=" * 60)
    print("Test 1: Observable-Based Hamiltonian Fitting")
    print("=" * 60)
    
    if SchrodingerModel is None:
        print("SKIP: SchrodingerModel not available")
        return False
    
    # Parameters
    lattice_size = 64
    dx = 0.2
    dt = 0.001
    mass = 1.0
    omega = 1.0
    timesteps = 50
    
    print(f"Parameters: N={lattice_size}, dx={dx}, dt={dt}, m={mass}, ω={omega}")
    
    # Generate evolution data
    model = SchrodingerModel(
        lattice_size=lattice_size,
        dx=dx,
        dt=dt,
        mass=mass,
        omega=omega,
        potential_kind="harmonic"
    )
    
    evolution_ab = model.generate_evolution(timesteps=timesteps, seed=42)
    V = model.get_potential()
    
    print(f"Generated evolution: shape={evolution_ab.shape}")
    
    # Convert to complex
    evolution_complex = evolution_ab[:, 0, :] + 1j * evolution_ab[:, 1, :]
    
    # Fit using observable method
    result = fit_hamiltonian_parameters(evolution_complex, V, dx, dt)
    
    print("\nResults:")
    print(f"  Fitted mass: {result.hamiltonian_params['mass'].real:.6f}")
    print(f"  True mass: {mass:.6f}")
    print(f"  Error: {abs(result.hamiltonian_params['mass'].real - mass) / mass * 100:.2f}%")
    print(f"  Fit quality: {result.fit_quality:.4f}")
    print(f"  RMS error (density): {result.rms_error_density:.6f}")
    print(f"  RMS error (phase): {result.rms_error_phase:.6f}")
    print(f"  RMS error (total): {result.rms_error_total:.6f}")
    print(f"  μ_discovery: {result.mu_discovery:.2f} bits")
    print(f"  μ_execution: {result.mu_execution:.2f} bits")
    print(f"  μ_total: {result.mu_total:.2f} bits")
    print(f"  Success: {result.success}")
    
    # Success if error < 20%
    mass_error = abs(result.hamiltonian_params['mass'].real - mass) / mass
    passed = mass_error < 0.2
    
    print(f"\n{'PASS' if passed else 'FAIL'}: Mass error {mass_error*100:.1f}% (threshold: 20%)")
    return passed


def test_advanced_fitting():
    """Test the advanced fitting with validation."""
    print("\n" + "=" * 60)
    print("Test 2: Advanced Schrödinger Fitting")
    print("=" * 60)
    
    if SchrodingerModel is None:
        print("SKIP: SchrodingerModel not available")
        return False
    
    # Parameters
    lattice_size = 64
    dx = 0.2
    dt = 0.001
    mass = 1.5
    omega = 0.5
    timesteps = 50
    
    print(f"Parameters: N={lattice_size}, dx={dx}, dt={dt}, m={mass}, ω={omega}")
    
    # Generate evolution
    model = SchrodingerModel(
        lattice_size=lattice_size,
        dx=dx,
        dt=dt,
        mass=mass,
        omega=omega,
        potential_kind="harmonic"
    )
    
    evolution_ab = model.generate_evolution(timesteps=timesteps, seed=123)
    V = model.get_potential()
    
    print(f"Generated evolution: shape={evolution_ab.shape}")
    
    # Fit using advanced method
    result = fit_schrodinger_advanced(evolution_ab, V, dx, dt, true_mass=mass)
    
    print("\nResults:")
    print(f"  Fitted mass: {result.hamiltonian_params['mass'].real:.6f}")
    print(f"  True mass: {mass:.6f}")
    print(f"  Error: {abs(result.hamiltonian_params['mass'].real - mass) / mass * 100:.2f}%")
    print(f"  Fit quality: {result.fit_quality:.4f}")
    print(f"  Success: {result.success}")
    
    mass_error = abs(result.hamiltonian_params['mass'].real - mass) / mass
    passed = mass_error < 0.2
    
    print(f"\n{'PASS' if passed else 'FAIL'}: Mass error {mass_error*100:.1f}% (threshold: 20%)")
    return passed


def test_unitary_evolution():
    """Test the unitary evolution method."""
    print("\n" + "=" * 60)
    print("Test 3: Unitary Evolution Fitting")
    print("=" * 60)
    
    if SchrodingerModel is None:
        print("SKIP: SchrodingerModel not available")
        return False
    
    # Parameters
    lattice_size = 32
    dx = 0.3
    dt = 0.001
    mass = 1.0
    omega = 1.0
    timesteps = 30
    
    print(f"Parameters: N={lattice_size}, dx={dx}, dt={dt}, m={mass}, ω={omega}")
    
    # Generate evolution
    model = SchrodingerModel(
        lattice_size=lattice_size,
        dx=dx,
        dt=dt,
        mass=mass,
        omega=omega,
        potential_kind="harmonic"
    )
    
    evolution_ab = model.generate_evolution(timesteps=timesteps, seed=456)
    V = model.get_potential()
    
    print(f"Generated evolution: shape={evolution_ab.shape}")
    
    # Fit using unitary method
    result = fit_with_unitary_evolution(evolution_ab, V, dx, dt)
    
    print("\nResults:")
    print(f"  Fitted mass: {result.hamiltonian_params['mass'].real:.6f}")
    print(f"  True mass: {mass:.6f}")
    print(f"  Error: {abs(result.hamiltonian_params['mass'].real - mass) / mass * 100:.2f}%")
    print(f"  Norm variation: {result.rms_error_density:.6f}")
    print(f"  Success: {result.success}")
    
    mass_error = abs(result.hamiltonian_params['mass'].real - mass) / mass
    passed = mass_error < 0.5  # More lenient for eigenvalue method
    
    print(f"\n{'PASS' if passed else 'FAIL'}: Mass error {mass_error*100:.1f}% (threshold: 50%)")
    return passed


def run_all_tests():
    """Run all quantum fitting tests."""
    print("\n" + "=" * 60)
    print("QUANTUM PDE FITTING TEST SUITE")
    print("=" * 60)
    
    tests = [
        ("Observable-Based Fitting", test_observable_fitting),
        ("Advanced Schrödinger Fitting", test_advanced_fitting),
        ("Unitary Evolution Fitting", test_unitary_evolution),
    ]
    
    results = []
    for name, test_func in tests:
        try:
            passed = test_func()
            results.append((name, passed))
        except Exception as e:
            print(f"\nERROR in {name}: {e}")
            import traceback
            traceback.print_exc()
            results.append((name, False))
    
    # Summary
    print("\n" + "=" * 60)
    print("TEST SUMMARY")
    print("=" * 60)
    
    for name, passed in results:
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{status}: {name}")
    
    total = len(results)
    passed_count = sum(1 for _, p in results if p)
    
    print(f"\nTotal: {passed_count}/{total} tests passed")
    
    return all(p for _, p in results)


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
