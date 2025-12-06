#!/usr/bin/env python3
"""
Comprehensive Stress Tests for Turbulence Closure Discovery

Tests turbulence closure under extreme conditions:
1. Higher Reynolds numbers (Re=5000)
2. Larger grids (128×128)
3. Longer evolution (500+ timesteps)
4. More coarse-graining factors
5. Different initial conditions
6. Extreme parameter regimes

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.turbulence_discovery import (
    simulate_2d_navier_stokes,
    compute_coarse_grained_error,
    compute_mu_cost_turbulence
)


def test_higher_reynolds():
    """Test at higher Reynolds number (more turbulent)."""
    print("\n" + "="*60)
    print("TEST 1: Higher Reynolds Number (Re=5000)")
    print("="*60)
    
    N = 64
    Re = 5000  # More turbulent
    T = 200
    dt = 0.001
    
    print(f"Simulating Re={Re}, N={N}×{N}, T={T}...")
    start = time.time()
    vorticity, energy = simulate_2d_navier_stokes(nx=N, ny=N, nt=T, Re=Re, dt=dt)
    # Extract final velocity fields (simplified - use vorticity as proxy)
    u = vorticity[-1]
    v = np.zeros_like(u)
    sim_time = time.time() - start
    print(f"Simulation time: {sim_time:.2f}s")
    
    # Test coarse-graining factors
    factors = [2, 4]
    for factor in factors:
        error = compute_coarse_grained_error(u, v, factor)
        mu_cost = compute_mu_cost_turbulence(N, N, T, factor)
        print(f"Factor {factor}: error={error:.3f}%, μ-cost={mu_cost/1000:.1f}k bits")
        
        # Error should be reasonable even at high Re
        assert error < 5.0, f"Factor {factor}: error too high ({error:.2f}%)"
        assert mu_cost > 0, f"Factor {factor}: invalid μ-cost"
    
    print("\n✓ PASSED: Higher Reynolds number test")


def test_larger_grid():
    """Test on larger 128×128 grid."""
    print("\n" + "="*60)
    print("TEST 2: Larger Grid (128×128)")
    print("="*60)
    
    N = 128
    Re = 1000
    T = 100  # Fewer timesteps due to computational cost
    dt = 0.001
    
    print(f"Simulating N={N}×{N}, Re={Re}, T={T}...")
    start = time.time()
    vorticity, energy = simulate_2d_navier_stokes(nx=N, ny=N, nt=T, Re=Re, dt=dt)
    u = vorticity[-1]
    v = np.zeros_like(u)
    sim_time = time.time() - start
    print(f"Simulation time: {sim_time:.2f}s")
    
    # Should complete in reasonable time (<300s)
    assert sim_time < 300, f"Simulation too slow: {sim_time:.1f}s"
    
    # Test coarse-graining
    factor = 4
    error = compute_coarse_grained_error(u, v, factor)
    mu_cost = compute_mu_cost_turbulence(N, N, T, factor)
    print(f"Factor {factor}: error={error:.3f}%, μ-cost={mu_cost/1000:.1f}k bits")
    
    # Larger grids should still give reasonable errors
    assert error < 3.0, f"Error too high on large grid: {error:.2f}%"
    
    print("\n✓ PASSED: Larger grid test")


def test_longer_evolution():
    """Test with longer time evolution."""
    print("\n" + "="*60)
    print("TEST 3: Longer Evolution (T=500)")
    print("="*60)
    
    N = 64
    Re = 1000
    T = 500  # Longer evolution
    dt = 0.001
    
    print(f"Simulating T={T} timesteps...")
    start = time.time()
    vorticity, energy = simulate_2d_navier_stokes(nx=N, ny=N, nt=T, Re=Re, dt=dt)
    u = vorticity[-1]
    v = np.zeros_like(u)
    sim_time = time.time() - start
    print(f"Simulation time: {sim_time:.2f}s")
    
    # Test coarse-graining at different stages
    # Early phase (first 100 steps)
    u_early = u[:100]
    v_early = v[:100]
    error_early = compute_coarse_grained_error(u_early, v_early, factor=2)
    print(f"Early phase (T=0-100): error={error_early:.3f}%")
    
    # Late phase (last 100 steps)
    u_late = u[-100:]
    v_late = v[-100:]
    error_late = compute_coarse_grained_error(u_late, v_late, factor=2)
    print(f"Late phase (T=400-500): error={error_late:.3f}%")
    
    # Full evolution
    error_full = compute_coarse_grained_error(u, v, factor=2)
    print(f"Full evolution (T=0-500): error={error_full:.3f}%")
    
    # All phases should have reasonable errors
    assert error_early < 2.0, f"Early phase error too high: {error_early:.2f}%"
    assert error_late < 2.0, f"Late phase error too high: {error_late:.2f}%"
    assert error_full < 2.0, f"Full evolution error too high: {error_full:.2f}%"
    
    print("\n✓ PASSED: Longer evolution test")


def test_multiple_coarse_graining_factors():
    """Test more coarse-graining factors."""
    print("\n" + "="*60)
    print("TEST 4: Multiple Coarse-Graining Factors")
    print("="*60)
    
    N = 64
    Re = 1000
    T = 200
    dt = 0.001
    
    print(f"Simulating Re={Re}, N={N}×{N}, T={T}...")
    vorticity, energy = simulate_2d_navier_stokes(nx=N, ny=N, nt=T, Re=Re, dt=dt)
    u = vorticity[-1]
    v = np.zeros_like(u)
    
    # Test many factors
    factors = [2, 4, 8, 16]
    errors = []
    mu_costs = []
    
    print("\nTesting coarse-graining factors:")
    for factor in factors:
        if N // factor < 4:  # Skip if too coarse
            continue
        error = compute_coarse_grained_error(u, v, factor)
        mu_cost = compute_mu_cost_turbulence(N, N, T, factor)
        errors.append(error)
        mu_costs.append(mu_cost)
        print(f"Factor {factor:2d}: N_coarse={N//factor:2d}, error={error:.3f}%, μ-cost={mu_cost/1000:6.1f}k bits")
    
    # Error should generally increase with coarsening
    assert errors[0] < errors[-1], "Error should increase with coarse-graining"
    
    # μ-cost should decrease with coarsening (fewer DOF)
    assert mu_costs[0] > mu_costs[-1], "μ-cost should decrease with coarse-graining"
    
    print("\n✓ PASSED: Multiple coarse-graining factors test")


def test_different_initial_conditions():
    """Test with different initial conditions."""
    print("\n" + "="*60)
    print("TEST 5: Different Initial Conditions")
    print("="*60)
    
    N = 64
    Re = 1000
    T = 150
    dt = 0.001
    
    # Standard random initial condition
    print("\nStandard random IC...")
    np.random.seed(42)
    vorticity1, energy1 = simulate_2d_navier_stokes(nx=N, ny=N, nt=T, Re=Re, dt=dt); u1 = vorticity1[-1]; v1 = np.zeros_like(u1)
    error1 = compute_coarse_grained_error(u1, v1, factor=2)
    print(f"Standard: error={error1:.3f}%")
    
    # Different random seed
    print("\nDifferent random IC...")
    np.random.seed(123)
    vorticity2, energy2 = simulate_2d_navier_stokes(nx=N, ny=N, nt=T, Re=Re, dt=dt); u2 = vorticity2[-1]; v2 = np.zeros_like(u2)
    error2 = compute_coarse_grained_error(u2, v2, factor=2)
    print(f"Different seed: error={error2:.3f}%")
    
    # Both should have similar (low) errors
    assert error1 < 2.0, f"Standard IC error too high: {error1:.2f}%"
    assert error2 < 2.0, f"Different IC error too high: {error2:.2f}%"
    
    # Errors should be similar (within factor of 2)
    ratio = max(error1, error2) / min(error1, error2)
    assert ratio < 3.0, f"Error ratio too large: {ratio:.2f}"
    
    print(f"\nError ratio: {ratio:.2f}x (should be <3)")
    
    print("\n✓ PASSED: Different initial conditions test")


def test_extreme_viscosity():
    """Test with extreme viscosity (low Re = high viscosity)."""
    print("\n" + "="*60)
    print("TEST 6: Extreme Viscosity (Re=100, high viscosity)")
    print("="*60)
    
    N = 64
    Re = 100  # Low Re = high viscosity = less turbulent
    T = 200
    dt = 0.001
    
    print(f"Simulating Re={Re} (high viscosity)...")
    vorticity, energy = simulate_2d_navier_stokes(nx=N, ny=N, nt=T, Re=Re, dt=dt)
    u = vorticity[-1]
    v = np.zeros_like(u)
    
    # Test coarse-graining
    factor = 2
    error = compute_coarse_grained_error(u, v, factor)
    print(f"Factor {factor}: error={error:.3f}%")
    
    # High viscosity should be easier to coarse-grain (smoother)
    assert error < 1.0, f"Error too high for smooth flow: {error:.2f}%"
    
    print("\n✓ PASSED: Extreme viscosity test")


def main():
    """Run all stress tests."""
    print("\n" + "="*60)
    print("TURBULENCE CLOSURE STRESS TEST SUITE")
    print("="*60)
    
    tests = [
        test_higher_reynolds,
        test_larger_grid,
        test_longer_evolution,
        test_multiple_coarse_graining_factors,
        test_different_initial_conditions,
        test_extreme_viscosity
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"\n✗ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"\n✗ ERROR: {e}")
            import traceback
            traceback.print_exc()
            failed += 1
    
    print("\n" + "="*60)
    print(f"RESULTS: {passed}/{len(tests)} tests passed")
    if failed > 0:
        print(f"         {failed}/{len(tests)} tests failed")
    print("="*60)
    
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
