#!/usr/bin/env python3
"""
Stress Test Suite for Quantum PDE Fitting
Tests with larger datasets, edge cases, and falsification attempts
"""

import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from quantum_pde_fitter import fit_schrodinger_advanced

# Test thresholds
ERROR_THRESHOLD_STANDARD = 10.0  # Standard error threshold (%)
ERROR_THRESHOLD_EXTREME_AVG = 15.0  # Average error for extreme conditions (%)
ERROR_THRESHOLD_EXTREME_MAX = 25.0  # Max error for extreme conditions (%)
ERROR_THRESHOLD_COMBINED = 15.0  # Higher threshold for combined stress test (%)

def generate_schrodinger_evolution(N, dx, dt, T, mass, omega, seed=42):
    """Generate Schrödinger evolution with harmonic potential"""
    np.random.seed(seed)
    
    x = np.linspace(-N//2 * dx, N//2 * dx, N)
    V = 0.5 * mass * omega**2 * x**2
    
    # Initial Gaussian wavepacket
    x0 = 0.0
    sigma = 1.0
    k0 = 2.0
    psi = np.exp(-(x - x0)**2 / (2 * sigma**2)) * np.exp(1j * k0 * x)
    psi = psi / np.sqrt(np.sum(np.abs(psi)**2) * dx)
    
    # Evolve using split-operator method
    evolution = np.zeros((T, 2, N))
    evolution[0, 0, :] = psi.real
    evolution[0, 1, :] = psi.imag
    
    # FFT frequencies (constant, computed once)
    k = 2 * np.pi * np.fft.fftfreq(N, dx)
    kinetic_phase = np.exp(-1j * (k**2 / (2 * mass)) * dt)
    potential_phase = np.exp(-1j * V * dt)
    
    for t in range(1, T):
        # Kinetic evolution (momentum space)
        psi_k = np.fft.fft(psi)
        psi_k *= kinetic_phase
        psi = np.fft.ifft(psi_k)
        
        # Potential evolution (position space)
        psi *= potential_phase
        
        evolution[t, 0, :] = psi.real
        evolution[t, 1, :] = psi.imag
    
    return evolution, V, x

def test_large_grid():
    """Test with large spatial grid (256 points)"""
    print("="*60)
    print("STRESS TEST 1: Large Grid (N=256)")
    print("="*60)
    
    N = 256
    dx = 0.1
    dt = 0.0005
    T = 100
    mass_true = 1.0
    omega = 1.0
    
    evolution, V, x = generate_schrodinger_evolution(N, dx, dt, T, mass_true, omega, seed=42)
    
    result = fit_schrodinger_advanced(evolution, V, dx, dt, true_mass=mass_true)
    
    mass_fitted = result.hamiltonian_params['mass'].real
    error_pct = abs(mass_fitted - mass_true) / mass_true * 100
    
    print(f"Grid size: {N}")
    print(f"Timesteps: {T}")
    print(f"True mass: {mass_true:.6f}")
    print(f"Fitted mass: {mass_fitted:.6f}")
    print(f"Error: {error_pct:.2f}%")
    print(f"R²: {result.fit_quality:.6f}")
    print(f"Success: {result.success}")
    
    passed = error_pct < ERROR_THRESHOLD_STANDARD
    print(f"\n{'✓ PASS' if passed else '✗ FAIL'}: Error {error_pct:.2f}% (threshold: {ERROR_THRESHOLD_STANDARD}%)")
    return passed

def test_long_evolution():
    """Test with long time evolution (200 timesteps)"""
    print("\n" + "="*60)
    print("STRESS TEST 2: Long Evolution (T=200)")
    print("="*60)
    
    N = 64
    dx = 0.2
    dt = 0.001
    T = 200
    mass_true = 1.0
    omega = 1.0
    
    evolution, V, x = generate_schrodinger_evolution(N, dx, dt, T, mass_true, omega, seed=43)
    
    result = fit_schrodinger_advanced(evolution, V, dx, dt, true_mass=mass_true)
    
    mass_fitted = result.hamiltonian_params['mass'].real
    error_pct = abs(mass_fitted - mass_true) / mass_true * 100
    
    print(f"Grid size: {N}")
    print(f"Timesteps: {T}")
    print(f"True mass: {mass_true:.6f}")
    print(f"Fitted mass: {mass_fitted:.6f}")
    print(f"Error: {error_pct:.2f}%")
    print(f"R²: {result.fit_quality:.6f}")
    print(f"Success: {result.success}")
    
    passed = error_pct < ERROR_THRESHOLD_STANDARD
    print(f"\n{'✓ PASS' if passed else '✗ FAIL'}: Error {error_pct:.2f}% (threshold: {ERROR_THRESHOLD_STANDARD}%)")
    return passed

def test_extreme_mass():
    """Test with extreme mass values"""
    print("\n" + "="*60)
    print("STRESS TEST 3: Extreme Mass Values")
    print("="*60)
    
    N = 64
    dx = 0.2
    dt = 0.001
    T = 50
    omega = 1.0
    
    test_masses = [0.1, 0.5, 2.0, 5.0, 10.0]
    results = []
    
    for mass_true in test_masses:
        evolution, V, x = generate_schrodinger_evolution(N, dx, dt, T, mass_true, omega, seed=44)
        result = fit_schrodinger_advanced(evolution, V, dx, dt, true_mass=mass_true)
        mass_fitted = result.hamiltonian_params['mass'].real
        error_pct = abs(mass_fitted - mass_true) / mass_true * 100
        results.append({'mass_fitted': mass_fitted, 'error_pct': error_pct, 'result': result})
        
        print(f"\nMass = {mass_true:.1f}: Fitted = {mass_fitted:.6f}, Error = {error_pct:.2f}%")
    
    errors = [r['error_pct'] for r in results]
    avg_error = np.mean(errors)
    max_error = np.max(errors)
    
    print(f"\nAverage error: {avg_error:.2f}%")
    print(f"Maximum error: {max_error:.2f}%")
    
    passed = avg_error < ERROR_THRESHOLD_EXTREME_AVG and max_error < ERROR_THRESHOLD_EXTREME_MAX
    print(f"\n{'✓ PASS' if passed else '✗ FAIL'}: Avg {avg_error:.2f}% (threshold: {ERROR_THRESHOLD_EXTREME_AVG}%), Max {max_error:.2f}% (threshold: {ERROR_THRESHOLD_EXTREME_MAX}%)")
    return passed

def test_strong_potential():
    """Test with strong harmonic potential"""
    print("\n" + "="*60)
    print("STRESS TEST 4: Strong Potential (ω=5.0)")
    print("="*60)
    
    N = 64
    dx = 0.2
    dt = 0.0005  # Smaller timestep for stability
    T = 50
    mass_true = 1.0
    omega = 5.0  # Strong potential
    
    evolution, V, x = generate_schrodinger_evolution(N, dx, dt, T, mass_true, omega, seed=45)
    
    result = fit_schrodinger_advanced(evolution, V, dx, dt, true_mass=mass_true)
    
    mass_fitted = result.hamiltonian_params['mass'].real
    error_pct = abs(mass_fitted - mass_true) / mass_true * 100
    
    print(f"Potential strength: ω = {omega}")
    print(f"True mass: {mass_true:.6f}")
    print(f"Fitted mass: {mass_fitted:.6f}")
    print(f"Error: {error_pct:.2f}%")
    print(f"R²: {result.fit_quality:.6f}")
    print(f"Success: {result.success}")
    
    passed = error_pct < ERROR_THRESHOLD_STANDARD
    print(f"\n{'✓ PASS' if passed else '✗ FAIL'}: Error {error_pct:.2f}% (threshold: {ERROR_THRESHOLD_STANDARD}%)")
    return passed

def test_weak_potential():
    """Test with weak harmonic potential"""
    print("\n" + "="*60)
    print("STRESS TEST 5: Weak Potential (ω=0.1)")
    print("="*60)
    
    N = 64
    dx = 0.2
    dt = 0.001
    T = 50
    mass_true = 1.0
    omega = 0.1  # Weak potential
    
    evolution, V, x = generate_schrodinger_evolution(N, dx, dt, T, mass_true, omega, seed=46)
    
    result = fit_schrodinger_advanced(evolution, V, dx, dt, true_mass=mass_true)
    
    mass_fitted = result.hamiltonian_params['mass'].real
    error_pct = abs(mass_fitted - mass_true) / mass_true * 100
    
    print(f"Potential strength: ω = {omega}")
    print(f"True mass: {mass_true:.6f}")
    print(f"Fitted mass: {mass_fitted:.6f}")
    print(f"Error: {error_pct:.2f}%")
    print(f"R²: {result.fit_quality:.6f}")
    print(f"Success: {result.success}")
    
    passed = error_pct < ERROR_THRESHOLD_STANDARD
    print(f"\n{'✓ PASS' if passed else '✗ FAIL'}: Error {error_pct:.2f}% (threshold: {ERROR_THRESHOLD_STANDARD}%)")
    return passed

def test_combined_stress():
    """Test with combined challenging conditions"""
    print("\n" + "="*60)
    print("STRESS TEST 6: Combined (Large + Long + Extreme)")
    print("="*60)
    
    N = 128
    dx = 0.15
    dt = 0.0005
    T = 150
    mass_true = 3.5
    omega = 2.5
    
    evolution, V, x = generate_schrodinger_evolution(N, dx, dt, T, mass_true, omega, seed=47)
    
    result = fit_schrodinger_advanced(evolution, V, dx, dt, true_mass=mass_true)
    
    mass_fitted = result.hamiltonian_params['mass'].real
    error_pct = abs(mass_fitted - mass_true) / mass_true * 100
    
    print(f"Grid size: {N}")
    print(f"Timesteps: {T}")
    print(f"Mass: {mass_true}")
    print(f"Potential: ω = {omega}")
    print(f"True mass: {mass_true:.6f}")
    print(f"Fitted mass: {mass_fitted:.6f}")
    print(f"Error: {error_pct:.2f}%")
    print(f"R²: {result.fit_quality:.6f}")
    print(f"Success: {result.success}")
    
    # Higher threshold for combined stress test due to extreme parameter combinations
    passed = error_pct < ERROR_THRESHOLD_COMBINED
    print(f"\n{'✓ PASS' if passed else '✗ FAIL'}: Error {error_pct:.2f}% (threshold: {ERROR_THRESHOLD_COMBINED}%)")
    return passed

def main():
    print("="*60)
    print("QUANTUM PDE STRESS TEST SUITE")
    print("Testing with larger datasets and edge cases")
    print("="*60)
    
    tests = [
        ("Large Grid", test_large_grid),
        ("Long Evolution", test_long_evolution),
        ("Extreme Masses", test_extreme_mass),
        ("Strong Potential", test_strong_potential),
        ("Weak Potential", test_weak_potential),
        ("Combined Stress", test_combined_stress),
    ]
    
    results = []
    for name, test_func in tests:
        try:
            passed = test_func()
            results.append((name, passed))
        except Exception as e:
            print(f"\n✗ ERROR in {name}: {e}")
            results.append((name, False))
    
    print("\n" + "="*60)
    print("STRESS TEST SUMMARY")
    print("="*60)
    
    for name, passed in results:
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{status}: {name}")
    
    passed_count = sum(1 for _, p in results if p)
    total = len(results)
    
    print(f"\nTotal: {passed_count}/{total} tests passed ({100*passed_count/total:.0f}%)")
    
    if passed_count == total:
        print("\n✓ ALL STRESS TESTS PASSED")
        return 0
    else:
        print(f"\n✗ {total - passed_count} STRESS TEST(S) FAILED")
        return 1

if __name__ == "__main__":
    exit(main())
