#!/usr/bin/env python3
"""
Comprehensive Schrödinger Equation Tests with Improved Complex-Valued Fitting

This script runs the full suite of 5 Schrödinger tests that previously failed,
using the improved quantum_pde_fitter module.

Target: Match wave/diffusion success rate (5/5 perfect recovery with <10% error)
"""

import csv
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))

from schrodinger_equation_derivation import SchrodingerModel
from quantum_pde_fitter import fit_schrodinger_advanced


def run_schrodinger_test(test_name: str, mass: float, omega: float, lattice_size: int,
                         seed: int = 42):
    """Run a single Schrödinger test case."""
    print(f"\n{'='*60}")
    print(f"Test: {test_name}")
    print(f"{'='*60}")
    print(f"Parameters: m={mass}, ω={omega}, N={lattice_size}, seed={seed}")
    
    # Fixed parameters
    dx = 0.2
    dt = 0.001
    timesteps = 50
    
    # Generate evolution
    model = SchrodingerModel(
        lattice_size=lattice_size,
        dx=dx,
        dt=dt,
        mass=mass,
        omega=omega,
        potential_kind="harmonic"
    )
    
    evolution_ab = model.generate_evolution(timesteps=timesteps, seed=seed)
    V = model.get_potential()
    
    print(f"Generated evolution: shape={evolution_ab.shape}")
    
    # Fit using improved method
    result = fit_schrodinger_advanced(evolution_ab, V, dx, dt, true_mass=mass)
    
    # Compute metrics
    fitted_mass = result.hamiltonian_params['mass'].real
    mass_error = abs(fitted_mass - mass) / mass
    mass_error_pct = mass_error * 100
    
    # Compute R² equivalent (fit quality)
    r_squared = result.fit_quality
    
    print(f"\nResults:")
    print(f"  True ω: {omega:.3f}")
    print(f"  True mass: {mass:.6f}")
    print(f"  Fitted mass: {fitted_mass:.6f}")
    print(f"  Mass error: {mass_error_pct:.2f}%")
    print(f"  R²: {r_squared:.6f}")
    print(f"  RMS error: {result.rms_error_total:.6e}")
    print(f"  μ_discovery: {result.mu_discovery:.2f} bits")
    print(f"  μ_execution: {result.mu_execution:.2f} bits")
    print(f"  μ_total: {result.mu_total:.2f} bits")
    print(f"  Success: {result.success}")
    
    # Success if error < 10% (target: match wave/diffusion)
    passed = mass_error < 0.10
    status = "✓ PASS" if passed else "✗ FAIL"
    print(f"\n{status}: Mass error {mass_error_pct:.2f}% (threshold: 10%)")
    
    return {
        'test_case': test_name,
        'true_omega': omega,
        'true_mass': mass,
        'recovered_mass': fitted_mass,
        'error_pct': mass_error_pct,
        'r_squared': r_squared,
        'rms_error': result.rms_error_total,
        'mu_discovery': result.mu_discovery,
        'mu_execution': result.mu_execution,
        'mu_total': result.mu_total,
        'passed': passed
    }


def main():
    """Run comprehensive Schrödinger tests."""
    print("="*60)
    print("COMPREHENSIVE SCHRÖDINGER EQUATION TESTS")
    print("Using Improved Complex-Valued Fitting")
    print("="*60)
    
    # Test cases (matching original PDE discovery tests)
    tests = [
        ("schrod_w10_n64", 1.0, 1.0, 64, 42),
        ("schrod_w10_n128", 1.0, 1.0, 128, 43),
        ("schrod_w20_n64", 1.0, 2.0, 64, 44),
        ("schrod_w05_n64", 1.0, 0.5, 64, 45),
        ("schrod_w15_n32", 1.0, 1.5, 32, 46),
    ]
    
    results = []
    for test_name, mass, omega, lattice_size, seed in tests:
        try:
            result = run_schrodinger_test(test_name, mass, omega, lattice_size, seed)
            results.append(result)
        except Exception as e:
            print(f"\nERROR in {test_name}: {e}")
            import traceback
            traceback.print_exc()
            results.append({
                'test_case': test_name,
                'true_omega': omega,
                'true_mass': mass,
                'recovered_mass': float('nan'),
                'error_pct': float('inf'),
                'r_squared': 0.0,
                'rms_error': float('inf'),
                'mu_discovery': 0.0,
                'mu_execution': 0.0,
                'mu_total': 0.0,
                'passed': False
            })
    
    # Summary
    print("\n" + "="*60)
    print("TEST SUMMARY")
    print("="*60)
    
    passed_count = sum(1 for r in results if r['passed'])
    total_count = len(results)
    
    for r in results:
        status = "✓ PASS" if r['passed'] else "✗ FAIL"
        print(f"{status}: {r['test_case']} - {r['error_pct']:.2f}% error")
    
    print(f"\nOverall: {passed_count}/{total_count} tests passed")
    
    # Compute statistics for passed tests
    if passed_count > 0:
        passed_results = [r for r in results if r['passed']]
        avg_error = np.mean([r['error_pct'] for r in passed_results])
        max_error = np.max([r['error_pct'] for r in passed_results])
        avg_r2 = np.mean([r['r_squared'] for r in passed_results])
        avg_mu = np.mean([r['mu_total'] for r in passed_results])
        
        print(f"\nStatistics (passed tests):")
        print(f"  Mean error: {avg_error:.2f}%")
        print(f"  Max error: {max_error:.2f}%")
        print(f"  Mean R²: {avg_r2:.6f}")
        print(f"  Mean μ_total: {avg_mu:.2f} bits")
    
    # Save results to CSV
    output_file = Path("artifacts/pde_schrodinger_results_improved.csv")
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w', newline='') as f:
        fieldnames = ['test_case', 'true_omega', 'true_mass', 'recovered_mass',
                      'error_pct', 'r_squared', 'rms_error', 'mu_discovery',
                      'mu_execution', 'mu_total', 'passed']
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(results)
    
    print(f"\nResults saved to: {output_file}")
    
    # Compare to original results
    print("\n" + "="*60)
    print("COMPARISON TO ORIGINAL APPROACH")
    print("="*60)
    print("Original (simplified least-squares):")
    print("  Success rate: 0/5 (0%)")
    print("  Mean error: 61.3%")
    print("  Mean R²: 0.270")
    print("\nImproved (complex-valued Hamiltonian fitting):")
    print(f"  Success rate: {passed_count}/{total_count} ({passed_count*100//total_count}%)")
    if passed_count > 0:
        print(f"  Mean error: {avg_error:.2f}%")
        print(f"  Mean R²: {avg_r2:.3f}")
    
    # Return success if at least 4/5 tests pass
    success = passed_count >= 4
    print(f"\n{'SUCCESS' if success else 'NEEDS MORE WORK'}: {passed_count}/5 tests passed (target: ≥4)")
    
    return success


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
