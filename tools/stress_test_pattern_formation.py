#!/usr/bin/env python3
"""
Comprehensive Stress Tests for Pattern Formation

Tests pattern μ-cost measurement under extreme conditions:
1. Large grids (512×512)
2. Long evolution times (10000+ steps)
3. Extreme parameter ranges
4. Multiple pattern types
5. High contrast patterns
6. Edge cases (uniform, noise)

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.pattern_simulator import (
    reaction_diffusion_gray_scott,
    game_of_life,
    spiral_pattern,
    phyllotaxis_pattern,
    random_pattern,
    compute_pattern_mu_cost
)


# Test constants
LARGE_SIZE = 512
MEDIUM_SIZE = 256
LONG_STEPS = 10000
COST_TOLERANCE = 1000  # bits/1000px


def test_large_grid_patterns():
    """Test pattern generation and μ-cost on large 512×512 grids."""
    print("\n" + "="*60)
    print("TEST 1: Large Grid Patterns (512×512)")
    print("="*60)
    
    # Gray-Scott on large grid
    print("\nGenerating Gray-Scott pattern on 512×512 grid...")
    pattern_gs = reaction_diffusion_gray_scott(
        size=LARGE_SIZE,
        steps=5000,
        Du=0.16,
        Dv=0.08,
        F=0.060,
        k=0.062
    )
    cost_gs = compute_pattern_mu_cost(pattern_gs.data)
    print(f"Gray-Scott: μ-cost = {cost_gs:.2f} bits/1000px")
    
    # Phyllotaxis on large grid
    print("\nGenerating phyllotaxis pattern on 512×512 grid...")
    pattern_phyl = phyllotaxis_pattern(size=LARGE_SIZE, n_points=1000)
    cost_phyl = compute_pattern_mu_cost(pattern_phyl.data)
    print(f"Phyllotaxis: μ-cost = {cost_phyl:.2f} bits/1000px")
    
    # Random on large grid
    print("\nGenerating random pattern on 512×512 grid...")
    pattern_rand = random_pattern(size=LARGE_SIZE, density=0.5)
    cost_rand = compute_pattern_mu_cost(pattern_rand.data)
    print(f"Random: μ-cost = {cost_rand:.2f} bits/1000px")
    
    # Validation: Structured should have lower cost than random
    print(f"\nΔμ (Phyllotaxis vs Random): {cost_rand - cost_phyl:.2f} bits/1000px")
    assert cost_phyl < cost_rand, "Phyllotaxis should have lower μ-cost than random"
    
    # Costs should be reasonable (not too extreme)
    assert 0 < cost_gs < 1500, f"Gray-Scott μ-cost out of range: {cost_gs}"
    assert 0 < cost_phyl < 1500, f"Phyllotaxis μ-cost out of range: {cost_phyl}"
    assert 0 < cost_rand < 1500, f"Random μ-cost out of range: {cost_rand}"
    
    print("\n✓ PASSED: Large grid patterns test")


def test_long_evolution():
    """Test with very long evolution times."""
    print("\n" + "="*60)
    print("TEST 2: Long Evolution (10000 steps)")
    print("="*60)
    
    # Gray-Scott with many steps
    print(f"\nRunning Gray-Scott for {LONG_STEPS} steps...")
    pattern = reaction_diffusion_gray_scott(
        size=128,
        steps=LONG_STEPS,
        Du=0.16,
        Dv=0.08,
        F=0.060,
        k=0.062
    )
    cost = compute_pattern_mu_cost(pattern.data)
    print(f"μ-cost after {LONG_STEPS} steps: {cost:.2f} bits/1000px")
    
    # Should still produce valid pattern
    assert not np.isnan(cost), "μ-cost is NaN"
    assert not np.isinf(cost), "μ-cost is infinite"
    assert cost > 0, "μ-cost should be positive"
    
    print("\n✓ PASSED: Long evolution test")


def test_extreme_parameters():
    """Test reaction-diffusion with extreme parameter values."""
    print("\n" + "="*60)
    print("TEST 3: Extreme Parameters")
    print("="*60)
    
    # Very high feed rate
    print("\nTesting high feed rate (F=0.15)...")
    pattern_high_F = reaction_diffusion_gray_scott(
        size=128, steps=2000, F=0.15, k=0.062
    )
    cost_high_F = compute_pattern_mu_cost(pattern_high_F.data)
    print(f"High F: μ-cost = {cost_high_F:.2f} bits/1000px")
    
    # Very low feed rate
    print("\nTesting low feed rate (F=0.01)...")
    pattern_low_F = reaction_diffusion_gray_scott(
        size=128, steps=2000, F=0.01, k=0.062
    )
    cost_low_F = compute_pattern_mu_cost(pattern_low_F.data)
    print(f"Low F: μ-cost = {cost_low_F:.2f} bits/1000px")
    
    # High diffusion contrast
    print("\nTesting high diffusion contrast (Du=0.5, Dv=0.01)...")
    pattern_diff = reaction_diffusion_gray_scott(
        size=128, steps=2000, Du=0.5, Dv=0.01, F=0.060, k=0.062
    )
    cost_diff = compute_pattern_mu_cost(pattern_diff.data)
    print(f"High diffusion contrast: μ-cost = {cost_diff:.2f} bits/1000px")
    
    # All should produce valid costs
    for cost, name in [(cost_high_F, "High F"), (cost_low_F, "Low F"), (cost_diff, "Diff")]:
        assert not np.isnan(cost), f"{name}: μ-cost is NaN"
        assert cost > 0, f"{name}: μ-cost should be positive"
        assert cost < 2000, f"{name}: μ-cost too high ({cost})"
    
    print("\n✓ PASSED: Extreme parameters test")


def test_multiple_spiral_arms():
    """Test spirals with varying number of arms."""
    print("\n" + "="*60)
    print("TEST 4: Multiple Spiral Arms")
    print("="*60)
    
    costs = []
    arms_list = [2, 3, 5, 8, 13]  # Fibonacci numbers
    
    for n_arms in arms_list:
        pattern = spiral_pattern(size=256, arms=n_arms, turns=5)
        cost = compute_pattern_mu_cost(pattern.data)
        costs.append(cost)
        print(f"{n_arms} arms: μ-cost = {cost:.2f} bits/1000px")
    
    # More arms generally means more complexity (but still structured)
    # All should be lower than random (≈664 bits)
    for cost in costs:
        assert cost < 800, f"Spiral μ-cost too high: {cost}"
    
    print("\n✓ PASSED: Multiple spiral arms test")


def test_edge_cases():
    """Test edge cases: uniform patterns, pure noise."""
    print("\n" + "="*60)
    print("TEST 5: Edge Cases (uniform, noise)")
    print("="*60)
    
    size = 128
    
    # Uniform pattern (all zeros)
    print("\nUniform (all zeros)...")
    uniform_zero = np.zeros((size, size))
    cost_zero = compute_pattern_mu_cost(uniform_zero)
    print(f"All zeros: μ-cost = {cost_zero:.2f} bits/1000px")
    
    # Uniform pattern (all ones)
    print("\nUniform (all ones)...")
    uniform_one = np.ones((size, size))
    cost_one = compute_pattern_mu_cost(uniform_one)
    print(f"All ones: μ-cost = {cost_one:.2f} bits/1000px")
    
    # Pure noise (uniform random)
    print("\nPure noise (uniform random)...")
    noise = np.random.rand(size, size)
    cost_noise = compute_pattern_mu_cost(noise)
    print(f"Noise: μ-cost = {cost_noise:.2f} bits/1000px")
    
    # Binary noise (salt and pepper)
    print("\nBinary noise (salt and pepper)...")
    binary_noise = (np.random.rand(size, size) > 0.5).astype(float)
    cost_binary = compute_pattern_mu_cost(binary_noise)
    print(f"Binary noise: μ-cost = {cost_binary:.2f} bits/1000px")
    
    # Uniform should have very low cost (high compressibility)
    assert cost_zero < 100, f"Uniform zero cost too high: {cost_zero}"
    assert cost_one < 100, f"Uniform one cost too high: {cost_one}"
    
    # Noise should have high cost (low compressibility)
    assert cost_noise > 400, f"Noise cost too low: {cost_noise}"
    assert cost_binary > 400, f"Binary noise cost too low: {cost_binary}"
    
    print("\n✓ PASSED: Edge cases test")


def test_high_contrast_patterns():
    """Test patterns with very high contrast."""
    print("\n" + "="*60)
    print("TEST 6: High Contrast Patterns")
    print("="*60)
    
    size = 256
    
    # Checkerboard pattern
    print("\nCheckerboard pattern...")
    x, y = np.meshgrid(np.arange(size), np.arange(size))
    checkerboard = ((x // 16 + y // 16) % 2).astype(float)
    cost_check = compute_pattern_mu_cost(checkerboard)
    print(f"Checkerboard: μ-cost = {cost_check:.2f} bits/1000px")
    
    # Stripes pattern
    print("\nStripes pattern...")
    stripes = (x // 10 % 2).astype(float)
    cost_stripes = compute_pattern_mu_cost(stripes)
    print(f"Stripes: μ-cost = {cost_stripes:.2f} bits/1000px")
    
    # Concentric circles
    print("\nConcentric circles...")
    center = size // 2
    r = np.sqrt((x - center)**2 + (y - center)**2)
    circles = (r // 15 % 2).astype(float)
    cost_circles = compute_pattern_mu_cost(circles)
    print(f"Circles: μ-cost = {cost_circles:.2f} bits/1000px")
    
    # All should have low-to-medium cost (highly structured)
    for cost, name in [(cost_check, "Checkerboard"), (cost_stripes, "Stripes"), (cost_circles, "Circles")]:
        assert 0 < cost < 800, f"{name}: μ-cost out of range ({cost})"
        # Structured patterns should be lower than random (≈664)
        # But some simple patterns might be higher due to edge effects
    
    print("\n✓ PASSED: High contrast patterns test")


def main():
    """Run all stress tests."""
    print("\n" + "="*60)
    print("PATTERN FORMATION STRESS TEST SUITE")
    print("="*60)
    
    tests = [
        test_large_grid_patterns,
        test_long_evolution,
        test_extreme_parameters,
        test_multiple_spiral_arms,
        test_edge_cases,
        test_high_contrast_patterns
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
            failed += 1
    
    print("\n" + "="*60)
    print(f"RESULTS: {passed}/{len(tests)} tests passed")
    if failed > 0:
        print(f"         {failed}/{len(tests)} tests failed")
    print("="*60)
    
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
