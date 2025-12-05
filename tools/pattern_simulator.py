#!/usr/bin/env python3
"""
Pattern Formation Simulator for Thiele Machine

This module simulates various pattern formation systems and measures their μ-cost
to validate H3 (μ captures pattern regularity).

Pattern systems implemented:
1. Reaction-Diffusion (Gray-Scott model)
2. Cellular Automata (Conway's Game of Life, spirals)
3. Phyllotaxis (plant leaf arrangement)
4. Random patterns (negative control)

The goal is to show that structured patterns have lower μ-cost than random patterns,
demonstrating that information-theoretic principles capture pattern regularity.

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple

import numpy as np
from scipy.ndimage import convolve


@dataclass
class Pattern:
    """A 2D pattern with metadata."""
    name: str
    data: np.ndarray  # 2D array
    description: str
    is_structured: bool  # True for structured patterns, False for random


def reaction_diffusion_gray_scott(
    size: int = 128,
    steps: int = 5000,
    Du: float = 0.16,
    Dv: float = 0.08,
    F: float = 0.060,
    k: float = 0.062,
    dt: float = 1.0
) -> Pattern:
    """
    Simulate Gray-Scott reaction-diffusion system.
    
    The Gray-Scott model produces intricate spatial patterns including
    spots, stripes, and spirals depending on parameters.
    
    Equations:
        ∂u/∂t = Du∇²u - uv² + F(1-u)
        ∂v/∂t = Dv∇²v + uv² - (F+k)v
    
    Args:
        size: Grid size (size × size)
        steps: Number of time steps
        Du, Dv: Diffusion coefficients
        F: Feed rate
        k: Kill rate
        dt: Time step
        
    Returns:
        Pattern with final v concentration (shows spots/stripes)
    """
    # Initialize with uniform state plus small perturbation
    u = np.ones((size, size))
    v = np.zeros((size, size))
    
    # Add seed perturbation in center
    center = size // 2
    r = size // 10
    y, x = np.ogrid[-center:size-center, -center:size-center]
    mask = x*x + y*y <= r*r
    v[mask] = 1.0
    
    # Laplacian kernel (5-point stencil)
    laplacian = np.array([[0, 1, 0],
                          [1, -4, 1],
                          [0, 1, 0]])
    
    # Time evolution
    for _ in range(steps):
        # Compute Laplacians
        Lu = convolve(u, laplacian, mode='wrap')
        Lv = convolve(v, laplacian, mode='wrap')
        
        # Reaction terms
        uvv = u * v * v
        
        # Update
        u += dt * (Du * Lu - uvv + F * (1 - u))
        v += dt * (Dv * Lv + uvv - (F + k) * v)
        
        # Clamp to valid range
        u = np.clip(u, 0, 1)
        v = np.clip(v, 0, 1)
    
    return Pattern(
        name="gray_scott_spots",
        data=v,
        description="Gray-Scott reaction-diffusion with spot patterns",
        is_structured=True
    )


def cellular_automaton_life(
    size: int = 128,
    steps: int = 100,
    seed: int = 42
) -> Pattern:
    """
    Simulate Conway's Game of Life.
    
    Rules:
    - Any live cell with 2-3 neighbors survives
    - Any dead cell with exactly 3 neighbors becomes alive
    - All other cells die or stay dead
    
    Args:
        size: Grid size
        steps: Number of generations
        seed: Random seed for initial state
        
    Returns:
        Pattern with final state
    """
    np.random.seed(seed)
    
    # Initialize with random state (30% alive)
    grid = (np.random.random((size, size)) < 0.3).astype(float)
    
    # Evolution kernel (count neighbors)
    kernel = np.array([[1, 1, 1],
                       [1, 0, 1],
                       [1, 1, 1]])
    
    for _ in range(steps):
        # Count neighbors
        neighbors = convolve(grid, kernel, mode='wrap')
        
        # Apply rules
        # Birth: dead cell with 3 neighbors
        birth = (grid == 0) & (neighbors == 3)
        # Survival: live cell with 2 or 3 neighbors
        survival = (grid == 1) & ((neighbors == 2) | (neighbors == 3))
        
        grid = (birth | survival).astype(float)
    
    return Pattern(
        name="game_of_life",
        data=grid,
        description="Conway's Game of Life after evolution",
        is_structured=True
    )


def cellular_automaton_spiral(
    size: int = 128,
    arms: int = 3
) -> Pattern:
    """
    Generate a spiral pattern using cellular automata.
    
    Creates rotating spiral waves similar to those in excitable media.
    
    Args:
        size: Grid size
        arms: Number of spiral arms
        
    Returns:
        Pattern with spiral structure
    """
    grid = np.zeros((size, size))
    center = size // 2
    
    # Create spiral arms
    y, x = np.ogrid[:size, :size]
    y = y - center
    x = x - center
    
    # Polar coordinates
    r = np.sqrt(x*x + y*y)
    theta = np.arctan2(y, x)
    
    # Spiral phase
    phase = theta * arms + r / (size / 10)
    
    # Create spiral pattern
    grid = (np.sin(phase) > 0).astype(float)
    
    return Pattern(
        name=f"spiral_{arms}arms",
        data=grid,
        description=f"Spiral pattern with {arms} arms",
        is_structured=True
    )


def phyllotaxis_pattern(
    size: int = 128,
    n_points: int = 500,
    angle: float = 137.5  # Golden angle in degrees
) -> Pattern:
    """
    Generate phyllotaxis (plant leaf arrangement) pattern.
    
    Uses the golden angle (≈137.5°) which produces optimal packing
    and beautiful spiral patterns seen in sunflowers, pinecones, etc.
    
    Args:
        size: Grid size
        n_points: Number of points (leaves)
        angle: Divergence angle in degrees (137.5 for golden angle)
        
    Returns:
        Pattern showing phyllotaxis arrangement
    """
    grid = np.zeros((size, size))
    center = size // 2
    
    # Convert angle to radians
    angle_rad = angle * np.pi / 180
    
    # Generate spiral points
    for i in range(n_points):
        # Radius grows with square root
        r = 0.5 * np.sqrt(i)
        
        # Angle increases by golden angle
        theta = i * angle_rad
        
        # Convert to Cartesian
        x = center + int(r * np.cos(theta))
        y = center + int(r * np.sin(theta))
        
        # Draw point (small circle)
        if 0 <= x < size and 0 <= y < size:
            # Draw 3x3 blob
            for dx in range(-1, 2):
                for dy in range(-1, 2):
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < size and 0 <= ny < size:
                        grid[ny, nx] = 1.0
    
    return Pattern(
        name="phyllotaxis",
        data=grid,
        description="Phyllotaxis pattern (golden angle spiral)",
        is_structured=True
    )


def random_pattern(size: int = 128, density: float = 0.5, seed: int = 42) -> Pattern:
    """
    Generate random pattern (negative control).
    
    Args:
        size: Grid size
        density: Fraction of cells that are 1
        seed: Random seed
        
    Returns:
        Pattern with random values
    """
    np.random.seed(seed)
    grid = (np.random.random((size, size)) < density).astype(float)
    
    return Pattern(
        name="random",
        data=grid,
        description="Random pattern (negative control)",
        is_structured=False
    )


def compute_mu_cost(pattern: Pattern) -> float:
    """
    Compute μ-cost of a pattern using compression-based approach.
    
    μ-cost measures the information content (compressibility) of the pattern.
    Structured patterns should compress better and have lower μ-cost.
    
    We use several measures:
    1. Entropy: -Σ p(x) log₂ p(x)
    2. Run-length encoding efficiency
    3. Fourier spectrum concentration
    
    Args:
        pattern: Pattern to analyze
        
    Returns:
        μ-cost in bits
    """
    data = pattern.data.flatten()
    n = len(data)
    
    # 1. Shannon entropy
    hist, _ = np.histogram(data, bins=10, range=(0, 1))
    hist = hist / hist.sum()
    hist = hist[hist > 0]  # Remove zeros
    entropy = -np.sum(hist * np.log2(hist))
    entropy_bits = entropy * n
    
    # 2. Run-length encoding efficiency
    # Count runs of consecutive same values
    if n > 1:
        changes = np.sum(np.diff(data) != 0)
        rle_ratio = changes / n
    else:
        rle_ratio = 1.0
    
    # Lower ratio = more compressible
    rle_bits = rle_ratio * n
    
    # 3. Fourier spectrum concentration
    # Structured patterns have concentrated spectra
    fft = np.fft.fft2(pattern.data)
    power = np.abs(fft) ** 2
    power_sorted = np.sort(power.flatten())[::-1]
    
    # Compute concentration: how much power in top 10% coefficients
    top_10_percent = int(0.1 * len(power_sorted))
    concentration = np.sum(power_sorted[:top_10_percent]) / np.sum(power_sorted)
    
    # Higher concentration = more structured = lower cost
    fourier_bits = (1 - concentration) * n
    
    # Combined μ-cost (weighted average)
    mu_cost = 0.5 * entropy_bits + 0.3 * rle_bits + 0.2 * fourier_bits
    
    # Normalize by pattern size
    mu_cost_normalized = mu_cost / n * 1000  # bits per 1000 pixels
    
    return mu_cost_normalized


def generate_all_patterns() -> List[Pattern]:
    """Generate all pattern types for benchmarking."""
    patterns = []
    
    # Structured patterns
    print("Generating structured patterns...")
    
    print("  1. Reaction-diffusion (Gray-Scott)...")
    patterns.append(reaction_diffusion_gray_scott(size=128, steps=5000))
    
    print("  2. Cellular automaton (Game of Life)...")
    patterns.append(cellular_automaton_life(size=128, steps=100))
    
    print("  3. Spiral patterns...")
    patterns.append(cellular_automaton_spiral(size=128, arms=3))
    patterns.append(cellular_automaton_spiral(size=128, arms=5))
    
    print("  4. Phyllotaxis (golden angle)...")
    patterns.append(phyllotaxis_pattern(size=128, n_points=500))
    
    # Random patterns (negative controls)
    print("Generating random patterns...")
    patterns.append(random_pattern(size=128, density=0.3, seed=42))
    patterns.append(random_pattern(size=128, density=0.5, seed=43))
    patterns.append(random_pattern(size=128, density=0.7, seed=44))
    
    return patterns


def analyze_patterns(output_file: Path):
    """
    Generate and analyze all patterns, measuring μ-cost.
    """
    print("="*60)
    print("PATTERN FORMATION ANALYSIS")
    print("="*60)
    
    patterns = generate_all_patterns()
    
    results = []
    
    print("\n" + "="*60)
    print("ANALYZING PATTERNS")
    print("="*60)
    
    for pattern in patterns:
        print(f"\n{pattern.name}:")
        print(f"  Type: {'Structured' if pattern.is_structured else 'Random'}")
        print(f"  Size: {pattern.data.shape}")
        print(f"  Description: {pattern.description}")
        
        # Compute μ-cost
        mu_cost = compute_mu_cost(pattern)
        print(f"  μ-cost: {mu_cost:.2f} bits/1000px")
        
        # Compute statistics
        mean_val = np.mean(pattern.data)
        std_val = np.std(pattern.data)
        
        results.append({
            'pattern': pattern.name,
            'type': 'structured' if pattern.is_structured else 'random',
            'size': pattern.data.shape[0],
            'mean_value': mean_val,
            'std_value': std_val,
            'mu_cost': mu_cost,
            'description': pattern.description
        })
    
    # Save results
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w', newline='') as f:
        fieldnames = ['pattern', 'type', 'size', 'mean_value', 'std_value', 'mu_cost', 'description']
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(results)
    
    print(f"\n{'='*60}")
    print(f"Results saved to: {output_file}")
    print(f"{'='*60}")
    
    # Summary statistics
    print("\nSUMMARY STATISTICS")
    print("="*60)
    
    structured = [r for r in results if r['type'] == 'structured']
    random_results = [r for r in results if r['type'] == 'random']
    
    if structured:
        avg_mu_structured = np.mean([r['mu_cost'] for r in structured])
        print(f"Structured patterns:")
        print(f"  Count: {len(structured)}")
        print(f"  Average μ-cost: {avg_mu_structured:.2f} bits/1000px")
        for r in structured:
            print(f"    {r['pattern']}: {r['mu_cost']:.2f}")
    
    if random_results:
        avg_mu_random = np.mean([r['mu_cost'] for r in random_results])
        print(f"\nRandom patterns:")
        print(f"  Count: {len(random_results)}")
        print(f"  Average μ-cost: {avg_mu_random:.2f} bits/1000px")
        for r in random_results:
            print(f"    {r['pattern']}: {r['mu_cost']:.2f}")
    
    # Statistical test
    if structured and random_results:
        mu_structured = [r['mu_cost'] for r in structured]
        mu_random = [r['mu_cost'] for r in random_results]
        
        print(f"\n{'='*60}")
        print("H3 VALIDATION TEST")
        print("="*60)
        print(f"Question: Do structured patterns have lower μ-cost than random?")
        print(f"Structured avg: {avg_mu_structured:.2f} bits/1000px")
        print(f"Random avg: {avg_mu_random:.2f} bits/1000px")
        print(f"Difference: {avg_mu_random - avg_mu_structured:.2f} bits/1000px")
        
        if avg_mu_structured < avg_mu_random:
            print(f"✓ YES: Structured patterns have {avg_mu_random - avg_mu_structured:.2f} bits/1000px lower μ-cost")
            print("H3 VALIDATED: μ captures pattern regularity")
        else:
            print(f"✗ NO: Random patterns have lower μ-cost")
            print("H3 NOT SUPPORTED by this test")


def main():
    parser = argparse.ArgumentParser(description='Pattern formation simulator')
    parser.add_argument(
        '--output',
        type=Path,
        default=Path('artifacts/pattern_results.csv'),
        help='Output CSV file for results'
    )
    
    args = parser.parse_args()
    
    analyze_patterns(args.output)


if __name__ == '__main__':
    main()
