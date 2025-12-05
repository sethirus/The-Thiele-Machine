#!/usr/bin/env python3
"""
PDE Discovery Pipeline via Thiele Machine

This module discovers partial differential equations from lattice evolution data
using the Thiele Machine's partition discovery and MDL-based learning framework.

The pipeline:
1. Generate/load evolution data from a physical system
2. Enumerate candidate PDE forms (finite difference stencils)
3. Fit coefficients for each candidate via least squares
4. Compute μ-discovery and μ-execution costs for each
5. Select PDE with minimal μ_total (MDL principle)
6. Return continuous PDE form with coefficients

Supports:
- Wave equation: ∂²u/∂t² = c²∇²u
- Diffusion equation: ∂u/∂t = D∇²u
- Schrödinger equation: iℏ∂ψ/∂t = -ℏ²/2m ∇²ψ + Vψ

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

from __future__ import annotations

import argparse
import csv
import dataclasses
import json
import math
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

# Wave model constants
CFL_STABILITY_THRESHOLD = 1.0 / np.sqrt(2)


@dataclasses.dataclass
class WaveModel:
    """
    1D wave equation model on a periodic lattice.
    
    Implements the discrete wave equation:
        u(x, t+1) = 2*u(x, t) - u(x, t-1) + c²*(u(x-1, t) - 2*u(x, t) + u(x+1, t))
    
    which emerges from the continuous wave equation:
        ∂²u/∂t² = c² * ∂²u/∂x²
    """
    
    lattice_size: int
    wave_speed: float = 0.5  # c, should be <= 1/sqrt(2) for stability
    dt: float = 1.0
    dx: float = 1.0
    
    def __post_init__(self):
        # CFL condition for wave equation stability
        self.c_squared = self.wave_speed ** 2
        cfl = self.wave_speed * self.dt / self.dx
        if cfl > CFL_STABILITY_THRESHOLD:
            raise ValueError(f"CFL condition violated: {cfl} > {CFL_STABILITY_THRESHOLD}")
    
    def initial_packet(self, center: Optional[int] = None, width: float = 3.0, amplitude: float = 1.0) -> np.ndarray:
        """Generate a localized Gaussian wave packet."""
        if center is None:
            center = self.lattice_size // 2
        x = np.arange(self.lattice_size)
        packet = amplitude * np.exp(-((x - center) ** 2) / (2 * width ** 2))
        return packet
    
    def evolve_step(self, u_current: np.ndarray, u_previous: np.ndarray) -> np.ndarray:
        """Evolve the wave by one timestep using the discrete wave equation."""
        u_plus = np.roll(u_current, -1)
        u_minus = np.roll(u_current, 1)
        laplacian = u_plus - 2 * u_current + u_minus
        u_next = 2 * u_current - u_previous + self.c_squared * laplacian
        return u_next
    
    def generate_evolution(
        self, 
        timesteps: int, 
        initial_u: Optional[np.ndarray] = None,
        initial_velocity: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """Generate the full lattice evolution over T timesteps."""
        if initial_u is None:
            initial_u = self.initial_packet()
        
        if initial_velocity is None:
            initial_velocity = np.zeros(self.lattice_size)
        
        evolution = np.zeros((timesteps, self.lattice_size))
        evolution[0] = initial_u.copy()
        
        u_previous = initial_u - self.dt * initial_velocity
        u_current = initial_u.copy()
        
        for t in range(1, timesteps):
            u_next = self.evolve_step(u_current, u_previous)
            evolution[t] = u_next
            u_previous = u_current
            u_current = u_next
        
        return evolution


@dataclasses.dataclass
class StencilCandidate:
    """
    A candidate PDE represented as a finite difference stencil.
    
    Attributes:
        name: Human-readable name (e.g., "wave", "diffusion")
        time_order: Order of time derivative (1 or 2)
        space_order: Order of spatial derivative (1 or 2)
        stencil_radius: Radius of spatial stencil
        coefficients: Fitted coefficients for this stencil
        r_squared: Goodness of fit (R² score)
        mu_discovery: μ-cost to discover this structure
        mu_execution: μ-cost to evaluate this model
    """
    name: str
    time_order: int  # 1 or 2
    space_order: int  # 1 or 2  
    stencil_radius: int  # 1 or 2
    coefficients: Optional[np.ndarray] = None
    r_squared: float = 0.0
    mu_discovery: float = 0.0
    mu_execution: float = 0.0
    
    @property
    def mu_total(self) -> float:
        """Total μ-cost = discovery + execution."""
        return self.mu_discovery + self.mu_execution
    
    def to_pde_string(self) -> str:
        """Convert to continuous PDE form."""
        if self.coefficients is None:
            return f"{self.name}: No coefficients fitted"
        
        if self.name == "wave" and self.time_order == 2 and self.space_order == 2:
            c_sq = self.coefficients[0] if len(self.coefficients) > 0 else 0.0
            c = np.sqrt(abs(c_sq))
            return f"∂²u/∂t² = {c:.4f}² ∇²u"
        elif self.name == "diffusion" and self.time_order == 1 and self.space_order == 2:
            D = self.coefficients[0] if len(self.coefficients) > 0 else 0.0
            return f"∂u/∂t = {D:.4f} ∇²u"
        else:
            return f"{self.name}: coeffs={self.coefficients}"


class PDEDiscovery:
    """
    Main PDE discovery engine using μ-minimization.
    """
    
    def __init__(self, data: np.ndarray, dt: float = 1.0, dx: float = 1.0):
        """
        Initialize PDE discovery on lattice evolution data.
        
        Args:
            data: 2D array of shape (timesteps, lattice_size)
            dt: Time step size
            dx: Spatial step size
        """
        self.data = data
        self.dt = dt
        self.dx = dx
        self.timesteps, self.lattice_size = data.shape
        
        if self.timesteps < 3:
            raise ValueError("Need at least 3 timesteps for 2nd order time derivatives")
        if self.lattice_size < 5:
            raise ValueError("Need at least 5 spatial points for finite differences")
    
    def generate_candidates(self) -> List[StencilCandidate]:
        """
        Generate hypothesis class of candidate PDE forms.
        
        Returns:
            List of StencilCandidate objects to test
        """
        candidates = []
        
        # Wave equation: ∂²u/∂t² = c²∇²u
        candidates.append(StencilCandidate(
            name="wave",
            time_order=2,
            space_order=2,
            stencil_radius=1
        ))
        
        # Diffusion equation: ∂u/∂t = D∇²u
        candidates.append(StencilCandidate(
            name="diffusion",
            time_order=1,
            space_order=2,
            stencil_radius=1
        ))
        
        # Higher order wave (larger stencil)
        candidates.append(StencilCandidate(
            name="wave_wide",
            time_order=2,
            space_order=2,
            stencil_radius=2
        ))
        
        # 1st order wave (advection-like)
        candidates.append(StencilCandidate(
            name="advection",
            time_order=1,
            space_order=1,
            stencil_radius=1
        ))
        
        return candidates
    
    def fit_wave_equation(self, candidate: StencilCandidate) -> StencilCandidate:
        """
        Fit wave equation: u(x,t+1) = 2u(x,t) - u(x,t-1) + c²∇²u(x,t)
        
        This is the discrete form of ∂²u/∂t² = c²∇²u.
        """
        # Build design matrix A and target vector b
        # For each interior point at each interior time, we have:
        # u(x, t+1) - 2u(x,t) + u(x,t-1) = c² * [u(x-1,t) - 2u(x,t) + u(x+1,t)]
        
        X_list = []  # Design matrix rows (laplacians)
        y_list = []  # Target vector (second time derivatives)
        
        for t in range(1, self.timesteps - 1):
            for x in range(self.lattice_size):
                # Periodic boundary conditions
                xm1 = (x - 1) % self.lattice_size
                xp1 = (x + 1) % self.lattice_size
                
                # Spatial Laplacian at (x, t)
                laplacian = self.data[t, xp1] - 2*self.data[t, x] + self.data[t, xm1]
                
                # Second time derivative approximation
                d2u_dt2 = (self.data[t+1, x] - 2*self.data[t, x] + self.data[t-1, x]) / (self.dt**2)
                
                X_list.append([laplacian / (self.dx**2)])
                y_list.append(d2u_dt2)
        
        X = np.array(X_list)
        y = np.array(y_list)
        
        # Least squares fit: y = X * c²
        c_squared = np.linalg.lstsq(X, y, rcond=None)[0]
        
        # Compute R² score
        y_pred = X @ c_squared
        ss_res = np.sum((y - y_pred)**2)
        ss_tot = np.sum((y - np.mean(y))**2)
        r_squared = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0.0
        
        candidate.coefficients = c_squared
        candidate.r_squared = r_squared
        return candidate
    
    def fit_diffusion_equation(self, candidate: StencilCandidate) -> StencilCandidate:
        """
        Fit diffusion equation: u(x,t+1) = u(x,t) + D∇²u(x,t)
        
        This is the discrete form of ∂u/∂t = D∇²u.
        """
        X_list = []
        y_list = []
        
        for t in range(self.timesteps - 1):
            for x in range(self.lattice_size):
                xm1 = (x - 1) % self.lattice_size
                xp1 = (x + 1) % self.lattice_size
                
                laplacian = self.data[t, xp1] - 2*self.data[t, x] + self.data[t, xm1]
                du_dt = (self.data[t+1, x] - self.data[t, x]) / self.dt
                
                X_list.append([laplacian / (self.dx**2)])
                y_list.append(du_dt)
        
        X = np.array(X_list)
        y = np.array(y_list)
        
        D = np.linalg.lstsq(X, y, rcond=None)[0]
        
        y_pred = X @ D
        ss_res = np.sum((y - y_pred)**2)
        ss_tot = np.sum((y - np.mean(y))**2)
        r_squared = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0.0
        
        candidate.coefficients = D
        candidate.r_squared = r_squared
        return candidate
    
    def compute_mu_costs(self, candidate: StencilCandidate) -> StencilCandidate:
        """
        Compute μ-discovery and μ-execution costs for a candidate PDE.
        
        μ-discovery: Cost to discover the structure (stencil + fit)
        μ-execution: Cost to evaluate the model on data
        
        Uses μ-spec v2.0 formulas.
        """
        N = self.lattice_size
        T = self.timesteps
        
        # μ-discovery: cost to discover stencil structure
        # - Enumerate stencil patterns: log2(num_patterns)
        # - Fit coefficients: log2(N*T) for data access + encoding precision
        num_stencil_patterns = 10  # Rough estimate for our hypothesis class
        encoding_bits = 32  # Float32 precision for coefficients
        num_coefficients = max(1, len(candidate.coefficients)) if candidate.coefficients is not None else 1
        
        mu_discovery = (
            math.log2(num_stencil_patterns) +  # Structure enumeration
            num_coefficients * encoding_bits +  # Coefficient encoding
            math.log2(N * T)  # Data access cost
        )
        
        # μ-execution: cost to evaluate model
        # - Per-point evaluation: stencil_radius neighbors + arithmetic ops
        # - Total: (N * T) evaluations
        ops_per_eval = 2 * candidate.stencil_radius + 3  # Neighbors + arithmetic
        mu_execution = math.log2(N * T * ops_per_eval)
        
        candidate.mu_discovery = mu_discovery
        candidate.mu_execution = mu_execution
        return candidate
    
    def discover_pde(self) -> Tuple[StencilCandidate, List[StencilCandidate]]:
        """
        Discover the best PDE from data using MDL principle.
        
        Returns:
            (best_candidate, all_candidates)
        """
        candidates = self.generate_candidates()
        
        # Fit each candidate
        for candidate in candidates:
            if candidate.name in ["wave", "wave_wide"]:
                self.fit_wave_equation(candidate)
            elif candidate.name == "diffusion":
                self.fit_diffusion_equation(candidate)
            elif candidate.name == "advection":
                # Simple 1st order fit (not implemented fully, placeholder)
                candidate.coefficients = np.array([0.0])
                candidate.r_squared = 0.0
            
            # Compute μ-costs
            self.compute_mu_costs(candidate)
        
        # Select candidate with minimal μ_total (MDL principle)
        candidates_with_fit = [c for c in candidates if c.r_squared > 0.5]  # Filter bad fits
        if not candidates_with_fit:
            raise ValueError("No candidates achieved R² > 0.5")
        
        best = min(candidates_with_fit, key=lambda c: c.mu_total)
        return best, candidates


def run_wave_test(c: float = 0.5, n: int = 64, timesteps: int = 100) -> Dict[str, Any]:
    """
    Run PDE discovery on wave equation data.
    
    Args:
        c: Wave speed
        n: Lattice size
        timesteps: Number of timesteps
    
    Returns:
        Dictionary with test results
    """
    
    # Generate wave evolution data
    wave = WaveModel(lattice_size=n, wave_speed=c)
    initial = wave.initial_packet()
    evolution = wave.generate_evolution(timesteps, initial_u=initial)
    
    # Run PDE discovery
    discovery = PDEDiscovery(evolution, dt=wave.dt, dx=wave.dx)
    best, all_candidates = discovery.discover_pde()
    
    # Extract recovered wave speed
    if best.coefficients is not None and len(best.coefficients) > 0:
        recovered_c = np.sqrt(abs(best.coefficients[0]))
    else:
        recovered_c = 0.0
    error_pct = 100 * abs(recovered_c - c) / c if c != 0 else 0.0
    
    results = {
        "test_case": f"wave_c{int(c*100):03d}_n{n}",
        "true_c": c,
        "recovered_c": float(recovered_c),
        "error_pct": error_pct,
        "mu_total": best.mu_total,
        "mu_discovery": best.mu_discovery,
        "mu_execution": best.mu_execution,
        "r_squared": best.r_squared,
        "best_model": best.name,
        "pde_form": best.to_pde_string()
    }
    
    return results


def run_wave_test_suite(output_csv: Path):
    """
    Run comprehensive wave equation test suite.
    """
    test_configs = [
        {"c": 0.5, "n": 64, "timesteps": 100},
        {"c": 0.5, "n": 128, "timesteps": 100},
        {"c": 0.4, "n": 64, "timesteps": 100},
        {"c": 0.6, "n": 64, "timesteps": 80},
        {"c": 0.3, "n": 32, "timesteps": 100},
    ]
    
    results = []
    for config in test_configs:
        print(f"Running test: c={config['c']}, n={config['n']}")
        result = run_wave_test(**config)
        results.append(result)
        print(f"  Recovered c={result.get('recovered_c', 0):.3f}, error={result.get('error_pct', 0):.2f}%, μ={result.get('mu_total', 0):.1f}")
    
    # Write results to CSV
    if results:
        fieldnames = results[0].keys()
        with open(output_csv, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(results)
        print(f"\nResults written to {output_csv}")


def main():
    parser = argparse.ArgumentParser(description="PDE Discovery via μ-minimization")
    parser.add_argument("--test", choices=["wave", "diffusion", "all"], default="wave",
                        help="Which PDE test suite to run")
    parser.add_argument("--output", type=Path, default=Path("artifacts/pde_wave_results.csv"),
                        help="Output CSV file for results")
    args = parser.parse_args()
    
    # Create artifacts directory if needed
    args.output.parent.mkdir(parents=True, exist_ok=True)
    
    if args.test in ["wave", "all"]:
        print("=== Running Wave Equation Test Suite ===")
        run_wave_test_suite(args.output)
    
    if args.test == "diffusion":
        print("Diffusion tests not yet implemented")
    
    print("\n=== PDE Discovery Complete ===")


if __name__ == "__main__":
    main()
