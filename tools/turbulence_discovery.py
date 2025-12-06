#!/usr/bin/env python3
"""
Turbulence Closure Discovery via μ-Minimization

Applies the Thiele Machine framework to 2D turbulent flows to discover
effective closure models for reduced-order modeling.

Key idea:
- Full 2D Navier-Stokes simulation is high-dimensional (expensive)
- μ-minimization should discover effective low-dimensional models
- Compare discovered closures to classical turbulence closures

System: 2D Navier-Stokes with periodic boundary conditions
"""

import numpy as np
import time
from typing import Dict, Tuple, List
from thielecpu.mdl import compute_mu_cost_rom as compute_mu_cost_rom_helper
import csv


def simulate_2d_navier_stokes(nx: int, ny: int, nt: int, Re: float, 
                               dt: float = 0.001, force_scale: float = 0.1,
                               seed: int = 42) -> Tuple[np.ndarray, np.ndarray]:
    """
    Simulate 2D Navier-Stokes equations using spectral method.
    
    Equations:
        ∂u/∂t + (u·∇)u = -∇p + (1/Re)∇²u + f
        ∇·u = 0
    
    Args:
        nx, ny: Grid resolution
        nt: Number of timesteps
        Re: Reynolds number
        dt: Timestep
        force_scale: Forcing amplitude
        seed: Random seed
        
    Returns:
        vorticity: (nt, nx, ny) vorticity field
        energy: (nt,) kinetic energy timeseries
    """
    np.random.seed(seed)
    
    # Setup spectral grid
    kx = np.fft.fftfreq(nx, 1.0/nx) * 2 * np.pi
    ky = np.fft.fftfreq(ny, 1.0/ny) * 2 * np.pi
    KX, KY = np.meshgrid(kx, ky, indexing='ij')
    K2 = KX**2 + KY**2
    K2[0, 0] = 1.0  # Avoid division by zero
    
    # Initialize vorticity field (random initial condition)
    vorticity = np.random.randn(nx, ny) * 0.1
    w_hat = np.fft.fft2(vorticity)
    
    # Storage
    vorticity_history = np.zeros((nt, nx, ny))
    energy_history = np.zeros(nt)
    
    # Time integration (pseudo-spectral)
    nu = 1.0 / Re
    
    for n in range(nt):
        # Store current state
        vorticity_history[n] = vorticity
        energy_history[n] = np.sum(vorticity**2) / (nx * ny)
        
        # Compute velocity from vorticity: u = ∇×ω
        psi_hat = -w_hat / K2
        u_hat = 1j * KY * psi_hat
        v_hat = -1j * KX * psi_hat
        
        u = np.real(np.fft.ifft2(u_hat))
        v = np.real(np.fft.ifft2(v_hat))
        
        # Nonlinear term: (u·∇)ω
        dwdx = np.real(np.fft.ifft2(1j * KX * w_hat))
        dwdy = np.real(np.fft.ifft2(1j * KY * w_hat))
        nonlinear = u * dwdx + v * dwdy
        
        # Add forcing (large-scale)
        forcing = force_scale * np.sin(2 * np.pi * np.arange(nx)[:, None] / nx) * \
                  np.cos(2 * np.pi * np.arange(ny)[None, :] / ny)
        
        # Time step (RK2)
        # Stage 1
        rhs_hat = np.fft.fft2(-nonlinear + forcing) - nu * K2 * w_hat
        w_hat_mid = w_hat + 0.5 * dt * rhs_hat
        
        # Stage 2
        vorticity_mid = np.real(np.fft.ifft2(w_hat_mid))
        psi_hat_mid = -w_hat_mid / K2
        u_mid = np.real(np.fft.ifft2(1j * KY * psi_hat_mid))
        v_mid = np.real(np.fft.ifft2(-1j * KX * psi_hat_mid))
        dwdx_mid = np.real(np.fft.ifft2(1j * KX * w_hat_mid))
        dwdy_mid = np.real(np.fft.ifft2(1j * KY * w_hat_mid))
        nonlinear_mid = u_mid * dwdx_mid + v_mid * dwdy_mid
        
        rhs_hat_mid = np.fft.fft2(-nonlinear_mid + forcing) - nu * K2 * w_hat_mid
        w_hat = w_hat + dt * rhs_hat_mid
        
        vorticity = np.real(np.fft.ifft2(w_hat))
    
    return vorticity_history, energy_history


def coarse_grain_field(field: np.ndarray, factor: int) -> np.ndarray:
    """
    Coarse-grain a 2D field by averaging over blocks.
    
    Args:
        field: (nx, ny) fine-scale field
        factor: Coarse-graining factor
        
    Returns:
        coarse: (nx//factor, ny//factor) coarse field
    """
    nx, ny = field.shape
    nx_c = nx // factor
    ny_c = ny // factor
    
    coarse = np.zeros((nx_c, ny_c))
    for i in range(nx_c):
        for j in range(ny_c):
            coarse[i, j] = np.mean(field[i*factor:(i+1)*factor, j*factor:(j+1)*factor])
    
    return coarse


def compute_coarse_grained_error(u: np.ndarray, v: np.ndarray, factor: int) -> float:
    """
    Compute the prediction error from coarse-graining velocity fields.

    Args:
        u: (nx, ny) x-velocity field
        v: (nx, ny) y-velocity field
        factor: Coarse-graining factor

    Returns:
        error: RMS relative error from coarse-graining
    """
    # Coarse-grain the fields
    u_coarse = coarse_grain_field(u, factor)
    v_coarse = coarse_grain_field(v, factor)

    # Reconstruct by upsampling (simple replication)
    nx, ny = u.shape
    u_recon = np.repeat(np.repeat(u_coarse, factor, axis=0), factor, axis=1)
    v_recon = np.repeat(np.repeat(v_coarse, factor, axis=0), factor, axis=1)

    # Ensure same shape
    u_recon = u_recon[:nx, :ny]
    v_recon = v_recon[:nx, :ny]

    # Compute RMS error
    error_u = np.sqrt(np.mean((u - u_recon)**2))
    error_v = np.sqrt(np.mean((v - v_recon)**2))
    norm_u = np.sqrt(np.mean(u**2))
    norm_v = np.sqrt(np.mean(v**2))

    relative_error = np.sqrt((error_u**2 + error_v**2) / (norm_u**2 + norm_v**2))

    return relative_error


def compute_mu_cost_turbulence(nx: int, ny: int, nt: int, factor: int) -> float:
    """
    Compute μ-cost for turbulence simulation with coarse-graining.

    Args:
        nx, ny: Fine grid resolution
        nt: Number of timesteps
        factor: Coarse-graining factor

    Returns:
        mu_cost: Total μ-cost in bits
    """
    # Full DOF
    dof_fine = nx * ny * nt

    # Coarse DOF
    dof_coarse = (nx // factor) * (ny // factor) * nt

    # μ-cost includes:
    # 1. Encoding the coarse-graining operation (log2 of compression ratio)
    # 2. Storing coarse-grained state (64 bits per DOF)
    compression_ratio = dof_fine / dof_coarse
    mu_discovery = np.log2(compression_ratio)
    mu_execution = dof_coarse * 64  # 64-bit floats

    return mu_discovery + mu_execution


def extract_rom_features(vorticity_fine: np.ndarray, 
                         factor: int) -> Tuple[np.ndarray, np.ndarray]:
    """
    Extract reduced-order model (ROM) features via coarse-graining.
    
    Args:
        vorticity_fine: (nt, nx, ny) fine-scale vorticity
        factor: Coarse-graining factor
        
    Returns:
        vorticity_coarse: (nt, nx_c, ny_c) coarse vorticity
        features: (nt, n_features) feature vector
    """
    nt, nx, ny = vorticity_fine.shape
    nx_c = nx // factor
    ny_c = ny // factor
    
    vorticity_coarse = np.zeros((nt, nx_c, ny_c))
    
    for t in range(nt):
        vorticity_coarse[t] = coarse_grain_field(vorticity_fine[t], factor)
    
    # Features: mean, variance, gradients, energy
    features = []
    for t in range(nt):
        w_c = vorticity_coarse[t]
        feat = [
            np.mean(w_c),
            np.std(w_c),
            np.mean(np.abs(np.gradient(w_c, axis=0))),
            np.mean(np.abs(np.gradient(w_c, axis=1))),
            np.sum(w_c**2) / (nx_c * ny_c)
        ]
        features.append(feat)
    
    return vorticity_coarse, np.array(features)


def fit_rom_dynamics(features: np.ndarray, 
                     dt: float) -> Tuple[np.ndarray, float]:
    """
    Fit ROM dynamics: dX/dt = f(X)
    
    Uses simple linear dynamics: dX/dt = A·X
    
    Args:
        features: (nt, n_features) feature timeseries
        dt: Timestep
        
    Returns:
        A: (n_features, n_features) dynamics matrix
        error: Prediction error
    """
    nt, n_feat = features.shape
    
    # Finite difference: dX/dt ≈ (X[t+1] - X[t]) / dt
    X = features[:-1]  # (nt-1, n_feat)
    dXdt = (features[1:] - features[:-1]) / dt
    
    # Least squares: dX/dt = A·X  =>  A = (dX/dt) · X^T · (X·X^T)^{-1}
    # Regularized version
    A = dXdt.T @ X @ np.linalg.inv(X.T @ X + 1e-6 * np.eye(n_feat))
    
    # Compute prediction error
    dXdt_pred = (A @ X.T).T
    error = np.mean((dXdt - dXdt_pred)**2) / np.mean(dXdt**2)
    
    return A, error


def compute_mu_cost_rom(features: np.ndarray, A: np.ndarray, dt: float, dof: int, include_state_storage: bool = True, precision_bits: int = 64) -> float:
    """Delegates μ-cost computation to centralized helper in thielecpu.mdl."""
    return compute_mu_cost_rom_helper(features, A, dt, dof, include_state_storage, precision_bits)


def benchmark_closure_models(vorticity_fine: np.ndarray,
                             energy_fine: np.ndarray,
                             dt: float,
                             factors: List[int] = [2, 4, 8],
                             include_state_storage: bool = True) -> Dict:
    """
    Benchmark different closure models.
    
    Args:
        vorticity_fine: (nt, nx, ny) fine-scale vorticity
        energy_fine: (nt,) fine-scale energy
        dt: Timestep
        factors: Coarse-graining factors to test
        
    Returns:
        results: Dictionary of results for each factor
    """
    results = {}
    
    for factor in factors:
        print(f"\n{'='*60}")
        print(f"Coarse-graining factor: {factor}")
        print(f"{'='*60}")
        
        # Extract ROM features
        start_time = time.time()
        vorticity_coarse, features = extract_rom_features(vorticity_fine, factor)
        
        # Fit ROM dynamics
        A, error = fit_rom_dynamics(features, dt)
        
        # Extract coarse-grid dimensions and DOF
        nt, nx_c, ny_c = vorticity_coarse.shape
        dof = nx_c * ny_c

        # Compute μ-cost: pass DOF (coarse-grained) and include state storage
        mu_cost = compute_mu_cost_rom(features, A, dt, dof=dof, include_state_storage=include_state_storage)

        runtime = time.time() - start_time
        dof = nx_c * ny_c
        
        print(f"  DOF: {dof} (reduced from {vorticity_fine.shape[1] * vorticity_fine.shape[2]})")
        print(f"  Compression: {(vorticity_fine.shape[1] * vorticity_fine.shape[2]) / dof:.1f}×")
        print(f"  Prediction error: {error:.4f}")
        print(f"  μ-cost: {mu_cost:.2f} bits")
        print(f"  Runtime: {runtime:.4f}s")
        
        results[f"factor_{factor}"] = {
            'factor': factor,
            'dof': dof,
            'compression': (vorticity_fine.shape[1] * vorticity_fine.shape[2]) / dof,
            'error': error,
            'mu_cost': mu_cost,
            'runtime': runtime,
            'A': A,
            'features': features
        }
    
    return results


def find_mu_optimal_closure(results: Dict) -> str:
    """
    Find μ-optimal closure among candidates.
    
    Args:
        results: Dictionary of results for each factor
        
    Returns:
        best_key: Key of best (μ-optimal) closure
    """
    best_key = None
    best_mu = float('inf')
    best_error = float('inf')
    
    # Use an epsilon for μ-cost comparisons (1 bit)
    EPS_BITS = 1.0
    for key, res in results.items():
        mu = res['mu_cost']
        err = res.get('error', float('inf'))
        # Prefer strictly lower μ (always win)
        if mu < best_mu:
            best_mu = mu
            best_error = err
            best_key = key
        # If μ is effectively equal (within EPS), prefer lower error
        elif abs(mu - best_mu) <= EPS_BITS:
            if err < best_error:
                best_error = err
                best_key = key
    
    return best_key


def analyze_turbulence(nx: int = 64, ny: int = 64, nt: int = 200,
                       Re: float = 1000, dt: float = 0.001,
                       output_file: str = 'benchmarks/turbulence_results.csv',
                       include_state_storage: bool = True):
    """
    Main analysis: Discover turbulence closure via μ-minimization.
    
    Args:
        nx, ny: Grid resolution
        nt: Number of timesteps
        Re: Reynolds number
        dt: Timestep
        output_file: Path to save results
    """
    print("="*70)
    print("TURBULENCE CLOSURE DISCOVERY VIA μ-MINIMIZATION")
    print("="*70)
    print(f"\nSimulation parameters:")
    print(f"  Grid: {nx}×{ny}")
    print(f"  Timesteps: {nt}")
    print(f"  Reynolds number: {Re}")
    print(f"  dt: {dt}")
    
    # Run full simulation
    print(f"\nRunning full 2D Navier-Stokes simulation...")
    start_sim = time.time()
    vorticity, energy = simulate_2d_navier_stokes(nx, ny, nt, Re, dt)
    sim_time = time.time() - start_sim
    print(f"  Simulation complete: {sim_time:.2f}s")
    print(f"  Final energy: {energy[-1]:.4e}")
    print(f"  Energy range: [{energy.min():.4e}, {energy.max():.4e}]")
    
    # Benchmark closure models
    print(f"\n{'='*70}")
    print("BENCHMARKING CLOSURE MODELS")
    print(f"{'='*70}")
    
    factors = [2, 4, 8]
    results = benchmark_closure_models(vorticity, energy, dt, factors, include_state_storage=include_state_storage)
    
    # Find μ-optimal
    print(f"\n{'='*70}")
    print("μ-OPTIMAL CLOSURE SELECTION")
    print(f"{'='*70}")
    
    best_key = find_mu_optimal_closure(results)
    best_result = results[best_key]

    # Find best accuracy closure separately (for reporting/choice)
    best_accuracy_key = min(results.items(), key=lambda kv: kv[1]['error'])[0]
    best_accuracy_result = results[best_accuracy_key]
    
    print(f"\nμ-Optimal closure: {best_key}")
    print(f"  DOF: {best_result['dof']}")
    print(f"  Compression: {best_result['compression']:.1f}×")
    print(f"  Prediction error: {best_result['error']:.4f}")
    print(f"  μ-cost: {best_result['mu_cost']:.2f} bits")
    print(f"\nBest-accuracy closure: {best_accuracy_key}")
    print(f"  DOF: {best_accuracy_result['dof']}")
    print(f"  Compression: {best_accuracy_result['compression']:.1f}×")
    print(f"  Prediction error: {best_accuracy_result['error']:.4f}")
    print(f"  μ-cost: {best_accuracy_result['mu_cost']:.2f} bits")
    
    # Save results
    with open(output_file, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['method', 'dof', 'compression', 'error', 'mu_cost_bits', 'runtime_s'])
        
        # Full simulation baseline
        writer.writerow(['full_simulation', nx*ny, 1.0, 0.0, 
                        nx*ny*nt*64,  # Full state storage cost
                        sim_time])
        
        # Closure models
        for key, res in results.items():
            writer.writerow([key, res['dof'], res['compression'], 
                           res['error'], res['mu_cost'], res['runtime']])
    
    print(f"\n{'='*70}")
    print(f"Results saved to: {output_file}")
    print(f"{'='*70}")
    
    # Summary
    print(f"\nSUMMARY")
    print(f"{'='*70}")
    print(f"Full simulation: {nx*ny} DOF, {sim_time:.2f}s")
    print(f"μ-Optimal closure: {best_result['dof']} DOF ({best_result['compression']:.1f}× compression)")
    print(f"Prediction error: {best_result['error']:.4f}")
    print(f"μ-cost reduction: {(nx*ny*nt*64 / best_result['mu_cost']):.1f}× lower")
    print(f"\nH3 TEST: Does μ-minimization find effective turbulence closure?")
    print(f"Result: {'✓ YES' if best_result['error'] < 0.5 else '✗ NO'} "
          f"(error {best_result['error']:.1%}, threshold 50%)")
    
    return results


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description='Turbulence closure discovery via μ-minimization')
    parser.add_argument('--output', dest='output_file', default='benchmarks/turbulence_results.csv')
    parser.add_argument('--nx', type=int, default=64)
    parser.add_argument('--ny', type=int, default=64)
    parser.add_argument('--nt', type=int, default=200)
    parser.add_argument('--Re', type=float, default=1000.0)
    parser.add_argument('--dt', type=float, default=0.001)
    parser.add_argument('--include-state-storage', dest='include_state_storage', action='store_true')
    parser.add_argument('--no-state-storage', dest='include_state_storage', action='store_false')
    parser.set_defaults(include_state_storage=True)

    args = parser.parse_args()

    results = analyze_turbulence(
        nx=args.nx, ny=args.ny, nt=args.nt, Re=args.Re, dt=args.dt,
        output_file=args.output_file, include_state_storage=args.include_state_storage
    )
