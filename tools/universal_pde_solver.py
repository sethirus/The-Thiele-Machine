#!/usr/bin/env python3
"""
Universal MDL PDE Solver: Compare Real vs Complex representations

This tool applies a simple MDL + MSE comparison to decide whether a
real-valued model (classical-like) or a complex-valued Schrodinger model
(quantum) better compresses the observed lattice evolution data.

It relies on the model candidate definitions and fitting routines in
`tools/schrodinger_equation_derivation.py`.
"""
from __future__ import annotations

from pathlib import Path
from typing import Tuple
import numpy as np

from tools.schrodinger_equation_derivation import (
    enumerate_models,
    FittingResult,
    ModelCandidate,
    fit_model,
)


def compare_real_vs_complex(evolution: np.ndarray, V: np.ndarray, dx: float) -> Tuple[FittingResult, FittingResult]:
    """Fit a simple real-only model and the full Schrödinger model and compare MDL.

    Returns a tuple (real_result, complex_result).
    """
    models = enumerate_models()
    # Find local_decoupled (real-like baseline) and full_schrodinger
    real_model = next((m for m in models if m.name == "local_decoupled"), None)
    complex_model = next((m for m in models if m.name == "full_schrodinger"), None)

    if real_model is None or complex_model is None:
        raise RuntimeError("Required model templates not found in enumeration")

    real_result = fit_model(evolution, V, dx, real_model)
    complex_result = fit_model(evolution, V, dx, complex_model)

    return real_result, complex_result


if __name__ == "__main__":
    print("This module is intended to be used programmatically by the Schrodinger derivation script.")
    # Minimal demo: generate small data and run comparison
    from tools.schrodinger_equation_derivation import SchrodingerModel
    model = SchrodingerModel(lattice_size=64, mass=1.0, dt=0.01, dx=1.0, potential_kind="harmonic")
    evolution = model.generate_evolution(100, seed=42)
    V = model.get_potential()
    real_result, complex_result = compare_real_vs_complex(evolution, V, 1.0)

    print(f"[REAL]    MSE: {real_result.rms_error_total:.2e} | Total Cost: {real_result.mu_total:.0f} bits")
    print(f"[COMPLEX] MSE: {complex_result.rms_error_total:.2e} | Total Cost: {complex_result.mu_total:.0f} bits")
    advantage = real_result.mu_total - complex_result.mu_total
    if advantage > 0:
        print(f">>> RESULT: SYSTEM IS QUANTUM/COMPLEX (Advantage: {advantage:.0f} bits)")
    else:
        print(f">>> RESULT: SYSTEM IS CLASSICAL/REAL (Advantage: {-advantage:.0f} bits)")
