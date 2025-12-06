import numpy as np
from tools.universal_pde_solver import compare_real_vs_complex
from tools.schrodinger_equation_derivation import SchrodingerModel


def test_compare_real_vs_complex_prefers_schrodinger():
    # Generate a small Schrödinger evolution with a harmonic potential
    model = SchrodingerModel(lattice_size=16, mass=1.0, dt=0.005, dx=1.0, potential_kind="harmonic")
    evolution = model.generate_evolution(timesteps=12, seed=42)
    V = model.get_potential()

    real_result, complex_result = compare_real_vs_complex(evolution, V, model.dx)

    # Validate outputs are sane
    assert real_result.model.name == "local_decoupled"
    assert complex_result.model.name == "full_schrodinger"

    # Complex model should yield lower μ-total and lower RMS error for Schrödinger data
    assert complex_result.mu_total < real_result.mu_total
    assert complex_result.rms_error_total <= real_result.rms_error_total
