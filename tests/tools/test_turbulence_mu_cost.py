from __future__ import annotations

from pathlib import Path

import numpy as np

from tools.turbulence_discovery import (
    simulate_2d_navier_stokes,
    extract_rom_features,
    fit_rom_dynamics,
    compute_mu_cost_rom,
    find_mu_optimal_closure,
)


def _small_sim(nx=16, ny=16, nt=10, Re=100):
    vorticity, energy = simulate_2d_navier_stokes(nx, ny, nt, Re, dt=0.01, seed=1)
    return vorticity, energy


def test_mu_cost_sensitivity_with_dof():
    vorticity, energy = _small_sim()
    dt = 0.01

    mu_costs = {}
    for factor in [2, 4, 8]:
        v_c, features = extract_rom_features(vorticity, factor)
        A, error = fit_rom_dynamics(features, dt)
        dof = v_c.shape[1] * v_c.shape[2]
        mu = compute_mu_cost_rom(features, A, dt, dof=dof, include_state_storage=True)
        mu_costs[factor] = mu

    # Ensure μ-costs are not identical and monotonically non-increasing with smaller DOF
    assert len(set(mu_costs.values())) > 1
    # factor 8 has smallest DOF; its mu should be smaller than factor 2
    assert mu_costs[8] < mu_costs[2]


def test_find_mu_optimal_closure_tiebreaker():
    results = {
        'a': {'mu_cost': 1000.0, 'error': 0.5},
        'b': {'mu_cost': 1000.5, 'error': 0.3},
        'c': {'mu_cost': 999.9, 'error': 0.9},
    }

    # 'c' should be selected by mu (lowest mu)
    assert find_mu_optimal_closure(results) == 'c'

    # Now make 'a' and 'b' tied in mu but 'b' lower error
    results2 = {
        'a': {'mu_cost': 1000.0, 'error': 0.5},
        'b': {'mu_cost': 1000.0 + 0.5e-9, 'error': 0.3},
    }
    # With EPS_MARGIN = 1.0 bit, these are considered equal mu; tiebreaker should pick 'b'
    assert find_mu_optimal_closure(results2) == 'b'


def test_analyze_turbulence_returns_mu_and_accuracy():
    # Run a small-scale turbulence analysis and check best-mu and best-accuracy selections
    vorticity, energy = _small_sim(nx=32, ny=32, nt=20, Re=200)
    dt = 0.01

    # Use the functions directly to avoid file output
    from tools.turbulence_discovery import benchmark_closure_models, find_mu_optimal_closure

    results = benchmark_closure_models(vorticity, energy, dt, factors=[2, 4, 8])
    mu_key = find_mu_optimal_closure(results)
    # The mu-optimal should be the smallest DOF (factor 8) when state storage included
    assert mu_key == 'factor_8'
    # Best-accuracy should be factor_2
    assert min(results.items(), key=lambda kv: kv[1]['error'])[0] == 'factor_2'


def test_include_state_storage_toggle_changes_mu():
    vorticity, energy = _small_sim(nx=32, ny=32, nt=20, Re=200)
    dt = 0.01
    from tools.turbulence_discovery import benchmark_closure_models

    results_with = benchmark_closure_models(vorticity, energy, dt, factors=[2, 4, 8], include_state_storage=True)
    results_without = benchmark_closure_models(vorticity, energy, dt, factors=[2, 4, 8], include_state_storage=False)

    mus_with = set(res['mu_cost'] for res in results_with.values())
    mus_without = set(res['mu_cost'] for res in results_without.values())

    # With state storage included, μ-costs should differ across factors
    assert len(mus_with) > 1
    # Without state storage, μ-costs should be identical across factors (dominated by feature-space costs)
    assert len(mus_without) == 1
