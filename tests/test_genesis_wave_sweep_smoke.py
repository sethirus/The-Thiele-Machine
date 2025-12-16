from __future__ import annotations

from tools.genesis_wave_sweep import run_one


def test_genesis_wave_sweep_smoke_python_engine() -> None:
    metrics = run_one(
        seed=0,
        phase_pi_prob=0.5,
        mutation_rate=0.15,
        payoff_rule="surprise_bits",
        population=20,
        generations=6,
        rounds_per_generation=6,
        initial_fuel=40,
        regen_per_round=3,
        bet_budget_fraction=0.8,
        surprise_cost_scale=1.0,
        detectors=8,
        paths_min=2,
        paths_max=4,
        mag_scale=1.0,
        slope_window=4,
        eval_rounds=40,
        engine="python",
    )

    assert metrics.final_alive >= 0
    assert 0.0 <= metrics.final_mean_alpha <= 6.0


def test_genesis_wave_sweep_smoke_vm_engine() -> None:
    # Tiny VM-backed run to ensure we can execute via the sandboxed VM path.
    metrics = run_one(
        seed=1,
        phase_pi_prob=0.7,
        mutation_rate=0.05,
        payoff_rule="log_score",
        population=8,
        generations=3,
        rounds_per_generation=4,
        initial_fuel=32,
        regen_per_round=3,
        bet_budget_fraction=0.8,
        surprise_cost_scale=1.0,
        detectors=6,
        paths_min=2,
        paths_max=3,
        mag_scale=1.0,
        slope_window=2,
        eval_rounds=20,
        engine="vm",
    )

    assert metrics.final_alive >= 0
    assert 0.0 <= metrics.final_mean_alpha <= 6.0
