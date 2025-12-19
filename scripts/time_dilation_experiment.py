#!/usr/bin/env python3
"""
Time-dilation harness based on μ-budget conservation.

We model a module with a fixed μ budget per global tick. The budget can be
spent on communication (EMIT-like payloads) or on local computation. If the
module spends more on communication, less budget remains for computation,
causing its local "clock" (compute steps per tick) to slow down. This mirrors
the No Free Insight constraint: μ is conserved, so spending it on signal
propagation reduces the μ available for internal evolution.

Running this script produces ``results/time_dilation_experiment.json`` with a
set of scenarios varying the communication payload size while holding the
budget constant. Each scenario records the μ spent on communication, μ spent
on computation, total μ, and the observed compute rate per tick.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

from thielecpu.state import MuLedger

REPO_ROOT = Path(__file__).resolve().parent.parent
RESULTS_PATH = REPO_ROOT / "results" / "time_dilation_experiment.json"


@dataclass
class ScenarioConfig:
    """Configuration for a single communication/computation trade-off run."""

    name: str
    budget_per_tick: int
    comm_bits_per_tick: int
    compute_cost: int = 1
    ticks: int = 64


@dataclass
class ScenarioResult:
    """Outcome metrics for a time-dilation scenario."""

    name: str
    budget_per_tick: int
    comm_bits_per_tick: int
    compute_cost: int
    ticks: int
    comm_mu: int
    compute_mu: int
    mu_total: int
    compute_steps: int

    @property
    def compute_rate(self) -> float:
        return self.compute_steps / float(self.ticks)


def _run_scenario(config: ScenarioConfig) -> ScenarioResult:
    """Simulate μ spending across ticks with prioritized communication."""

    ledger = MuLedger()
    backlog_bits = 0  # communication bits queued for emission
    compute_steps = 0
    comm_mu = 0
    compute_mu = 0

    for _ in range(config.ticks):
        remaining_budget = config.budget_per_tick
        backlog_bits += config.comm_bits_per_tick

        # Spend budget on communication first (signal propagation).
        comm_spend = min(backlog_bits, remaining_budget)
        backlog_bits -= comm_spend
        remaining_budget -= comm_spend
        comm_mu += comm_spend
        ledger.mu_execution += comm_spend

        # Use any remaining budget for local computation (vm_step work).
        if remaining_budget >= config.compute_cost:
            steps = remaining_budget // config.compute_cost
            compute_steps += steps
            compute_mu += steps * config.compute_cost
            ledger.mu_execution += steps * config.compute_cost

    return ScenarioResult(
        name=config.name,
        budget_per_tick=config.budget_per_tick,
        comm_bits_per_tick=config.comm_bits_per_tick,
        compute_cost=config.compute_cost,
        ticks=config.ticks,
        comm_mu=comm_mu,
        compute_mu=compute_mu,
        mu_total=ledger.total,
        compute_steps=compute_steps,
    )


def run_experiment(write: bool = True) -> Dict[str, object]:
    """Execute the time-dilation scenarios and optionally persist JSON."""

    scenarios = [
        ScenarioConfig(name="baseline_no_comm", budget_per_tick=32, comm_bits_per_tick=0),
        ScenarioConfig(name="light_comm", budget_per_tick=32, comm_bits_per_tick=4),
        ScenarioConfig(name="moderate_comm", budget_per_tick=32, comm_bits_per_tick=12),
        ScenarioConfig(name="heavy_comm", budget_per_tick=32, comm_bits_per_tick=24),
    ]

    results: List[ScenarioResult] = [_run_scenario(cfg) for cfg in scenarios]

    payload = {
        "description": "Compute vs communication trade-off under fixed μ budget",
        "scenarios": [
            {
                "name": r.name,
                "budget_per_tick": r.budget_per_tick,
                "comm_bits_per_tick": r.comm_bits_per_tick,
                "compute_cost": r.compute_cost,
                "ticks": r.ticks,
                "comm_mu": r.comm_mu,
                "compute_mu": r.compute_mu,
                "mu_total": r.mu_total,
                "compute_steps": r.compute_steps,
                "compute_rate": r.compute_rate,
            }
            for r in results
        ],
    }

    if write:
        RESULTS_PATH.parent.mkdir(parents=True, exist_ok=True)
        RESULTS_PATH.write_text(json.dumps(payload, indent=2))

    return payload


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the μ-budget time dilation harness")
    parser.add_argument(
        "--out",
        type=Path,
        default=RESULTS_PATH,
        help="Path to write results JSON (default: results/time_dilation_experiment.json)",
    )
    args = parser.parse_args()

    payload = run_experiment(write=False)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
