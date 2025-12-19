"""Simulate a μ-budgeted infinite loop and emit a receipt when the budget is exhausted."""
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

from thielecpu.state import MuLedger

REPO_ROOT = Path(__file__).resolve().parent.parent
RESULTS_PATH = REPO_ROOT / "results" / "halting_trap.json"


@dataclass
class LoopConfig:
    budget_mu: int = 1000
    step_cost: int = 1
    max_steps: int = 10_000


@dataclass
class LoopResult:
    steps_executed: int
    mu_spent: int
    status: str
    budget_mu: int
    step_cost: int
    trace: List[int]

    def to_dict(self) -> Dict[str, object]:
        return {
            "steps_executed": self.steps_executed,
            "mu_spent": self.mu_spent,
            "status": self.status,
            "budget_mu": self.budget_mu,
            "step_cost": self.step_cost,
            "trace": self.trace,
        }


def run_budgeted_loop(config: LoopConfig = LoopConfig(), write: bool = True) -> LoopResult:
    ledger = MuLedger()
    trace: List[int] = []
    steps = 0

    while steps < config.max_steps and ledger.total < config.budget_mu:
        ledger.mu_execution += config.step_cost
        steps += 1
        trace.append(ledger.total)

    status = "mu_overflow" if ledger.total >= config.budget_mu else "max_steps_reached"
    result = LoopResult(
        steps_executed=steps,
        mu_spent=ledger.total,
        status=status,
        budget_mu=config.budget_mu,
        step_cost=config.step_cost,
        trace=trace,
    )

    if write:
        RESULTS_PATH.parent.mkdir(parents=True, exist_ok=True)
        RESULTS_PATH.write_text(json.dumps(result.to_dict(), indent=2), encoding="utf-8")

    return result


if __name__ == "__main__":
    res = run_budgeted_loop()
    print(json.dumps(res.to_dict(), indent=2))
