#!/usr/bin/env python3
"""Genesis robustness sweep for the interference environment (wave genesis).

This turns the "nice demo" into a reproducible, falsifiable sweep:
- seeds: configurable (default 20)
- phase flip probability: configurable grid
- mutation rate: configurable grid
- payoff rule: at least two (default: surprise_bits vs log_score)

Outputs a single CSV with per-run metrics plus an aggregated summary CSV.

Notes on interpretation
- This is a *selection* experiment, not a proof of the Born rule.
- The key question is whether α trends toward ~2 specifically in
  phase-hidden interference regimes, and how sensitive that is to
  payoff definition and mutation.
"""

from __future__ import annotations

import argparse
import csv
import math
import statistics
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Literal, Sequence, Tuple

import numpy as np
from tqdm import tqdm

from thielecpu import genesis_wave as gw

from thielecpu.genesis_wave import InterferenceEnvironment, WaveAgent, WaveConfig, mutate_gene, random_gene
from thielecpu.state import State
from thielecpu.vm import VM

PayoffRule = Literal["surprise_bits", "log_score", "brier"]
BetsEngine = Literal["python", "vm"]


def _now_tag() -> str:
    return time.strftime("%Y%m%d_%H%M%S")


def _lin_slope(xs: Sequence[float], ys: Sequence[float]) -> float:
    if len(xs) != len(ys) or len(xs) < 2:
        return 0.0
    x = np.asarray(xs, dtype=float)
    y = np.asarray(ys, dtype=float)
    x = x - float(np.mean(x))
    denom = float(np.sum(x * x))
    if denom <= 0.0:
        return 0.0
    return float(np.sum(x * (y - float(np.mean(y)))) / denom)


def payoff_cost(q: float, *, scale: float, rule: PayoffRule) -> int:
    """Compute an integer cost from the predicted outcome probability q.

    Lower cost is better; agents lose fuel by this cost and regain a fixed regen.

    - surprise_bits: ceil(scale * -log2(q)) (matches thielecpu.genesis_wave)
    - log_score:     round(scale * -log(q)) in nats (different curvature + rounding)
    - brier:         round(scale * (1-q)^2) (quadratic penalty; non-log rule)
    """

    q = float(q)
    if q <= 0.0:
        return 1_000_000
    if rule == "surprise_bits":
        surprise = -math.log2(max(1e-12, q))
        return int(math.ceil(float(scale) * surprise))
    if rule == "log_score":
        loss = -math.log(max(1e-12, q))
        return int(max(1, round(float(scale) * loss)))
    if rule == "brier":
        loss = (1.0 - q) * (1.0 - q)
        return int(max(1, round(float(scale) * loss)))
    raise ValueError(f"unknown payoff rule: {rule}")


def compile_strategy() -> "callable":
    """Compile the exact strategy code string into a callable.

    This executes the same code shipped to the VM (via `_strategy_install_code()`),
    but runs it in-process for speed in large sweeps.
    """

    namespace: Dict[str, object] = {}
    exec(gw._strategy_install_code(), namespace)  # type: ignore[attr-defined]
    fn = namespace.get("genesis_wave_strategy")
    if not callable(fn):
        raise RuntimeError("Failed to compile genesis_wave_strategy")
    return fn


@dataclass(frozen=True)
class RunMetrics:
    seed: int
    phase_pi_prob: float
    mutation_rate: float
    payoff_rule: PayoffRule

    final_mean_alpha: float
    alpha_slope_last_n: float
    final_alpha_variance: float
    alpha2_gap: float
    final_alive: int


def _evaluate_gene(
    *,
    gene: dict,
    phase_pi_prob: float,
    seed: int,
    rounds: int,
    detectors: int,
    paths_min: int,
    paths_max: int,
    mag_scale: float,
    fuel: int,
) -> float:
    """Return average negative log2(q_outcome) over an evaluation set."""

    rng = np.random.default_rng(seed)
    env = InterferenceEnvironment(
        detectors=detectors,
        paths_min=paths_min,
        paths_max=paths_max,
        mag_scale=mag_scale,
        phase_pi_prob=phase_pi_prob,
        rng=rng,
    )

    strategy = compile_strategy()

    losses: List[float] = []
    for _ in range(int(rounds)):
        obs, outcome, _meta = env.sample_round()
        result = strategy(obs, int(fuel), dict(gene))
        bets = result.get("bets") if isinstance(result, dict) else None
        if not isinstance(bets, list) or any((not isinstance(x, int) or x < 0) for x in bets):
            return float("inf")
        total = int(sum(bets))
        q = (float(bets[outcome]) / float(total)) if total > 0 else 0.0
        losses.append(float(-math.log2(max(1e-12, q))))

    return float(np.mean(losses)) if losses else float("inf")


def run_one(
    *,
    seed: int,
    phase_pi_prob: float,
    mutation_rate: float,
    payoff_rule: PayoffRule,
    population: int,
    generations: int,
    rounds_per_generation: int,
    initial_fuel: int,
    regen_per_round: int,
    bet_budget_fraction: float,
    surprise_cost_scale: float,
    detectors: int,
    paths_min: int,
    paths_max: int,
    mag_scale: float,
    slope_window: int,
    eval_rounds: int,
    engine: BetsEngine,
) -> RunMetrics:
    cfg = WaveConfig(
        seed=seed,
        population=population,
        generations=generations,
        rounds_per_generation=rounds_per_generation,
        initial_fuel=initial_fuel,
        bet_budget_fraction=bet_budget_fraction,
        surprise_cost_scale=surprise_cost_scale,
        regen_per_round=regen_per_round,
        elite_fraction=0.20,
        mutation_rate=float(mutation_rate),
        detectors=detectors,
        paths_min=paths_min,
        paths_max=paths_max,
        mag_scale=mag_scale,
        phase_pi_prob=float(phase_pi_prob),
        outdir=None,
    )

    rng = np.random.default_rng(cfg.seed)
    env = InterferenceEnvironment(
        detectors=cfg.detectors,
        paths_min=cfg.paths_min,
        paths_max=cfg.paths_max,
        mag_scale=cfg.mag_scale,
        phase_pi_prob=cfg.phase_pi_prob,
        rng=rng,
    )

    population_agents: List[WaveAgent] = [
        WaveAgent(agent_id=i, gene=random_gene(rng), fuel=int(cfg.initial_fuel))
        for i in range(int(cfg.population))
    ]

    strategy_vm = VM(State()) if engine == "vm" else None
    strategy = compile_strategy() if engine == "python" else None

    history_mean_alpha: List[float] = []
    history_alive: List[int] = []

    regen = int(cfg.regen_per_round)
    if regen <= 0:
        regen = max(1, int(round(math.log2(max(2, int(cfg.detectors))))))

    survivors: List[WaveAgent] = []

    for gen in range(int(cfg.generations)):
        alive_agents = [a for a in population_agents if a.alive]
        if not alive_agents:
            history_mean_alpha.append(0.0)
            history_alive.append(0)
            survivors = []
            break

        for _r in range(int(cfg.rounds_per_generation)):
            obs, outcome, _meta = env.sample_round()

            for agent in alive_agents:
                if not agent.alive:
                    continue
                if agent.fuel <= 0:
                    agent.alive = False
                    continue

                bet_budget = max(1, int(math.floor(agent.fuel * cfg.bet_budget_fraction)))
                bet_budget = min(bet_budget, agent.fuel)

                original_fuel = agent.fuel
                agent.fuel = bet_budget
                try:
                    if engine == "vm":
                        assert strategy_vm is not None
                        bets, _strat_meta, _trace = gw.vm_bets(strategy_vm, agent, obs)
                    else:
                        assert strategy is not None
                        # Strategy expects a plain dict gene.
                        result = strategy(obs, int(agent.fuel), gw.asdict(agent.gene))
                        bets = result.get("bets") if isinstance(result, dict) else None
                        if not isinstance(bets, list):
                            raise RuntimeError(f"strategy returned unexpected result: {result!r}")
                finally:
                    agent.fuel = original_fuel

                if len(bets) != cfg.detectors:
                    agent.alive = False
                    continue

                spent = int(sum(bets))
                if spent <= 0 or spent > bet_budget:
                    agent.alive = False
                    continue

                if int(bets[outcome]) <= 0:
                    agent.alive = False
                    continue

                q = float(bets[outcome]) / float(spent)
                cost = payoff_cost(q, scale=cfg.surprise_cost_scale, rule=payoff_rule)

                agent.fuel = min(
                    int(cfg.initial_fuel),
                    max(0, int(agent.fuel) - int(cost) + int(regen)),
                )
                agent.age += 1

            alive_agents = [a for a in alive_agents if a.alive]
            if not alive_agents:
                break

        survivors = [a for a in population_agents if a.alive]
        survivors.sort(key=lambda a: (a.age, a.fuel), reverse=True)

        history_alive.append(len(survivors))
        alphas = [a.gene.alpha for a in survivors]
        history_mean_alpha.append(float(np.mean(alphas)) if alphas else 0.0)

        if not survivors:
            break

        elite_n = max(1, int(math.ceil(cfg.elite_fraction * len(survivors))))
        elite = survivors[:elite_n]

        population_agents = [
            WaveAgent(
                agent_id=i,
                gene=mutate_gene(elite[int(rng.integers(0, len(elite)))].gene, rng, cfg.mutation_rate),
                fuel=int(cfg.initial_fuel),
            )
            for i in range(int(cfg.population))
        ]

    # Final metrics
    final_mean_alpha = float(history_mean_alpha[-1]) if history_mean_alpha else 0.0

    window = int(min(max(2, slope_window), len(history_mean_alpha)))
    xs = list(range(len(history_mean_alpha) - window, len(history_mean_alpha)))
    ys = history_mean_alpha[-window:]
    alpha_slope = _lin_slope(xs, ys)

    final_alphas = [a.gene.alpha for a in survivors]
    final_var = float(statistics.pvariance(final_alphas)) if len(final_alphas) >= 2 else 0.0

    # Performance gap: best evolved vs same gene with alpha fixed to 2.
    alpha2_gap = 0.0
    if survivors:
        best_gene = survivors[0].gene
        best_dict = {
            "alpha": float(best_gene.alpha),
            "beta": float(best_gene.beta),
            "explore": float(best_gene.explore),
            "coverage": float(best_gene.coverage),
        }
        alpha2_dict = dict(best_dict)
        alpha2_dict["alpha"] = 2.0

        best_loss = _evaluate_gene(
            gene=best_dict,
            phase_pi_prob=float(phase_pi_prob),
            seed=int(seed) ^ 0xA5A5,
            rounds=int(eval_rounds),
            detectors=int(detectors),
            paths_min=int(paths_min),
            paths_max=int(paths_max),
            mag_scale=float(mag_scale),
            fuel=int(initial_fuel),
        )
        alpha2_loss = _evaluate_gene(
            gene=alpha2_dict,
            phase_pi_prob=float(phase_pi_prob),
            seed=int(seed) ^ 0x5A5A,
            rounds=int(eval_rounds),
            detectors=int(detectors),
            paths_min=int(paths_min),
            paths_max=int(paths_max),
            mag_scale=float(mag_scale),
            fuel=int(initial_fuel),
        )
        alpha2_gap = float(alpha2_loss - best_loss)

    return RunMetrics(
        seed=int(seed),
        phase_pi_prob=float(phase_pi_prob),
        mutation_rate=float(mutation_rate),
        payoff_rule=payoff_rule,
        final_mean_alpha=float(final_mean_alpha),
        alpha_slope_last_n=float(alpha_slope),
        final_alpha_variance=float(final_var),
        alpha2_gap=float(alpha2_gap),
        final_alive=int(history_alive[-1]) if history_alive else 0,
    )


def _write_csv(path: Path, rows: Sequence[Dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def _aggregate(metrics: Sequence[RunMetrics]) -> List[Dict[str, object]]:
    groups: Dict[Tuple[float, float, str], List[RunMetrics]] = {}
    for m in metrics:
        key = (m.phase_pi_prob, m.mutation_rate, m.payoff_rule)
        groups.setdefault(key, []).append(m)

    out: List[Dict[str, object]] = []
    for (phase, mut, rule), items in sorted(groups.items(), key=lambda kv: kv[0]):
        out.append(
            {
                "phase_pi_prob": phase,
                "mutation_rate": mut,
                "payoff_rule": rule,
                "runs": len(items),
                "final_mean_alpha_mean": float(np.mean([i.final_mean_alpha for i in items])),
                "final_mean_alpha_std": float(np.std([i.final_mean_alpha for i in items], ddof=0)),
                "alpha_slope_mean": float(np.mean([i.alpha_slope_last_n for i in items])),
                "alpha_var_mean": float(np.mean([i.final_alpha_variance for i in items])),
                "alpha2_gap_mean": float(np.mean([i.alpha2_gap for i in items])),
                "final_alive_mean": float(np.mean([i.final_alive for i in items])),
            }
        )
    return out


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--outdir", type=Path, default=Path("artifacts") / "genesis_wave_sweep" / _now_tag())

    p.add_argument("--seeds", type=int, default=20, help="Number of seeds (runs use seeds 0..N-1)")
    p.add_argument(
        "--phase-pi-prob",
        type=float,
        nargs="*",
        default=[0.1, 0.3, 0.5, 0.7, 0.9],
        help="Phase pi probability grid.",
    )
    p.add_argument(
        "--mutation-rate",
        type=float,
        nargs="*",
        default=[0.05, 0.15, 0.30],
        help="Mutation rate grid.",
    )
    p.add_argument(
        "--payoff-rule",
        type=str,
        nargs="*",
        default=["surprise_bits", "log_score"],
        choices=["surprise_bits", "log_score", "brier"],
    )

    # Keep defaults modest so the 600-run sweep is feasible.
    p.add_argument("--population", type=int, default=60)
    p.add_argument("--generations", type=int, default=25)
    p.add_argument("--rounds", type=int, default=25)
    p.add_argument("--initial-fuel", type=int, default=72)
    p.add_argument("--regen", type=int, default=4)

    p.add_argument("--detectors", type=int, default=16)
    p.add_argument("--paths-min", type=int, default=2)
    p.add_argument("--paths-max", type=int, default=8)
    p.add_argument("--mag-scale", type=float, default=1.0)

    p.add_argument("--bet-budget-fraction", type=float, default=0.80)
    p.add_argument("--surprise-cost-scale", type=float, default=1.0)

    p.add_argument("--slope-window", type=int, default=10)
    p.add_argument("--eval-rounds", type=int, default=200)

    p.add_argument(
        "--engine",
        choices=["python", "vm"],
        default="python",
        help="Execution engine for the strategy (python is much faster for large sweeps).",
    )

    return p.parse_args()


def main() -> int:
    args = parse_args()

    outdir: Path = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)

    seeds = list(range(int(args.seeds)))
    phase_grid = [float(x) for x in args.phase_pi_prob]
    mutation_grid = [float(x) for x in args.mutation_rate]
    payoff_rules: List[PayoffRule] = [x for x in args.payoff_rule]

    total = len(seeds) * len(phase_grid) * len(mutation_grid) * len(payoff_rules)

    metrics: List[RunMetrics] = []
    rows: List[Dict[str, object]] = []

    with tqdm(total=total, desc="Genesis sweep", unit="run") as bar:
        for seed in seeds:
            for phase in phase_grid:
                for mut in mutation_grid:
                    for rule in payoff_rules:
                        m = run_one(
                            seed=seed,
                            phase_pi_prob=phase,
                            mutation_rate=mut,
                            payoff_rule=rule,
                            population=int(args.population),
                            generations=int(args.generations),
                            rounds_per_generation=int(args.rounds),
                            initial_fuel=int(args.initial_fuel),
                            regen_per_round=int(args.regen),
                            bet_budget_fraction=float(args.bet_budget_fraction),
                            surprise_cost_scale=float(args.surprise_cost_scale),
                            detectors=int(args.detectors),
                            paths_min=int(args.paths_min),
                            paths_max=int(args.paths_max),
                            mag_scale=float(args.mag_scale),
                            slope_window=int(args.slope_window),
                            eval_rounds=int(args.eval_rounds),
                            engine=args.engine,
                        )
                        metrics.append(m)
                        rows.append(
                            {
                                "seed": m.seed,
                                "phase_pi_prob": m.phase_pi_prob,
                                "mutation_rate": m.mutation_rate,
                                "payoff_rule": m.payoff_rule,
                                "final_mean_alpha": round(m.final_mean_alpha, 6),
                                "alpha_slope_last_n": round(m.alpha_slope_last_n, 8),
                                "final_alpha_variance": round(m.final_alpha_variance, 6),
                                "alpha2_gap": round(m.alpha2_gap, 6),
                                "final_alive": m.final_alive,
                            }
                        )
                        bar.update(1)

    runs_csv = outdir / "runs.csv"
    summary_csv = outdir / "summary.csv"
    _write_csv(runs_csv, rows)
    _write_csv(summary_csv, _aggregate(metrics))

    print(f"Wrote per-run metrics: {runs_csv}")
    print(f"Wrote aggregated summary: {summary_csv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
