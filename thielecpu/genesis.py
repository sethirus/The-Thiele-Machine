from __future__ import annotations

import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

from thielecpu.state import State
from thielecpu.vm import VM


@dataclass(frozen=True)
class GenesisConfig:
    seed: int = 0
    population: int = 1_000
    generations: int = 50
    rounds_per_generation: int = 40
    initial_fuel: int = 64
    growth_per_round: int = 4
    base_choices: int = 8

    # Hidden environment: reachable indices are exactly i % env_mod == env_residue.
    env_mod: int = 7
    env_residue: int = 3

    # Outcome distribution within reachable indices: p(i) ∝ exp(-i / env_scale)
    env_scale: float = 12.0

    # Selection
    elite_fraction: float = 0.20
    mutation_rate: float = 0.15

    # Betting mechanics
    bet_budget_fraction: float = 0.80
    surprise_cost_scale: float = 1.0

    # Output
    outdir: Optional[Path] = None


@dataclass
class Gene:
    # Agent hypothesis about reachability predicate: i % guess_mod == guess_residue
    guess_mod: int
    guess_residue: int
    # Betting exponent. alpha=1 is linear weighting; larger alpha concentrates bets.
    alpha: float
    coverage: float
    sharpness: float
    explore: float

    def clamp(self) -> None:
        self.guess_mod = max(2, int(self.guess_mod))
        self.guess_residue = int(self.guess_residue) % self.guess_mod
        self.alpha = float(min(6.0, max(0.50, self.alpha)))
        self.coverage = float(min(1.0, max(0.01, self.coverage)))
        self.sharpness = float(min(5.0, max(0.05, self.sharpness)))
        self.explore = float(min(0.50, max(0.0, self.explore)))


@dataclass
class Agent:
    agent_id: int
    gene: Gene
    fuel: int
    alive: bool = True
    age: int = 0


class HiddenEnvironment:
    def __init__(
        self,
        *,
        env_mod: int,
        env_residue: int,
        env_scale: float,
        rng: np.random.Generator,
    ):
        self.env_mod = env_mod
        self.env_residue = env_residue
        self.env_scale = env_scale
        self._rng = rng

    def choice_count(self, *, base: int, growth: int, round_index: int) -> int:
        return int(base + growth * round_index)

    def reachable_indices(self, k: int) -> List[int]:
        return [i for i in range(k) if (i % self.env_mod) == self.env_residue]

    def probs_over_reachable(self, reachable: List[int]) -> np.ndarray:
        if not reachable:
            return np.zeros((0,), dtype=float)
        weights = np.array(
            [math.exp(-float(i) / float(self.env_scale)) for i in reachable],
            dtype=float,
        )
        s = float(weights.sum())
        if s <= 0.0:
            return np.full((len(reachable),), 1.0 / len(reachable), dtype=float)
        return weights / s

    def sample_outcome(self, k: int) -> Tuple[int, Dict[str, Any]]:
        reachable = self.reachable_indices(k)
        if not reachable:
            return 0, {"reachable": [], "p": []}
        p = self.probs_over_reachable(reachable)
        idx = int(self._rng.choice(len(reachable), p=p))
        return int(reachable[idx]), {"reachable": reachable, "p": p.tolist()}


def _now_tag() -> str:
    return time.strftime("%Y%m%d_%H%M%S")


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, default=str), encoding="utf-8")


def _write_csv(path: Path, rows: List[Dict[str, Any]]) -> None:
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    keys = list(rows[0].keys())
    lines = [",".join(keys)]
    for row in rows:
        lines.append(",".join(str(row.get(k, "")) for k in keys))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def random_gene(rng: np.random.Generator) -> Gene:
    guess_mod = int(rng.integers(2, 13))
    guess_residue = int(rng.integers(0, guess_mod))
    alpha = float(rng.uniform(0.90, 4.00))
    coverage = float(rng.uniform(0.10, 0.90))
    sharpness = float(rng.uniform(0.20, 2.00))
    explore = float(rng.uniform(0.00, 0.25))
    gene = Gene(
        guess_mod=guess_mod,
        guess_residue=guess_residue,
        alpha=alpha,
        coverage=coverage,
        sharpness=sharpness,
        explore=explore,
    )
    gene.clamp()
    return gene


def mutate_gene(parent: Gene, rng: np.random.Generator, mutation_rate: float) -> Gene:
    g = Gene(
        guess_mod=parent.guess_mod,
        guess_residue=parent.guess_residue,
        alpha=parent.alpha,
        coverage=parent.coverage,
        sharpness=parent.sharpness,
        explore=parent.explore,
    )

    if rng.random() < mutation_rate:
        g.guess_mod = int(max(2, g.guess_mod + int(rng.integers(-2, 3))))
        g.guess_residue = int(rng.integers(0, g.guess_mod))

    if rng.random() < mutation_rate:
        g.coverage = float(g.coverage + rng.normal(0.0, 0.08))
    if rng.random() < mutation_rate:
        # Keep alpha positive; mutate in log-space for multiplicative variation.
        g.alpha = float(g.alpha * math.exp(rng.normal(0.0, 0.20)))
    if rng.random() < mutation_rate:
        g.sharpness = float(g.sharpness * math.exp(rng.normal(0.0, 0.15)))
    if rng.random() < mutation_rate:
        g.explore = float(g.explore + rng.normal(0.0, 0.06))

    g.clamp()
    return g


def _strategy_install_code() -> str:
    # Executes inside the VM; defines `genesis_strategy`.
    return """
import math

def genesis_strategy(k, fuel, gene):
    k = int(k)
    fuel = int(fuel)
    gene = dict(gene)

    mod = int(gene.get('guess_mod', 7))
    res = int(gene.get('guess_residue', 0))
    alpha = float(gene.get('alpha', 1.0))
    coverage = float(gene.get('coverage', 0.5))
    sharpness = float(gene.get('sharpness', 1.0))
    explore = float(gene.get('explore', 0.10))

    mod = max(2, mod)
    res = res % mod
    alpha = min(6.0, max(0.50, alpha))
    coverage = min(1.0, max(0.01, coverage))
    sharpness = min(5.0, max(0.05, sharpness))
    explore = min(0.50, max(0.0, explore))

    if k <= 0:
        return {'bets': [], 'chosen': [], 'support': 0, 'mod': mod, 'res': res,
                'alpha': alpha, 'coverage': coverage, 'sharpness': sharpness, 'explore': explore}

    explore_budget = int(math.floor(fuel * explore))
    explore_budget = min(explore_budget, fuel)

    candidates = [i for i in range(k) if (i % mod) == res]
    if not candidates:
        candidates = list(range(k))

    bets = [0] * k
    if explore_budget > 0:
        step = max(1, k // max(1, explore_budget))
        offset = (res % k)
        for t in range(explore_budget):
            bets[(offset + (t * step)) % k] += 1

    fuel_main = fuel - explore_budget
    if fuel_main <= 0:
        return {'bets': bets, 'chosen': [], 'support': 0, 'mod': mod, 'res': res,
                'alpha': alpha, 'coverage': coverage, 'sharpness': sharpness, 'explore': explore}

    support = max(1, int(math.ceil(len(candidates) * coverage)))
    support = min(support, len(candidates))
    # Survival heuristic: if the hypothesized reachable set fits in the budget,
    # cover it fully to avoid avoidable zero-bet deaths.
    if len(candidates) <= fuel_main:
        support = len(candidates)
    support = min(support, max(1, fuel_main))

    # Lowest-index candidates are treated as more likely; alpha sharpens/softens
    # the resulting allocation when distributing extra budget.
    chosen = sorted(candidates)[:support]

    for i in chosen:
        bets[i] += 1

    remaining = fuel_main - support
    if remaining > 0 and chosen:
        # Base weights: w_i ∝ exp(-sharpness * i)
        # Exponentiate by alpha to model risk attitude.
        chosen_scores = [(-sharpness * float(i)) for i in chosen]
        m = max(chosen_scores)
        w = [math.exp((s - m) * alpha) for s in chosen_scores]
        z = sum(w) if w else 1.0
        w = [x / z for x in w]

        extra = [int(math.floor(remaining * x)) for x in w]
        used = sum(extra)
        for idx, e in enumerate(extra):
            bets[chosen[idx]] += e

        leftover = remaining - used
        if leftover > 0:
            best_order = sorted(range(len(chosen)), key=lambda j: w[j], reverse=True)
            for t in range(leftover):
                bets[chosen[best_order[t % len(best_order)]]] += 1

    return {
        'bets': bets,
        'chosen': chosen,
        'support': support,
        'mod': mod,
        'res': res,
        'alpha': alpha,
        'coverage': coverage,
        'sharpness': sharpness,
        'explore': explore,
    }
""".strip()


def _ensure_strategy_installed(vm: VM) -> None:
    if vm.python_globals.get("_genesis_strategy_installed"):
        return
    vm.execute_python(_strategy_install_code())
    vm.python_globals["_genesis_strategy_installed"] = True


def vm_bets(vm: VM, agent: Agent, k: int) -> Tuple[List[int], Dict[str, Any], str]:
    _ensure_strategy_installed(vm)
    vm.python_globals["k"] = int(k)
    vm.python_globals["fuel"] = int(agent.fuel)
    vm.python_globals["gene"] = asdict(agent.gene)
    result, trace = vm.execute_python("__result__ = genesis_strategy(k, fuel, gene)")
    if not isinstance(result, dict) or "bets" not in result:
        raise RuntimeError(f"strategy returned unexpected result: {result!r}\nTRACE:\n{trace}")
    bets = result.get("bets")
    if not isinstance(bets, list) or any((not isinstance(x, int) or x < 0) for x in bets):
        raise RuntimeError(f"invalid bet vector: {bets!r}\nTRACE:\n{trace}")
    return bets, result, trace


def _surprise_cost_from_bets(bets: List[int], outcome: int, scale: float) -> int:
    total = int(sum(bets))
    if total <= 0:
        return 1_000_000
    b = int(bets[outcome])
    if b <= 0:
        return 1_000_000
    q = float(b) / float(total)
    surprise = -math.log2(max(1e-12, q))
    return int(math.ceil(float(scale) * surprise))


def run_genesis(config: GenesisConfig) -> Path:
    rng = np.random.default_rng(config.seed)

    outdir = config.outdir
    if outdir is None:
        outdir = Path("artifacts") / "genesis" / _now_tag()
    outdir.mkdir(parents=True, exist_ok=True)

    env = HiddenEnvironment(
        env_mod=config.env_mod,
        env_residue=config.env_residue,
        env_scale=config.env_scale,
        rng=rng,
    )

    population: List[Agent] = [
        Agent(agent_id=i, gene=random_gene(rng), fuel=int(config.initial_fuel))
        for i in range(config.population)
    ]

    rows: List[Dict[str, Any]] = []
    _write_json(outdir / "config.json", {"config": asdict(config)})

    strategy_vm = VM(State())
    _ensure_strategy_installed(strategy_vm)

    for gen in range(config.generations):
        alive_agents = [a for a in population if a.alive]
        if not alive_agents:
            rows.append(
                {
                    "generation": gen,
                    "alive": 0,
                    "mean_fuel": 0.0,
                    "mean_age": 0.0,
                    "hit_env_mod": 0,
                    "hit_env_mod_and_residue": 0,
                }
            )
            break

        for r in range(config.rounds_per_generation):
            k = env.choice_count(base=config.base_choices, growth=config.growth_per_round, round_index=r)
            outcome, _env_meta = env.sample_outcome(k)

            for agent in alive_agents:
                if not agent.alive:
                    continue
                if agent.fuel <= 0:
                    agent.alive = False
                    continue

                bet_budget = max(1, int(math.floor(agent.fuel * config.bet_budget_fraction)))
                bet_budget = min(bet_budget, agent.fuel)

                original_fuel = agent.fuel
                agent.fuel = bet_budget
                try:
                    bets, _strat_meta, _trace = vm_bets(strategy_vm, agent, k)
                finally:
                    agent.fuel = original_fuel

                if len(bets) != k:
                    agent.alive = False
                    continue
                spent = int(sum(bets))
                if spent > bet_budget:
                    agent.alive = False
                    continue
                if int(bets[outcome]) <= 0:
                    agent.alive = False
                    continue

                surprise_cost = _surprise_cost_from_bets(bets, outcome, config.surprise_cost_scale)
                # Metabolic model: information-surprise costs fuel, but survivors
                # regenerate a small fixed amount each step (capped at initial_fuel).
                agent.fuel = min(
                    int(config.initial_fuel),
                    max(0, int(agent.fuel) - int(surprise_cost) + 1),
                )
                agent.age += 1

            alive_agents = [a for a in alive_agents if a.alive]
            if not alive_agents:
                break

        survivors = [a for a in population if a.alive]
        survivors.sort(key=lambda a: (a.age, a.fuel), reverse=True)

        alive = len(survivors)
        mean_fuel = float(np.mean([a.fuel for a in survivors])) if survivors else 0.0
        mean_age = float(np.mean([a.age for a in survivors])) if survivors else 0.0
        mean_alpha = float(np.mean([a.gene.alpha for a in survivors])) if survivors else 0.0
        alpha_p25 = float(np.percentile([a.gene.alpha for a in survivors], 25.0)) if survivors else 0.0
        alpha_p50 = float(np.percentile([a.gene.alpha for a in survivors], 50.0)) if survivors else 0.0
        alpha_p75 = float(np.percentile([a.gene.alpha for a in survivors], 75.0)) if survivors else 0.0
        mod_hits = sum(1 for a in survivors if a.gene.guess_mod == config.env_mod)
        residue_hits = sum(
            1
            for a in survivors
            if a.gene.guess_mod == config.env_mod and a.gene.guess_residue == config.env_residue
        )

        _write_json(
            outdir / "survivors" / f"gen_{gen:04d}.json",
            {
                "generation": gen,
                "alive": alive,
                "survivors": [
                    {
                        "agent_id": a.agent_id,
                        "age": a.age,
                        "fuel": a.fuel,
                        "gene": asdict(a.gene),
                    }
                    for a in survivors
                ],
            },
        )

        rows.append(
            {
                "generation": gen,
                "alive": alive,
                "mean_fuel": round(mean_fuel, 3),
                "mean_age": round(mean_age, 3),
                "mean_alpha": round(mean_alpha, 4),
                "alpha_p25": round(alpha_p25, 4),
                "alpha_p50": round(alpha_p50, 4),
                "alpha_p75": round(alpha_p75, 4),
                "hit_env_mod": mod_hits,
                "hit_env_mod_and_residue": residue_hits,
            }
        )

        if not survivors:
            break

        elite_n = max(1, int(math.ceil(config.elite_fraction * len(survivors))))
        elite = survivors[:elite_n]

        population = [
            Agent(
                agent_id=i,
                gene=mutate_gene(elite[int(rng.integers(0, len(elite)))].gene, rng, config.mutation_rate),
                fuel=int(config.initial_fuel),
            )
            for i in range(config.population)
        ]

    _write_csv(outdir / "history.csv", rows)
    _write_json(
        outdir / "sample_genes.json",
        {"sample": [{"agent_id": a.agent_id, "gene": asdict(a.gene)} for a in population[:25]]},
    )
    return outdir


def plot_history(outdir: Path) -> Optional[Path]:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    history_path = outdir / "history.csv"
    if not history_path.exists():
        return None
    lines = history_path.read_text(encoding="utf-8").splitlines()
    if len(lines) < 2:
        return None

    header = lines[0].split(",")
    parsed = [dict(zip(header, ln.split(","))) for ln in lines[1:] if ln.strip()]
    if not parsed:
        return None

    gen = [int(r["generation"]) for r in parsed]
    alive = [int(r["alive"]) for r in parsed]
    mean_fuel = [float(r["mean_fuel"]) for r in parsed]
    hit_res = [int(r["hit_env_mod_and_residue"]) for r in parsed]

    mean_alpha = [float(r.get("mean_alpha", 0.0)) for r in parsed]

    fig, ax = plt.subplots(4, 1, figsize=(10, 11), sharex=True)
    ax[0].plot(gen, alive)
    ax[0].set_ylabel("alive")
    ax[0].grid(True, alpha=0.3)

    ax[1].plot(gen, mean_fuel)
    ax[1].set_ylabel("mean fuel")
    ax[1].grid(True, alpha=0.3)

    ax[2].plot(gen, hit_res)
    ax[2].set_ylabel("correct reachability")
    ax[2].grid(True, alpha=0.3)

    ax[3].plot(gen, mean_alpha)
    ax[3].set_ylabel("mean alpha")
    ax[3].set_xlabel("generation")
    ax[3].grid(True, alpha=0.3)

    fig.tight_layout()
    plot_path = outdir / "plot.png"
    fig.savefig(plot_path, dpi=160)
    plt.close(fig)
    return plot_path
