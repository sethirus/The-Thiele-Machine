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
class WaveConfig:
    seed: int = 0
    population: int = 1_000
    generations: int = 60
    rounds_per_generation: int = 60

    initial_fuel: int = 72
    bet_budget_fraction: float = 0.80
    surprise_cost_scale: float = 1.0
    regen_per_round: int = 4

    elite_fraction: float = 0.20
    mutation_rate: float = 0.15

    # Environment
    detectors: int = 16
    paths_min: int = 2
    paths_max: int = 8
    mag_scale: float = 1.0  # exponential scale
    phase_pi_prob: float = 0.50  # 0 -> phase 0, 1 -> phase pi

    # Output
    outdir: Optional[Path] = None


@dataclass
class WaveGene:
    # alpha=1 corresponds to linear sum of magnitudes; alpha=2 corresponds to sum of squares.
    alpha: float
    # beta controls softmax sharpness over detector scores.
    beta: float
    # fraction of budget reserved for random exploration coverage.
    explore: float
    # fraction of detectors included in support.
    coverage: float

    def clamp(self) -> None:
        self.alpha = float(min(6.0, max(0.50, self.alpha)))
        self.beta = float(min(8.0, max(0.05, self.beta)))
        self.explore = float(min(0.50, max(0.0, self.explore)))
        self.coverage = float(min(1.0, max(0.05, self.coverage)))


@dataclass
class WaveAgent:
    agent_id: int
    gene: WaveGene
    fuel: int
    alive: bool = True
    age: int = 0


class InterferenceEnvironment:
    """Oracle environment with hidden phases causing constructive/destructive interference.

    Observation exposes only per-path magnitudes (no phases). True probabilities are based on
    intensities: I_j = |sum_p (sign_p * mag_p)|^2.
    """

    def __init__(
        self,
        *,
        detectors: int,
        paths_min: int,
        paths_max: int,
        mag_scale: float,
        phase_pi_prob: float,
        rng: np.random.Generator,
    ):
        self.detectors = int(detectors)
        self.paths_min = int(paths_min)
        self.paths_max = int(paths_max)
        self.mag_scale = float(mag_scale)
        self.phase_pi_prob = float(phase_pi_prob)
        self._rng = rng

    def sample_round(self) -> Tuple[List[List[float]], int, Dict[str, Any]]:
        k = self.detectors
        mags: List[List[float]] = []
        intensities = np.zeros((k,), dtype=float)

        for j in range(k):
            n_paths = int(self._rng.integers(self.paths_min, self.paths_max + 1))
            # Exponential magnitudes, strictly positive.
            m = self._rng.exponential(self.mag_scale, size=(n_paths,)).astype(float)
            # Hidden phase: 0 -> +1, pi -> -1.
            phase_is_pi = self._rng.random(size=(n_paths,)) < self.phase_pi_prob
            signs = np.where(phase_is_pi, -1.0, 1.0)
            amp = float(np.sum(signs * m))
            intensities[j] = float(amp * amp)
            mags.append([float(x) for x in m.tolist()])

        total = float(np.sum(intensities))
        if total <= 0.0:
            # Degenerate: all cancelled. Resample once; if still degenerate, fall back to uniform.
            total = 0.0

        if total <= 0.0:
            p = np.full((k,), 1.0 / k, dtype=float)
        else:
            p = intensities / total

        outcome = int(self._rng.choice(k, p=p))
        meta = {
            "intensities": intensities.tolist(),
            "p": p.tolist(),
        }
        return mags, outcome, meta


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


def random_gene(rng: np.random.Generator) -> WaveGene:
    g = WaveGene(
        alpha=float(rng.uniform(0.80, 4.00)),
        beta=float(rng.uniform(0.25, 3.00)),
        explore=float(rng.uniform(0.00, 0.25)),
        coverage=float(rng.uniform(0.10, 0.80)),
    )
    g.clamp()
    return g


def mutate_gene(parent: WaveGene, rng: np.random.Generator, mutation_rate: float) -> WaveGene:
    g = WaveGene(alpha=parent.alpha, beta=parent.beta, explore=parent.explore, coverage=parent.coverage)

    if rng.random() < mutation_rate:
        g.alpha = float(g.alpha * math.exp(rng.normal(0.0, 0.22)))
    if rng.random() < mutation_rate:
        g.beta = float(g.beta * math.exp(rng.normal(0.0, 0.22)))
    if rng.random() < mutation_rate:
        g.explore = float(g.explore + rng.normal(0.0, 0.06))
    if rng.random() < mutation_rate:
        g.coverage = float(g.coverage + rng.normal(0.0, 0.10))

    g.clamp()
    return g


def _strategy_install_code() -> str:
    return """
import math

def genesis_wave_strategy(obs, fuel, gene):
    # obs: list[list[float]] path magnitudes per detector
    fuel = int(fuel)
    gene = dict(gene)

    alpha = float(gene.get('alpha', 1.0))
    beta = float(gene.get('beta', 1.0))
    explore = float(gene.get('explore', 0.10))
    coverage = float(gene.get('coverage', 0.30))

    alpha = min(6.0, max(0.50, alpha))
    beta = min(8.0, max(0.05, beta))
    explore = min(0.50, max(0.0, explore))
    coverage = min(1.0, max(0.05, coverage))

    k = len(obs)
    if k <= 0 or fuel <= 0:
        return {'bets': [], 'alpha': alpha, 'beta': beta, 'coverage': coverage, 'explore': explore}

    # Score_j = sum_p (mag_p ** alpha). alpha=2 corresponds to sum of squares.
    scores = []
    for comp in obs:
        s = 0.0
        for x in comp:
            try:
                fx = float(x)
            except Exception:
                fx = 0.0
            if fx > 0.0:
                s += fx ** alpha
        scores.append(max(1e-12, s))

    explore_budget = int(math.floor(fuel * explore))
    explore_budget = min(explore_budget, fuel)

    bets = [0] * k
    if explore_budget > 0:
        step = max(1, k // max(1, explore_budget))
        offset = (int(alpha * 1000.0) + int(beta * 100.0)) % k
        for t in range(explore_budget):
            bets[(offset + t * step) % k] += 1

    fuel_main = fuel - explore_budget
    if fuel_main <= 0:
        return {'bets': bets, 'alpha': alpha, 'beta': beta, 'coverage': coverage, 'explore': explore}

    # Ensure some coverage over top-scoring detectors.
    support = max(1, int(math.ceil(k * coverage)))
    support = min(support, k)
    # Survival heuristic: if we can afford one chip on every detector,
    # do it to avoid avoidable zero-bet deaths.
    if k <= fuel_main:
        support = k
    support = min(support, max(1, fuel_main))

    order = sorted(range(k), key=lambda j: scores[j], reverse=True)
    chosen = order[:support]

    for j in chosen:
        bets[j] += 1

    remaining = fuel_main - support
    if remaining > 0 and chosen:
        # Softmax over log-scores for numerical stability.
        logs = [math.log(scores[j]) for j in chosen]
        m = max(logs)
        w = [math.exp(beta * (v - m)) for v in logs]
        z = sum(w) if w else 1.0
        w = [x / z for x in w]

        extra = [int(math.floor(remaining * x)) for x in w]
        used = sum(extra)
        for idx, e in enumerate(extra):
            bets[chosen[idx]] += e

        leftover = remaining - used
        if leftover > 0:
            best_order = sorted(range(len(chosen)), key=lambda i: w[i], reverse=True)
            for t in range(leftover):
                bets[chosen[best_order[t % len(best_order)]]] += 1

    return {
        'bets': bets,
        'alpha': alpha,
        'beta': beta,
        'coverage': coverage,
        'explore': explore,
        'scores': scores,
        'chosen': chosen,
    }
""".strip()


def _ensure_strategy_installed(vm: VM) -> None:
    if vm.python_globals.get("_genesis_wave_strategy_installed"):
        return
    vm.execute_python(_strategy_install_code())
    vm.python_globals["_genesis_wave_strategy_installed"] = True


def vm_bets(vm: VM, agent: WaveAgent, obs: List[List[float]]) -> Tuple[List[int], Dict[str, Any], str]:
    _ensure_strategy_installed(vm)
    vm.python_globals["obs"] = obs
    vm.python_globals["fuel"] = int(agent.fuel)
    vm.python_globals["gene"] = asdict(agent.gene)
    result, trace = vm.execute_python("__result__ = genesis_wave_strategy(obs, fuel, gene)")
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


def run_genesis_wave(config: WaveConfig) -> Path:
    rng = np.random.default_rng(config.seed)

    outdir = config.outdir
    if outdir is None:
        outdir = Path("artifacts") / "genesis_wave" / _now_tag()
    outdir.mkdir(parents=True, exist_ok=True)

    env = InterferenceEnvironment(
        detectors=config.detectors,
        paths_min=config.paths_min,
        paths_max=config.paths_max,
        mag_scale=config.mag_scale,
        phase_pi_prob=config.phase_pi_prob,
        rng=rng,
    )

    population: List[WaveAgent] = [
        WaveAgent(agent_id=i, gene=random_gene(rng), fuel=int(config.initial_fuel))
        for i in range(config.population)
    ]

    _write_json(outdir / "config.json", {"config": asdict(config)})

    strategy_vm = VM(State())
    _ensure_strategy_installed(strategy_vm)

    rows: List[Dict[str, Any]] = []

    regen = int(config.regen_per_round)
    if regen <= 0:
        regen = max(1, int(round(math.log2(max(2, int(config.detectors))))))

    for gen in range(config.generations):
        alive_agents = [a for a in population if a.alive]
        if not alive_agents:
            rows.append(
                {
                    "generation": gen,
                    "alive": 0,
                    "mean_fuel": 0.0,
                    "mean_age": 0.0,
                    "mean_alpha": 0.0,
                    "alpha_p25": 0.0,
                    "alpha_p50": 0.0,
                    "alpha_p75": 0.0,
                }
            )
            break

        for _r in range(config.rounds_per_generation):
            obs, outcome, _meta = env.sample_round()

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
                    bets, _strat_meta, _trace = vm_bets(strategy_vm, agent, obs)
                finally:
                    agent.fuel = original_fuel

                if len(bets) != config.detectors:
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
                agent.fuel = min(
                    int(config.initial_fuel),
                    max(0, int(agent.fuel) - int(surprise_cost) + int(regen)),
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

        alphas = [a.gene.alpha for a in survivors]
        mean_alpha = float(np.mean(alphas)) if alphas else 0.0
        alpha_p25 = float(np.percentile(alphas, 25.0)) if alphas else 0.0
        alpha_p50 = float(np.percentile(alphas, 50.0)) if alphas else 0.0
        alpha_p75 = float(np.percentile(alphas, 75.0)) if alphas else 0.0

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
            }
        )

        if not survivors:
            break

        elite_n = max(1, int(math.ceil(config.elite_fraction * len(survivors))))
        elite = survivors[:elite_n]

        population = [
            WaveAgent(
                agent_id=i,
                gene=mutate_gene(elite[int(rng.integers(0, len(elite)))].gene, rng, config.mutation_rate),
                fuel=int(config.initial_fuel),
            )
            for i in range(config.population)
        ]

    _write_csv(outdir / "history.csv", rows)

    # Sample of the final population genes (not necessarily survivors).
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
    mean_alpha = [float(r.get("mean_alpha", 0.0)) for r in parsed]
    alpha_p25 = [float(r.get("alpha_p25", 0.0)) for r in parsed]
    alpha_p50 = [float(r.get("alpha_p50", 0.0)) for r in parsed]
    alpha_p75 = [float(r.get("alpha_p75", 0.0)) for r in parsed]

    fig, ax = plt.subplots(4, 1, figsize=(10, 11), sharex=True)

    ax[0].plot(gen, alive)
    ax[0].set_ylabel("alive")
    ax[0].grid(True, alpha=0.3)

    ax[1].plot(gen, mean_fuel)
    ax[1].set_ylabel("mean fuel")
    ax[1].grid(True, alpha=0.3)

    ax[2].plot(gen, mean_alpha)
    ax[2].fill_between(gen, alpha_p25, alpha_p75, alpha=0.20)
    ax[2].plot(gen, alpha_p50)
    ax[2].set_ylabel("alpha")
    ax[2].grid(True, alpha=0.3)

    ax[3].plot(gen, alpha_p25, label="p25")
    ax[3].plot(gen, alpha_p50, label="p50")
    ax[3].plot(gen, alpha_p75, label="p75")
    ax[3].set_ylabel("alpha percentiles")
    ax[3].set_xlabel("generation")
    ax[3].grid(True, alpha=0.3)

    fig.tight_layout()
    plot_path = outdir / "plot.png"
    fig.savefig(plot_path, dpi=160)
    plt.close(fig)
    return plot_path
