"""Entropy identity runner built on the biased diffusion protocol."""

from __future__ import annotations

import argparse
import csv
import json
import math
import statistics
from dataclasses import dataclass
from pathlib import Path
import random
from typing import Dict, Iterable, Iterator, List, MutableMapping, Sequence, Tuple

from . import ledger_io

K_BOLTZMANN = 1.0


@dataclass(frozen=True)
class EntropyConfig:
    """Configuration parameters for deterministic entropy-identity runs."""

    output_dir: Path
    seeds: Sequence[int]
    temps: Sequence[float]
    trials_per_condition: int
    steps: int = 96
    dt: float = 1.0
    mobility: float = 0.35
    force: float = 0.8
    protocol: str = "sighted"
    blind_flip_interval: int = 12
    destroyed_jitter: float = 0.45
    entropy_scale: float = 1.0
    entropy_smoothing: float = 0.12


@dataclass(frozen=True)
class EntropySummary:
    """Aggregated statistics for the entropy identity audit."""

    seed: int
    temperature: float
    trial_id: int
    protocol: str
    mu_answer_sum: float
    entropy_sum: float
    entropy_residual: float
    theil_sen_slope: float
    theil_sen_intercept: float
    slope_ci_low: float
    slope_ci_high: float
    spearman_rho: float
    spearman_pvalue: float

    def as_row(self) -> Dict[str, str]:
        return {
            "seed": str(self.seed),
            "T": f"{self.temperature:.6f}",
            "trial_id": str(self.trial_id),
            "protocol": self.protocol,
            "mu_answer_sum": f"{self.mu_answer_sum:.10f}",
            "entropy_sum": f"{self.entropy_sum:.10f}",
            "entropy_residual": f"{self.entropy_residual:.12f}",
            "theil_sen_slope": f"{self.theil_sen_slope:.10f}",
            "theil_sen_intercept": f"{self.theil_sen_intercept:.10f}",
            "slope_ci_low": f"{self.slope_ci_low:.10f}",
            "slope_ci_high": f"{self.slope_ci_high:.10f}",
            "spearman_rho": f"{self.spearman_rho:.10f}",
            "spearman_pvalue": f"{self.spearman_pvalue:.12e}",
        }


@dataclass(frozen=True)
class RunResult:
    ledger_rows: List[MutableMapping[str, float | int | str]]
    summaries: List[EntropySummary]
    metadata: Dict[str, float | int | str]
    series_rows: List[MutableMapping[str, float | int | str]]


def _trial_seed(base_seed: int, temp_index: int, trial_id: int) -> int:
    return base_seed * 10_000 + temp_index * 1_000 + trial_id


def _force_schedule(config: EntropyConfig, rng: random.Random) -> Iterator[float]:
    base = config.force
    if config.protocol == "sighted":
        for _ in range(config.steps):
            yield base
    elif config.protocol == "blind":
        sign = 1
        for step in range(config.steps):
            if step % max(1, config.blind_flip_interval) == 0 and step:
                sign *= -1
            yield base * sign
    elif config.protocol == "destroyed":
        for _ in range(config.steps):
            sign = -1 if rng.random() < 0.5 else 1
            jitter = 0.4 + config.destroyed_jitter * rng.random()
            yield sign * base * jitter
    else:
        raise ValueError(f"Unsupported protocol: {config.protocol}")


def _normalise_noise(noise: List[float]) -> List[float]:
    if not noise:
        return []
    mean_noise = sum(noise) / len(noise)
    var_noise = sum((val - mean_noise) ** 2 for val in noise) / len(noise)
    if var_noise <= 1e-12:
        return [0.0 for _ in noise]
    scale = 1.0 / math.sqrt(var_noise)
    return [(val - mean_noise) * scale for val in noise]


def _entropy_delta(
    mu_increment: float,
    new_position: float,
    prev_position: float,
    config: EntropyConfig,
) -> float:
    gradient = math.tanh(new_position) - math.tanh(prev_position)
    return config.entropy_scale * mu_increment + config.entropy_smoothing * gradient


def _theil_sen_statistics(xs: Sequence[float], ys: Sequence[float]) -> Tuple[float, float, float, float]:
    n = len(xs)
    slopes: List[float] = []
    for i in range(n):
        for j in range(i + 1, n):
            if xs[j] == xs[i]:
                continue
            slopes.append((ys[j] - ys[i]) / (xs[j] - xs[i]))
    if not slopes:
        slope = 0.0
        intercept = float(statistics.median(ys)) if ys else 0.0
        return slope, intercept, slope, slope
    slopes.sort()
    slope = statistics.median(slopes)
    intercepts = [ys[idx] - slope * xs[idx] for idx in range(n)]
    intercept = statistics.median(intercepts)
    low = _quantile(slopes, 0.025)
    high = _quantile(slopes, 0.975)
    return slope, intercept, low, high


def _quantile(values: Sequence[float], q: float) -> float:
    if not values:
        return 0.0
    if q <= 0.0:
        return values[0]
    if q >= 1.0:
        return values[-1]
    position = q * (len(values) - 1)
    lower = int(math.floor(position))
    upper = int(math.ceil(position))
    if lower == upper:
        return values[lower]
    weight = position - lower
    return values[lower] * (1 - weight) + values[upper] * weight


def _rank(values: Sequence[float]) -> List[float]:
    n = len(values)
    indexed = sorted(range(n), key=lambda idx: values[idx])
    ranks = [0.0] * n
    i = 0
    while i < n:
        j = i
        while j + 1 < n and values[indexed[j + 1]] == values[indexed[i]]:
            j += 1
        rank_value = (i + j + 2) / 2.0
        for k in range(i, j + 1):
            ranks[indexed[k]] = rank_value
        i = j + 1
    return ranks


def _spearman(xs: Sequence[float], ys: Sequence[float]) -> Tuple[float, float]:
    if len(xs) != len(ys):
        raise ValueError("Spearman samples must share length")
    n = len(xs)
    if n < 3:
        return 0.0, 1.0
    rank_x = _rank(xs)
    rank_y = _rank(ys)
    mean_x = sum(rank_x) / n
    mean_y = sum(rank_y) / n
    cov = sum((rank_x[i] - mean_x) * (rank_y[i] - mean_y) for i in range(n))
    std_x = math.sqrt(sum((rank - mean_x) ** 2 for rank in rank_x))
    std_y = math.sqrt(sum((rank - mean_y) ** 2 for rank in rank_y))
    if std_x == 0.0 or std_y == 0.0:
        return 0.0, 1.0
    rho = cov / (std_x * std_y)
    rho = max(-1.0, min(1.0, rho))
    t_stat = abs(rho) * math.sqrt((n - 2) / max(1e-12, 1.0 - rho**2))
    # Two-sided p-value via normal approximation of the t-distribution tail.
    p = math.erfc(t_stat / math.sqrt(2.0))
    return rho, p


def _simulate_single_trial(
    config: EntropyConfig,
    seed: int,
    temp_index: int,
    temperature: float,
    trial_id: int,
) -> Tuple[List[MutableMapping[str, float | int | str]], EntropySummary, List[MutableMapping[str, float | int | str]]]:
    trial_rng = random.Random(_trial_seed(seed, temp_index, trial_id))
    position = 0.0
    mu_sum = 0.0
    entropy_sum = 0.0
    mu_samples: List[float] = []
    entropy_samples: List[float] = []
    ledger_rows: List[MutableMapping[str, float | int | str]] = []
    series_rows: List[MutableMapping[str, float | int | str]] = []

    forces = list(_force_schedule(config, trial_rng))
    steps = len(forces)
    if steps == 0:
        raise ValueError("Simulation produced no steps")

    variance = 2.0 * config.mobility * K_BOLTZMANN * temperature * config.dt
    raw_noise = [trial_rng.gauss(0.0, 1.0) for _ in range(steps)]
    normalised_noise = _normalise_noise(raw_noise)

    for step_index, (force, noise) in enumerate(zip(forces, normalised_noise)):
        drift = config.mobility * force * config.dt
        dx = drift + math.sqrt(variance) * noise
        new_position = position + dx
        mu_increment = (force * dx) / (K_BOLTZMANN * temperature)
        entropy_increment = _entropy_delta(mu_increment, new_position, position, config)
        mu_sum += mu_increment
        entropy_sum += entropy_increment

        ledger_row: MutableMapping[str, float | int | str] = {
            "module": "entropy_identity",
            "protocol": config.protocol,
            "seed": seed,
            "T": temperature,
            "trial_id": trial_id,
            "step": step_index,
            "dt": config.dt,
            "force": force,
            "dx": dx,
            "position": new_position,
            "mu_answer": mu_increment,
            "entropy_delta": entropy_increment,
        }
        ledger_rows.append(ledger_row)

        series_rows.append(
            {
                "seed": seed,
                "T": temperature,
                "trial_id": trial_id,
                "step": step_index,
                "mu_cumulative": mu_sum,
                "entropy_cumulative": entropy_sum,
            }
        )

        mu_samples.append(mu_increment)
        entropy_samples.append(entropy_increment)
        position = new_position

    slope, intercept, low, high = _theil_sen_statistics(mu_samples, entropy_samples)
    rho, p_value = _spearman(mu_samples, entropy_samples)

    summary = EntropySummary(
        seed=seed,
        temperature=temperature,
        trial_id=trial_id,
        protocol=config.protocol,
        mu_answer_sum=mu_sum,
        entropy_sum=entropy_sum,
        entropy_residual=entropy_sum - mu_sum,
        theil_sen_slope=slope,
        theil_sen_intercept=intercept,
        slope_ci_low=low,
        slope_ci_high=high,
        spearman_rho=rho,
        spearman_pvalue=p_value,
    )
    return ledger_rows, summary, series_rows


def _summaries_from_rows(
    rows: Iterable[MutableMapping[str, float | int | str]]
) -> Tuple[List[EntropySummary], List[MutableMapping[str, float | int | str]]]:
    grouped: Dict[Tuple[int, float, int, str], Dict[str, List[float] | float]] = {}
    step_order: Dict[Tuple[int, float, int, str], List[int]] = {}
    for row in rows:
        seed = int(row["seed"])
        temperature = float(row["T"])
        trial_id = int(row["trial_id"])
        protocol = str(row["protocol"])
        key = (seed, temperature, trial_id, protocol)
        state = grouped.setdefault(key, {"mu": [], "entropy": []})
        (state["mu"]).append(float(row.get("mu_answer", 0.0)))
        (state["entropy"]).append(float(row.get("entropy_delta", 0.0)))
        step_order.setdefault(key, []).append(int(row.get("step", len(step_order.get(key, [])))))

    summaries: List[EntropySummary] = []
    series_rows: List[MutableMapping[str, float | int | str]] = []
    for (seed, temperature, trial_id, protocol), state in grouped.items():
        mu_samples = list(state["mu"])
        entropy_samples = list(state["entropy"])
        slope, intercept, low, high = _theil_sen_statistics(mu_samples, entropy_samples)
        rho, p_value = _spearman(mu_samples, entropy_samples)
        mu_sum = sum(mu_samples)
        entropy_sum = sum(entropy_samples)
        cumulative_mu = 0.0
        cumulative_entropy = 0.0
        steps = step_order[(seed, temperature, trial_id, protocol)]
        for step, mu_inc, entropy_inc in zip(steps, mu_samples, entropy_samples):
            cumulative_mu += mu_inc
            cumulative_entropy += entropy_inc
            series_rows.append(
                {
                    "seed": seed,
                    "T": temperature,
                    "trial_id": trial_id,
                    "step": step,
                    "mu_cumulative": cumulative_mu,
                    "entropy_cumulative": cumulative_entropy,
                }
            )
        summaries.append(
            EntropySummary(
                seed=seed,
                temperature=temperature,
                trial_id=trial_id,
                protocol=protocol,
                mu_answer_sum=mu_sum,
                entropy_sum=entropy_sum,
                entropy_residual=entropy_sum - mu_sum,
                theil_sen_slope=slope,
                theil_sen_intercept=intercept,
                slope_ci_low=low,
                slope_ci_high=high,
                spearman_rho=rho,
                spearman_pvalue=p_value,
            )
        )

    summaries.sort(key=lambda item: (item.seed, item.temperature, item.trial_id))
    series_rows.sort(key=lambda row: (row["seed"], row["T"], row["trial_id"], row["step"]))
    return summaries, series_rows


def execute(config: EntropyConfig) -> RunResult:
    ledger_rows: List[MutableMapping[str, float | int | str]] = []
    summaries: List[EntropySummary] = []
    series_rows: List[MutableMapping[str, float | int | str]] = []

    for seed in config.seeds:
        for temp_index, temperature in enumerate(config.temps):
            for trial_id in range(config.trials_per_condition):
                trial_rows, summary, trial_series = _simulate_single_trial(
                    config, seed, temp_index, temperature, trial_id
                )
                ledger_rows.extend(trial_rows)
                summaries.append(summary)
                series_rows.extend(trial_series)

    metadata = {
        "k_B": K_BOLTZMANN,
        "protocol": config.protocol,
        "steps": config.steps,
        "dt": config.dt,
        "mobility": config.mobility,
        "force": config.force,
        "entropy_scale": config.entropy_scale,
        "entropy_smoothing": config.entropy_smoothing,
        "num_trials": len(summaries),
    }
    return RunResult(
        ledger_rows=ledger_rows,
        summaries=summaries,
        metadata=metadata,
        series_rows=series_rows,
    )


def _write_summary_csv(path: Path, summaries: Sequence[EntropySummary]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "seed",
                "T",
                "trial_id",
                "protocol",
                "mu_answer_sum",
                "entropy_sum",
                "entropy_residual",
                "theil_sen_slope",
                "theil_sen_intercept",
                "slope_ci_low",
                "slope_ci_high",
                "spearman_rho",
                "spearman_pvalue",
            ],
        )
        writer.writeheader()
        for summary in summaries:
            writer.writerow(summary.as_row())


def _write_series_csv(path: Path, series_rows: Sequence[MutableMapping[str, float | int | str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "seed",
                "T",
                "trial_id",
                "step",
                "mu_cumulative",
                "entropy_cumulative",
            ],
        )
        writer.writeheader()
        for row in series_rows:
            writer.writerow(
                {
                    "seed": row["seed"],
                    "T": f"{float(row["T"]):.6f}",
                    "trial_id": row["trial_id"],
                    "step": row["step"],
                    "mu_cumulative": f"{float(row["mu_cumulative"]):.10f}",
                    "entropy_cumulative": f"{float(row["entropy_cumulative"]):.10f}",
                }
            )


def _write_metadata(path: Path, metadata: Dict[str, float | int | str], digest: str) -> None:
    enriched = dict(metadata)
    enriched["ledger_digest_sha256"] = digest
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(enriched, handle, indent=2, sort_keys=True)
        handle.write("\n")


def _replay_synthetic_ledger(path: Path) -> RunResult:
    entries = ledger_io.load_ledger(path)
    ledger_rows = [dict(entry.payload) for entry in entries]
    summaries, series_rows = _summaries_from_rows(ledger_rows)
    metadata = {
        "k_B": K_BOLTZMANN,
        "protocol": "synthetic",
        "steps": max(int(row.get("step", 0)) for row in ledger_rows) + 1 if ledger_rows else 0,
        "dt": float(ledger_rows[0].get("dt", 1.0)) if ledger_rows else 1.0,
        "num_trials": len(summaries),
    }
    return RunResult(
        ledger_rows=ledger_rows,
        summaries=summaries,
        metadata=metadata,
        series_rows=series_rows,
    )


def run_entropy(
    config: EntropyConfig,
    synthetic_ledger: Path | None = None,
) -> RunResult:
    if synthetic_ledger is not None:
        return _replay_synthetic_ledger(synthetic_ledger)
    return execute(config)


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Entropy identity diffusion runner with μ-ledger logging"
    )
    parser.add_argument("--output-dir", type=Path, required=True, help="Directory for artefacts")
    parser.add_argument("--seeds", type=int, nargs="*", default=[0, 1, 2], help="Deterministic RNG seeds")
    parser.add_argument(
        "--temps",
        type=float,
        nargs="*",
        default=[0.5, 1.0, 1.5],
        help="Temperature grid for the diffusion experiments",
    )
    parser.add_argument(
        "--trials-per-condition",
        type=int,
        default=40,
        help="Number of trials for each (seed, T) pair",
    )
    parser.add_argument(
        "--protocol",
        choices=["sighted", "blind", "destroyed"],
        default="sighted",
        help="Protocol variant controlling force schedules",
    )
    parser.add_argument("--steps", type=int, default=96, help="Number of time steps per trial")
    parser.add_argument("--dt", type=float, default=1.0, help="Time increment per step")
    parser.add_argument("--mobility", type=float, default=0.35, help="Mobility parameter")
    parser.add_argument("--force", type=float, default=0.8, help="Base applied force")
    parser.add_argument(
        "--blind-flip-interval",
        type=int,
        default=12,
        help="Flip interval for blind force schedule",
    )
    parser.add_argument(
        "--destroyed-jitter",
        type=float,
        default=0.45,
        help="Relative jitter amplitude for destroyed protocol",
    )
    parser.add_argument(
        "--entropy-scale",
        type=float,
        default=1.0,
        help="Scaling factor applied to μ increments when generating entropy deltas",
    )
    parser.add_argument(
        "--entropy-smoothing",
        type=float,
        default=0.12,
        help="Deterministic smoothing term applied to entropy deltas",
    )
    parser.add_argument(
        "--synthetic-ledger",
        type=Path,
        default=None,
        help="Replay an existing ledger instead of simulating",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = _parse_args(argv)
    output_dir: Path = args.output_dir

    config = EntropyConfig(
        output_dir=output_dir,
        seeds=args.seeds,
        temps=args.temps,
        trials_per_condition=args.trials_per_condition,
        steps=args.steps,
        dt=args.dt,
        mobility=args.mobility,
        force=args.force,
        protocol=args.protocol,
        blind_flip_interval=args.blind_flip_interval,
        destroyed_jitter=args.destroyed_jitter,
        entropy_scale=args.entropy_scale,
        entropy_smoothing=args.entropy_smoothing,
    )

    result = run_entropy(config, synthetic_ledger=args.synthetic_ledger)

    ledger_path = output_dir / "entropy_steps.jsonl"
    summary_path = output_dir / "entropy_summary.csv"
    series_path = output_dir / "entropy_series.csv"
    metadata_path = output_dir / "entropy_metadata.json"

    ledger_io.dump_ledger(result.ledger_rows, ledger_path)
    ledger_entries = ledger_io.load_ledger(ledger_path)
    digest = ledger_io.ledger_digest(ledger_entries)

    _write_summary_csv(summary_path, result.summaries)
    _write_series_csv(series_path, result.series_rows)
    _write_metadata(metadata_path, result.metadata, digest)


if __name__ == "__main__":  # pragma: no cover - CLI entry point
    main()

