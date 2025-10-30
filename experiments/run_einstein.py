"""Biased diffusion runner for the Einstein relation experiment."""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path
import random
from typing import Dict, Iterable, Iterator, List, MutableMapping, Sequence, Tuple

from . import ledger_io

K_BOLTZMANN = 1.0


@dataclass(frozen=True)
class EinsteinConfig:
    """Configuration parameters for deterministic Einstein simulations."""

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


@dataclass(frozen=True)
class EinsteinSummary:
    """Aggregated metrics for a single biased diffusion trial."""

    seed: int
    temperature: float
    trial_id: int
    protocol: str
    diffusion: float
    mobility: float
    residual: float
    mu_answer_sum: float
    drift_velocity: float
    msd: float
    cost_proxy: float

    @property
    def diffusion_over_kT(self) -> float:
        return self.diffusion / (K_BOLTZMANN * self.temperature)

    def as_row(self) -> Dict[str, str]:
        return {
            "seed": str(self.seed),
            "T": f"{self.temperature:.6f}",
            "trial_id": str(self.trial_id),
            "protocol": self.protocol,
            "diffusion": f"{self.diffusion:.10f}",
            "mobility": f"{self.mobility:.10f}",
            "diffusion_over_kT": f"{self.diffusion_over_kT:.10f}",
            "residual": f"{self.residual:.12f}",
            "mu_answer_sum": f"{self.mu_answer_sum:.10f}",
            "drift_velocity": f"{self.drift_velocity:.10f}",
            "msd": f"{self.msd:.10f}",
            "cost_proxy": f"{self.cost_proxy:.10f}",
        }


@dataclass(frozen=True)
class RunResult:
    ledger_rows: List[MutableMapping[str, float | int | str]]
    summaries: List[EinsteinSummary]
    metadata: Dict[str, float | int | str]


def _trial_seed(base_seed: int, temp_index: int, trial_id: int) -> int:
    return base_seed * 10_000 + temp_index * 1_000 + trial_id


def _force_schedule(config: EinsteinConfig, rng: random.Random) -> Iterator[float]:
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


def _simulate_single_trial(
    config: EinsteinConfig,
    seed: int,
    temp_index: int,
    temperature: float,
    trial_id: int,
) -> Tuple[List[MutableMapping[str, float | int | str]], EinsteinSummary]:
    trial_rng = random.Random(_trial_seed(seed, temp_index, trial_id))
    position = 0.0
    sum_dx = 0.0
    sum_dx2 = 0.0
    mu_sum = 0.0
    sum_dx_force = 0.0
    sum_force_sq = 0.0
    cost_proxy = 0.0
    forces = list(_force_schedule(config, trial_rng))
    steps = len(forces)
    if steps == 0:
        raise ValueError("Simulation produced no steps")

    variance = 2.0 * config.mobility * K_BOLTZMANN * temperature * config.dt
    noise_samples = [trial_rng.gauss(0.0, 1.0) for _ in range(steps)]
    mean_noise = sum(noise_samples) / steps
    var_noise = sum((val - mean_noise) ** 2 for val in noise_samples) / steps
    if var_noise <= 1e-12:
        normalised_noise = [0.0 for _ in range(steps)]
    else:
        scale = 1.0 / math.sqrt(var_noise)
        normalised_noise = [(val - mean_noise) * scale for val in noise_samples]

    ledger_rows: List[MutableMapping[str, float | int | str]] = []

    for step_index, (force, noise) in enumerate(zip(forces, normalised_noise)):
        drift = config.mobility * force * config.dt
        dx = drift + math.sqrt(variance) * noise
        position += dx
        sum_dx += dx
        sum_dx2 += dx * dx
        mu_increment = (force * dx) / (K_BOLTZMANN * temperature)
        mu_sum += mu_increment
        sum_dx_force += dx * force
        sum_force_sq += force * force
        cost_proxy += abs(position)

        ledger_rows.append(
            {
                "module": "einstein",
                "protocol": config.protocol,
                "seed": seed,
                "T": temperature,
                "trial_id": trial_id,
                "step": step_index,
                "dt": config.dt,
                "force": force,
                "dx": dx,
                "position": position,
                "mu_answer": mu_increment,
                "abs_position": abs(position),
            }
        )

    mean_dx = sum_dx / steps
    mean_dx2 = sum_dx2 / steps
    variance_dx = max(0.0, mean_dx2 - mean_dx**2)
    diffusion = variance_dx / (2.0 * config.dt)
    mobility = sum_dx_force / (sum_force_sq * config.dt) if sum_force_sq > 0.0 else 0.0
    residual = diffusion - mobility * K_BOLTZMANN * temperature
    drift_velocity = mean_dx / config.dt
    msd = mean_dx2
    cost_average = cost_proxy / steps

    summary = EinsteinSummary(
        seed=seed,
        temperature=temperature,
        trial_id=trial_id,
        protocol=config.protocol,
        diffusion=diffusion,
        mobility=mobility,
        residual=residual,
        mu_answer_sum=mu_sum,
        drift_velocity=drift_velocity,
        msd=msd,
        cost_proxy=cost_average,
    )
    return ledger_rows, summary


def execute(config: EinsteinConfig) -> RunResult:
    ledger_rows: List[MutableMapping[str, float | int | str]] = []
    summaries: List[EinsteinSummary] = []

    for seed in config.seeds:
        for temp_index, temperature in enumerate(config.temps):
            for trial_id in range(config.trials_per_condition):
                trial_rows, summary = _simulate_single_trial(
                    config, seed, temp_index, temperature, trial_id
                )
                ledger_rows.extend(trial_rows)
                summaries.append(summary)

    metadata = {
        "k_B": K_BOLTZMANN,
        "protocol": config.protocol,
        "steps": config.steps,
        "dt": config.dt,
        "mobility": config.mobility,
        "force": config.force,
        "num_trials": len(summaries),
    }
    return RunResult(ledger_rows=ledger_rows, summaries=summaries, metadata=metadata)


def _write_summary_csv(path: Path, summaries: Sequence[EinsteinSummary]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "seed",
                "T",
                "trial_id",
                "protocol",
                "diffusion",
                "mobility",
                "diffusion_over_kT",
                "residual",
                "mu_answer_sum",
                "drift_velocity",
                "msd",
                "cost_proxy",
            ],
        )
        writer.writeheader()
        for summary in summaries:
            writer.writerow(summary.as_row())


def _write_metadata(path: Path, metadata: Dict[str, float | int | str], digest: str) -> None:
    enriched = dict(metadata)
    enriched["ledger_digest_sha256"] = digest
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(enriched, handle, indent=2, sort_keys=True)
        handle.write("\n")


def _summaries_from_ledger(entries: Iterable[ledger_io.LedgerEntry]) -> List[EinsteinSummary]:
    grouped: Dict[Tuple[int, float, int, str], Dict[str, float]] = {}
    for entry in entries:
        payload = entry.payload
        key = (
            int(payload["seed"]),
            float(payload["T"]),
            int(payload["trial_id"]),
            str(payload["protocol"]),
        )
        state = grouped.setdefault(
            key,
            {
                "sum_dx": 0.0,
                "sum_dx2": 0.0,
                "sum_dx_force": 0.0,
                "sum_force_sq": 0.0,
                "steps": 0.0,
                "mu_sum": 0.0,
                "cost_proxy": 0.0,
                "dt": float(payload.get("dt", 1.0)),
            },
        )
        dx = float(payload.get("dx", 0.0))
        force = float(payload.get("force", 0.0))
        state["sum_dx"] += dx
        state["sum_dx2"] += dx * dx
        state["sum_dx_force"] += dx * force
        state["sum_force_sq"] += force * force
        state["steps"] += 1.0
        state["mu_sum"] += float(payload.get("mu_answer", 0.0))
        state["cost_proxy"] += float(payload.get("abs_position", abs(dx)))

    summaries: List[EinsteinSummary] = []
    for (seed, temperature, trial_id, protocol), state in grouped.items():
        steps = int(state["steps"]) or 1
        dt = state["dt"]
        mean_dx = state["sum_dx"] / steps
        mean_dx2 = state["sum_dx2"] / steps
        variance_dx = max(0.0, mean_dx2 - mean_dx**2)
        diffusion = variance_dx / (2.0 * dt)
        denom = state["sum_force_sq"] * dt
        mobility = state["sum_dx_force"] / denom if denom > 0.0 else 0.0
        residual = diffusion - mobility * K_BOLTZMANN * temperature
        drift_velocity = mean_dx / dt
        msd = mean_dx2
        cost_average = state["cost_proxy"] / steps
        summaries.append(
            EinsteinSummary(
                seed=seed,
                temperature=temperature,
                trial_id=trial_id,
                protocol=protocol,
                diffusion=diffusion,
                mobility=mobility,
                residual=residual,
                mu_answer_sum=state["mu_sum"],
                drift_velocity=drift_velocity,
                msd=msd,
                cost_proxy=cost_average,
            )
        )

    summaries.sort(key=lambda item: (item.seed, item.temperature, item.trial_id))
    return summaries


def _replay_synthetic_ledger(path: Path) -> RunResult:
    entries = ledger_io.load_ledger(path)
    summaries = _summaries_from_ledger(entries)
    metadata = {
        "k_B": K_BOLTZMANN,
        "protocol": "synthetic",
        "steps": max(int(entry.payload.get("step", 0)) for entry in entries) + 1 if entries else 0,
        "dt": float(entries[0].payload.get("dt", 1.0)) if entries else 1.0,
        "num_trials": len(summaries),
    }
    ledger_rows = [dict(entry.payload) for entry in entries]
    return RunResult(ledger_rows=ledger_rows, summaries=summaries, metadata=metadata)


def run_einstein(config: EinsteinConfig, synthetic_ledger: Path | None = None) -> RunResult:
    if synthetic_ledger is not None:
        return _replay_synthetic_ledger(synthetic_ledger)
    return execute(config)


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Einstein relation biased diffusion runner")
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
        "--synthetic-ledger",
        type=Path,
        default=None,
        help="Replay an existing ledger instead of simulating",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = _parse_args(argv)
    output_dir: Path = args.output_dir

    config = EinsteinConfig(
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
    )

    result = run_einstein(config, synthetic_ledger=args.synthetic_ledger)

    ledger_path = output_dir / "einstein_steps.jsonl"
    summary_path = output_dir / "einstein_summary.csv"
    metadata_path = output_dir / "einstein_metadata.json"

    ledger_io.dump_ledger(result.ledger_rows, ledger_path)
    digest = ledger_io.ledger_digest(ledger_io.load_ledger(ledger_path))
    summaries = result.summaries
    _write_summary_csv(summary_path, summaries)
    _write_metadata(metadata_path, result.metadata, digest)


if __name__ == "__main__":  # pragma: no cover - CLI entry point
    main()
