#!/usr/bin/env python3
"""Quantify finite signal speed predictions from the NUSD ledger."""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from typing import Iterable, List, Sequence


@dataclass
class SpeedResult:
    frame: str
    candidate_speed: float
    mu_question: float
    mu_answer: float
    mu_total: float


@dataclass
class Trajectory:
    time: List[float]
    position: List[float]


def generate_trajectory(speed: float, steps: int) -> Trajectory:
    time = [float(t) for t in range(steps)]
    position = [speed * t for t in time]
    return Trajectory(time=time, position=position)


def transform_frame(traj: Trajectory, drift: float) -> Trajectory:
    if abs(drift) >= 1.0:
        raise ValueError("drift must be strictly within (-1, 1) for Lorentz transform")
    gamma = 1.0 / math.sqrt(1.0 - drift * drift)
    new_time: List[float] = []
    new_pos: List[float] = []
    for t, x in zip(traj.time, traj.position):
        new_time.append(gamma * (t - drift * x))
        new_pos.append(gamma * (x - drift * t))
    return Trajectory(time=new_time, position=new_pos)


def mu_question(candidate_speed: float) -> float:
    return math.log2(1.0 + candidate_speed ** 2)


def mu_answer(traj: Trajectory, candidate_speed: float) -> float:
    penalty = 0.0
    for idx in range(1, len(traj.time)):
        dt = traj.time[idx] - traj.time[idx - 1]
        dx = abs(traj.position[idx] - traj.position[idx - 1])
        if dt <= 0:
            continue
        max_allowed = candidate_speed * dt
        if dx > max_allowed + 1e-12:
            penalty += (dx - max_allowed) ** 2
    return math.log2(1.0 + penalty)


def evaluate_frame(label: str, traj: Trajectory, speeds: Sequence[float]) -> List[SpeedResult]:
    results: List[SpeedResult] = []
    for candidate in speeds:
        question = mu_question(candidate)
        answer = mu_answer(traj, candidate)
        results.append(
            SpeedResult(
                frame=label,
                candidate_speed=candidate,
                mu_question=question,
                mu_answer=answer,
                mu_total=question + answer,
            )
        )
    return results


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--actual-speed", type=float, default=1.0, help="true propagation speed")
    parser.add_argument("--steps", type=int, default=32, help="number of time steps to simulate")
    parser.add_argument(
        "--candidates",
        type=float,
        nargs="*",
        default=[0.5, 1.0, 1.5, 2.0, 3.0],
        help="candidate speeds to evaluate",
    )
    parser.add_argument(
        "--drifts",
        type=float,
        nargs="*",
        default=[0.0, -0.4, 0.4],
        help="frame drifts (co-moving observers) to test",
    )
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    base = generate_trajectory(args.actual_speed, args.steps)
    frames = [(f"drift={drift:+.2f}", transform_frame(base, drift)) for drift in args.drifts]
    header = f"{'frame':<12}{'candidate':>12}{'μ_question':>14}{'μ_answer':>12}{'μ_total':>12}"
    print(header)
    print("-" * len(header))
    for frame_label, traj in frames:
        results = evaluate_frame(frame_label, traj, args.candidates)
        for entry in results:
            print(
                f"{entry.frame:<12}{entry.candidate_speed:>12.2f}{entry.mu_question:>14.3f}"
                f"{entry.mu_answer:>12.3f}{entry.mu_total:>12.3f}"
            )
        best = min(results, key=lambda result: result.mu_total)
        print(
            f"  -> minimal μ_total in {frame_label} occurs at speed {best.candidate_speed:.2f}"
            f" ({best.mu_total:.6f} bits)"
        )


if __name__ == "__main__":
    main()
