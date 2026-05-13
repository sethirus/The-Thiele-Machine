"""Eval harness: brute-force vs random baseline, bucketed by ground-truth period."""
from __future__ import annotations

import random
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from .brute_force import brute_force_period
from .streams import LabeledStream


def _correct(predicted: Optional[int], truth: Optional[int]) -> bool:
    return predicted == truth


@dataclass(frozen=True)
class StreamEvalRow:
    stream: LabeledStream
    predicted_period: Optional[int]
    correct: bool
    mu_paid: int
    num_probes: int


@dataclass(frozen=True)
class BucketStats:
    label: str
    count: int
    correct: int
    mean_mu: float
    mean_probes: float

    @property
    def accuracy(self) -> float:
        return self.correct / self.count if self.count else float("nan")


def evaluate_brute_force(
    dataset: List[LabeledStream],
    max_k: int,
) -> Tuple[List[StreamEvalRow], Dict[Optional[int], BucketStats]]:
    """Run brute-force on every stream; return (rows, per-truth bucket stats)."""
    rows: List[StreamEvalRow] = []
    for labeled in dataset:
        result = brute_force_period(labeled.bits, max_k=max_k)
        rows.append(StreamEvalRow(
            stream=labeled,
            predicted_period=result.predicted_period,
            correct=_correct(result.predicted_period, labeled.period),
            mu_paid=result.total_mu,
            num_probes=result.num_probes,
        ))
    return rows, _bucket_by_truth(rows)


def evaluate_random_baseline(
    dataset: List[LabeledStream],
    max_k: int,
    seed: int = 0,
) -> Tuple[List[StreamEvalRow], Dict[Optional[int], BucketStats]]:
    """Random guesser baseline: pick k uniformly in [2, max_k], no probing, µ=0."""
    rng = random.Random(seed)
    rows: List[StreamEvalRow] = []
    for labeled in dataset:
        guess = rng.randint(2, max_k)
        rows.append(StreamEvalRow(
            stream=labeled,
            predicted_period=guess,
            correct=_correct(guess, labeled.period),
            mu_paid=0,
            num_probes=0,
        ))
    return rows, _bucket_by_truth(rows)


def _bucket_by_truth(
    rows: List[StreamEvalRow],
) -> Dict[Optional[int], BucketStats]:
    by_truth: Dict[Optional[int], List[StreamEvalRow]] = {}
    for r in rows:
        by_truth.setdefault(r.stream.period, []).append(r)
    out: Dict[Optional[int], BucketStats] = {}
    for truth, group in by_truth.items():
        out[truth] = BucketStats(
            label=("period " + str(truth)) if truth is not None else "non-periodic",
            count=len(group),
            correct=sum(1 for r in group if r.correct),
            mean_mu=sum(r.mu_paid for r in group) / len(group),
            mean_probes=sum(r.num_probes for r in group) / len(group),
        )
    return out


def format_table(stats: Dict[Optional[int], BucketStats]) -> str:
    """Pretty-print the bucket-stats table sorted by ground-truth period."""
    def sort_key(k):
        return (1, 0) if k is None else (0, k)
    keys = sorted(stats.keys(), key=sort_key)
    lines = [
        f"{'truth':>14} {'count':>6} {'correct':>8} {'acc':>7} {'mean_mu':>10} {'probes':>7}",
        "-" * 60,
    ]
    for k in keys:
        s = stats[k]
        lines.append(
            f"{s.label:>14} {s.count:>6} {s.correct:>8} "
            f"{s.accuracy:>7.2%} {s.mean_mu:>10.1f} {s.mean_probes:>7.2f}"
        )
    return "\n".join(lines)
