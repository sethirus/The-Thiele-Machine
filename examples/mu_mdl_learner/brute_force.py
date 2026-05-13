"""Brute-force periodicity learner: ascending scan, stop at first certifying k."""
from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional

from .encoding import run_period_claim
from .streams import Stream


@dataclass(frozen=True)
class BruteForceProbe:
    k: int
    verified: bool
    mu_paid: int


@dataclass(frozen=True)
class BruteForceResult:
    predicted_period: Optional[int]
    total_mu: int
    probes: List[BruteForceProbe]

    @property
    def num_probes(self) -> int:
        return len(self.probes)


def brute_force_period(
    stream: Stream,
    max_k: int,
    min_k: int = 2,
) -> BruteForceResult:
    """Scan k in [min_k, max_k] and return the first certifying period."""
    if not (1 <= min_k <= max_k):
        raise ValueError(f"need 1 <= min_k <= max_k; got min_k={min_k}, max_k={max_k}")
    if max_k >= len(stream):
        raise ValueError(
            f"max_k must be < len(stream); got max_k={max_k}, len={len(stream)}"
        )

    probes: List[BruteForceProbe] = []
    total_mu = 0
    predicted: Optional[int] = None
    for k in range(min_k, max_k + 1):
        verified, mu_paid, _state, _prog = run_period_claim(stream, k)
        probes.append(BruteForceProbe(k=k, verified=verified, mu_paid=mu_paid))
        total_mu += mu_paid
        if verified:
            predicted = k
            break
    return BruteForceResult(
        predicted_period=predicted,
        total_mu=total_mu,
        probes=probes,
    )
