"""Compositional learner: try periods related (factors/multiples) to recent successes first.

Refinement step after a hit scans proper divisors of the verifying k so the
reported period is the minimum, not a multiple. Required for correctness:
the period-k LASSERT formula encodes shift-by-k invariance, which is a
superset of "minimum period k".
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Optional

from .brute_force import BruteForceProbe, BruteForceResult
from .encoding import run_period_claim
from .streams import Stream


def _factors(k: int, lo: int, hi: int) -> List[int]:
    return [d for d in range(lo, hi + 1) if d > 0 and k % d == 0]


def _multiples(k: int, lo: int, hi: int) -> List[int]:
    out = []
    m = k
    while True:
        m += k
        if m > hi:
            break
        if m >= lo:
            out.append(m)
    return out


def candidate_order(history: List[int], min_k: int, max_k: int) -> List[int]:
    """Candidate periods to try, biased by recent-first history + factors/multiples."""
    seen: set = set()
    ordered: List[int] = []

    def add(k: int) -> None:
        if min_k <= k <= max_k and k not in seen:
            seen.add(k)
            ordered.append(k)

    for k in history:
        add(k)
    for k in history:
        for d in _factors(k, min_k, max_k):
            add(d)
        for m in _multiples(k, min_k, max_k):
            add(m)
    for k in range(min_k, max_k + 1):
        add(k)
    return ordered


@dataclass
class CompositionalLearner:
    min_k: int
    max_k: int
    history_cap: int = 32
    history: List[int] = field(default_factory=list)

    def reset(self) -> None:
        self.history.clear()

    def predict(self, stream: Stream) -> BruteForceResult:
        order = candidate_order(self.history, self.min_k, self.max_k)
        probes: List[BruteForceProbe] = []
        total_mu = 0
        predicted: Optional[int] = None
        for k in order:
            verified, mu_paid, _state, _prog = run_period_claim(stream, k)
            probes.append(BruteForceProbe(k=k, verified=verified, mu_paid=mu_paid))
            total_mu += mu_paid
            if not verified:
                continue
            already_failed = {p.k for p in probes if not p.verified}
            min_verified = k
            for d in _factors(k, self.min_k, k - 1):
                if d in already_failed:
                    continue
                v2, mu2, _s2, _p2 = run_period_claim(stream, d)
                probes.append(BruteForceProbe(k=d, verified=v2, mu_paid=mu2))
                total_mu += mu2
                if v2:
                    min_verified = d
                    break
            predicted = min_verified
            self.history = [predicted] + [h for h in self.history if h != predicted]
            if len(self.history) > self.history_cap:
                self.history = self.history[: self.history_cap]
            break
        return BruteForceResult(
            predicted_period=predicted,
            total_mu=total_mu,
            probes=probes,
        )
