"""Bit-stream generator with exact-minimum-period labeling."""
from __future__ import annotations

import random
from dataclasses import dataclass
from typing import List, Optional, Tuple


Stream = Tuple[int, ...]


@dataclass(frozen=True)
class LabeledStream:
    bits: Stream
    period: Optional[int]
    source: str  # "periodic" | "random"


def is_period_k(bits: Stream, k: int) -> bool:
    """True iff bits[i] == bits[i+k] for all i with i+k < len(bits)."""
    n = len(bits)
    for i in range(n - k):
        if bits[i] != bits[i + k]:
            return False
    return True


def minimum_period(bits: Stream, max_k: int) -> Optional[int]:
    """Smallest k in [1, max_k] with is_period_k(bits, k); None if none works."""
    for k in range(1, max_k + 1):
        if is_period_k(bits, k):
            return k
    return None


def make_periodic(n: int, period: int, seed: int) -> Stream:
    """Stream of length n made by repeating a random `period`-bit pattern.

    Minimum period may be smaller if the random pattern has internal
    sub-period structure; filter with minimum_period() if exact.
    """
    rng = random.Random(seed)
    pattern = tuple(rng.randint(0, 1) for _ in range(period))
    return tuple(pattern[i % period] for i in range(n))


def make_random(n: int, seed: int) -> Stream:
    rng = random.Random(seed)
    return tuple(rng.randint(0, 1) for _ in range(n))


def make_dataset(
    n: int,
    periods: List[int],
    samples_per_period: int,
    random_samples: int,
    seed: int = 0,
    require_exact_min_period: bool = True,
    max_search_k: Optional[int] = None,
) -> List[LabeledStream]:
    """Labeled set of periodic + random streams; resamples to hit exact min-period."""
    if max_search_k is None:
        max_search_k = max(periods) if periods else n // 2
    out: List[LabeledStream] = []
    base = seed * 1_000_003
    counter = 0
    for k in periods:
        accepted = 0
        attempts = 0
        while accepted < samples_per_period:
            sample_seed = base + counter
            counter += 1
            attempts += 1
            bits = make_periodic(n, k, sample_seed)
            mp = minimum_period(bits, max_search_k)
            if require_exact_min_period and mp != k:
                if attempts > samples_per_period * 50:
                    raise RuntimeError(
                        f"could not produce {samples_per_period} streams of "
                        f"exact min-period {k} for n={n} after {attempts} tries"
                    )
                continue
            out.append(LabeledStream(bits=bits, period=k, source="periodic"))
            accepted += 1
    for _ in range(random_samples):
        sample_seed = base + counter
        counter += 1
        bits = make_random(n, sample_seed)
        mp = minimum_period(bits, max_search_k)
        out.append(LabeledStream(bits=bits, period=mp, source="random"))
    return out
