from __future__ import annotations

"""Finite-quantum (finite-sample) prediction engines.

This module is deliberately narrow and operational:

- It produces a *finite multiset of CHSH trials* that represents the output of a
  "prediction engine" for a CHSH experiment.
- Trials are intended to be executed via the VM's dedicated `CHSH_TRIAL` opcode,
  making the observable receipt-defined and non-forgeable.

The main artifact here is a deterministic, exact-rational construction that hits
our conservative Tsirelson bound approximation exactly:

  TSIRELSON_BOUND = 5657/2000

This is not a full real-analysis derivation of $2\sqrt{2}$; it's an operational
finite-domain model that stays within the VM/kernel's admissibility threshold.
"""

from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, List

from tools.bell_operational import DatasetCounts, chsh_from_counts


@dataclass(frozen=True)
class QMTrial:
    x: int
    y: int
    a: int
    b: int


TSIRELSON_BOUND: Fraction = Fraction(5657, 2000)


def _repeat(trial: QMTrial, n: int) -> List[QMTrial]:
    return [trial for _ in range(int(n))]


def tsirelson_bound_trials(*, denom: int = 4000) -> List[QMTrial]:
    """Return a deterministic finite trial stream with CHSH exactly 5657/2000.

    Construction (balanced per setting):

    - For settings (1,1), (1,0), (0,1): correlator E=+1, so always a=b.
    - For setting (0,0): choose correlator E00 = 343/2000 so that
        S = 1 + 1 + 1 - E00 = 5657/2000.

      This yields:
        P_same = (1+E00)/2 = 2343/4000
        P_diff = (1-E00)/2 = 1657/4000

    `denom` must be a multiple of 4000 to realize these counts exactly.
    """

    if denom % 4000 != 0:
        raise ValueError("denom must be a multiple of 4000")

    scale = denom // 4000

    # Deterministic order: (x,y) lex, then outcome blocks.
    trials: List[QMTrial] = []

    # E=+1 settings: only (a,b)=(0,0) emitted.
    for (x, y) in [(0, 1), (1, 0), (1, 1)]:
        trials.extend(_repeat(QMTrial(x=x, y=y, a=0, b=0), denom))

    # (0,0) setting: mix same and diff outcomes.
    same = 2343 * scale
    diff = 1657 * scale
    trials.extend(_repeat(QMTrial(x=0, y=0, a=0, b=0), same))
    trials.extend(_repeat(QMTrial(x=0, y=0, a=0, b=1), diff))

    return trials


def _counts_from_trials(trials: Iterable[QMTrial]) -> DatasetCounts:
    counts = {}
    per_setting = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
    for t in trials:
        key = (int(t.x), int(t.y), int(t.a), int(t.b))
        counts[key] = int(counts.get(key, 0)) + 1
        per_setting[(int(t.x), int(t.y))] += 1

    n_vals = set(per_setting.values())
    if len(n_vals) != 1:
        raise ValueError(f"unbalanced trials per setting: {per_setting}")

    return DatasetCounts(n_per_setting=int(next(iter(n_vals))), counts=counts)


def chsh_from_trials(trials: Iterable[QMTrial]) -> Fraction:
    dataset = _counts_from_trials(trials)
    return chsh_from_counts(dataset)


__all__ = [
    "QMTrial",
    "TSIRELSON_BOUND",
    "tsirelson_bound_trials",
    "chsh_from_trials",
]
