# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Semantic helpers for Bell/CHSH receipt enforcement.

This module intentionally lives under ``thielecpu`` so the VM can enforce
CHSH-related invariants without importing from ``tools``.

Convention matches ``tools/chsh_receipts.py``:
  S = E(1,1) + E(1,0) + E(0,1) - E(0,0)
where E(x,y) = P(a=b|x,y) - P(a!=b|x,y).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Dict, Tuple

CountKey = Tuple[int, int, int, int]
SettingKey = Tuple[int, int]

TSIRELSON_BOUND: Fraction = Fraction(5657, 2000)  # 2√2 ≈ 2.8285 (matches Coq kernel)
DEFAULT_ENFORCEMENT_MIN_TRIALS_PER_SETTING: int = 10

# CHSH value computation result (matches Coq kernel/Certification.v chsh_value)
def chsh_value(counts: BellCounts) -> Fraction:
    """Compute CHSH value from trial counts (matches Coq Certification.chsh_value)."""
    return counts.chsh()


@dataclass
class BellCounts:
    """Accumulates CHSH_TRIAL outcomes and computes CHSH when balanced."""

    counts: Dict[CountKey, int] = field(default_factory=dict)
    per_setting: Dict[SettingKey, int] = field(
        default_factory=lambda: {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
    )

    def update_trial(self, *, x: int, y: int, a: int, b: int) -> None:
        key = (int(x), int(y), int(a), int(b))
        self.counts[key] = int(self.counts.get(key, 0)) + 1
        self.per_setting[(int(x), int(y))] = int(self.per_setting.get((int(x), int(y)), 0)) + 1

    def is_balanced(self, *, min_trials_per_setting: int) -> bool:
        vals = list(self.per_setting.values())
        if len(vals) != 4:
            return False
        if any(v < int(min_trials_per_setting) for v in vals):
            return False
        return len(set(vals)) == 1

    def chsh(self) -> Fraction:
        def setting_correlator(x: int, y: int) -> Fraction:
            n = int(self.per_setting.get((x, y), 0))
            if n <= 0:
                return Fraction(0, 1)
            same = int(self.counts.get((x, y, 0, 0), 0)) + int(self.counts.get((x, y, 1, 1), 0))
            diff = int(self.counts.get((x, y, 0, 1), 0)) + int(self.counts.get((x, y, 1, 0), 0))
            return Fraction(same - diff, n)

        e00 = setting_correlator(0, 0)
        e01 = setting_correlator(0, 1)
        e10 = setting_correlator(1, 0)
        e11 = setting_correlator(1, 1)
        return e11 + e10 + e01 - e00


def is_supra_quantum(*, chsh: Fraction, bound: Fraction = TSIRELSON_BOUND) -> bool:
    return chsh > bound


__all__ = [
    "BellCounts",
    "CountKey",
    "SettingKey",
    "TSIRELSON_BOUND",
    "DEFAULT_ENFORCEMENT_MIN_TRIALS_PER_SETTING",
    "is_supra_quantum",
]
