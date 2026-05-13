"""MDL scoring.

  model bits = ceil(log2(max_k - min_k + 1)) + k    (period index + pattern)
  residual   = 0 if certified, else n               (whole stream literal)
  gain       = n - (model + residual)
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Optional

from .streams import Stream


def _ceil_log2(n: int) -> int:
    if n <= 1:
        return 0
    return math.ceil(math.log2(n))


@dataclass(frozen=True)
class MDLScore:
    n: int
    min_k: int
    max_k: int
    baseline_bits: int
    model_bits: Optional[int]
    residual_bits: int
    predicted_period: Optional[int]

    @property
    def total_description_bits(self) -> int:
        if self.model_bits is None:
            return self.baseline_bits
        return self.model_bits + self.residual_bits

    @property
    def gain_bits(self) -> int:
        return self.baseline_bits - self.total_description_bits


def mdl_score(
    stream: Stream,
    predicted_period: Optional[int],
    min_k: int,
    max_k: int,
    verified: bool,
) -> MDLScore:
    n = len(stream)
    if predicted_period is None or not verified:
        return MDLScore(n, min_k, max_k, n, None, n, predicted_period)
    model_bits = _ceil_log2(max_k - min_k + 1) + predicted_period
    return MDLScore(n, min_k, max_k, n, model_bits, 0, predicted_period)
