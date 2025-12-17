from __future__ import annotations

"""Device-independent randomness bounds (CHSH-based).

This module is intentionally small/pure and is used by tools/rng_metric.py.

We use a standard CHSH→guessing-probability upper bound for quantum side
information:

  p_guess <= 1/2 + 1/2 * sqrt(2 - S^2/4)

for 2 <= S <= 2*sqrt(2).

Then H_min >= -log2(p_guess).

Notes:
- This bound is widely used in DI randomness expansion/amplification literature
  (e.g. Pironio et al., Nature 2010; follow-up work by Vazirani/Vidick et al.).
- We treat the transcript as an empirical CHSH value; for finite statistics,
  callers should apply a conservative lower confidence bound on S.
"""

import math
from fractions import Fraction
from typing import Final


TSIRELSON_BOUND_Q: Final[Fraction] = Fraction(5657, 2000)


def clamp(value: float, lo: float, hi: float) -> float:
    if value < lo:
        return lo
    if value > hi:
        return hi
    return value


def p_guess_upper_bound_from_chsh(chsh: Fraction) -> float:
    """Upper bound on guessing probability from CHSH value.

    Returns a float in [0.5, 1.0]. Values outside the physical range are
    clipped conservatively.
    """

    s = float(chsh)
    # The bound is meaningful for s in [2, 2*sqrt(2)].
    # If s <= 2, the best upper bound is 1 (no certified randomness).
    if s <= 2.0:
        return 1.0

    # If s exceeds Tsirelson due to finite-sample noise or adversarial traces,
    # we conservatively clip to Tsirelson to avoid over-claiming randomness.
    s_max = 2.0 * math.sqrt(2.0)
    s = min(s, s_max)

    inside = 2.0 - (s * s) / 4.0
    inside = max(0.0, inside)
    p_guess = 0.5 + 0.5 * math.sqrt(inside)
    return clamp(p_guess, 0.5, 1.0)


def hmin_lower_bound_bits_from_p_guess(p_guess_upper: float) -> float:
    """Lower bound on min-entropy in bits: H_min >= -log2(p_guess)."""

    p = clamp(float(p_guess_upper), 0.5, 1.0)
    return float(-math.log(p, 2))


def hmin_lower_bound_bits_from_chsh(chsh: Fraction) -> float:
    """Convenience: CHSH -> H_min lower bound (bits)."""

    return hmin_lower_bound_bits_from_p_guess(p_guess_upper_bound_from_chsh(chsh))


def chsh_lower_confidence_bound_hoeffding(
    *,
    chsh_observed: Fraction,
    n_per_setting: int,
    soundness_delta: float,
) -> Fraction:
    """Conservative lower confidence bound on the *expected* CHSH.

    Assumes balanced settings and bounded outcomes (standard CHSH estimator).

    We use a simple Hoeffding + union bound over the 4 correlation terms.
    This is conservative and avoids any distributional claims beyond boundedness.

    Returns a rational lower bound (may be below 2).
    """

    if n_per_setting <= 0:
        return Fraction(0, 1)

    delta = float(soundness_delta)
    if not (0.0 < delta < 1.0):
        raise ValueError("soundness_delta must be in (0,1)")

    # For each E_xy in [-1,1]: P(|Ehat - E| >= t) <= 2 exp(-2 N t^2)
    # Union bound over 4 settings gives <= 8 exp(-2 N t^2).
    # Set 8 exp(-2 N t^2) = delta => t = sqrt(log(8/delta)/(2N)).
    t = math.sqrt(math.log(8.0 / delta) / (2.0 * float(n_per_setting)))
    # CHSH is sum of 4 terms, so subtract 4t.
    s_lb = float(chsh_observed) - 4.0 * t
    return Fraction.from_float(s_lb).limit_denominator(10_000_000)


__all__ = [
    "TSIRELSON_BOUND_Q",
    "chsh_lower_confidence_bound_hoeffding",
    "hmin_lower_bound_bits_from_chsh",
    "hmin_lower_bound_bits_from_p_guess",
    "p_guess_upper_bound_from_chsh",
]
