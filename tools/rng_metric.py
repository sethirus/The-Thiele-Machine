from __future__ import annotations

"""Receipt-defined DI-randomness metric.

This is the D2 building block in MASTER_MILESTONES.

We compute:
- empirical CHSH (exact rational)
- a conservative CHSH→Hmin bound (bits) using a standard guessing-probability
    upper bound, optionally with a simple Hoeffding finite-statistics correction.

Important scope note:
This metric is a *receipts-only* computation. It does not assume stdout/logs,
and it can optionally gate “certified” randomness on structure-addition being
present in the transcript.
"""

from dataclasses import dataclass
from fractions import Fraction
from typing import Final

from tools.bell_operational import DatasetCounts, chsh_from_counts
from tools.chsh_receipts import counts_from_trials

from tools.di_randomness_bounds import (
    TSIRELSON_BOUND_Q,
    chsh_lower_confidence_bound_hoeffding,
    hmin_lower_bound_bits_from_chsh,
)

from tools.rng_transcript import RNGTranscript


@dataclass(frozen=True)
class RNGMetric:
    chsh: Fraction
    n_per_setting: int
    hmin_lower_bound_bits: float
    epsilon: float


DEFAULT_SOUNDNESS_DELTA: Final[float] = 1e-9


def rng_metric(transcript: RNGTranscript, *, soundness_delta: float = DEFAULT_SOUNDNESS_DELTA) -> RNGMetric:
    """Compute a conservative DI-randomness metric from a transcript.

        Returns:
            - empirical CHSH (exact rational)
            - trials per setting (balanced)
            - min-entropy lower bound (bits) derived from CHSH (conservative)
            - epsilon = soundness_delta used for the finite-statistics correction

        Operational convention:
        - If `transcript.has_structure_addition` is False, we return a certified
            min-entropy lower bound of 0.0 (even if CHSH is large). This makes the
            metric match the repo’s “no free insight” stance: randomness claims must
            be accompanied by an explicit structure-addition event.
    """

    if not transcript.trials:
        return RNGMetric(
            chsh=Fraction(0, 1),
            n_per_setting=0,
            hmin_lower_bound_bits=0.0,
            epsilon=float(soundness_delta),
        )

    dataset: DatasetCounts = counts_from_trials(transcript.trials)
    s = chsh_from_counts(dataset)

    # Conservative clipping: never allow CHSH>Tsirelson to *increase* Hmin.
    s_for_hmin = min(s, TSIRELSON_BOUND_Q)

    # Optional finite-statistics correction: derive a lower confidence bound
    # on expected CHSH, then translate to Hmin.
    # This is conservative and transcript-only.
    if dataset.n_per_setting > 0:
        s_lb = chsh_lower_confidence_bound_hoeffding(
            chsh_observed=s_for_hmin,
            n_per_setting=int(dataset.n_per_setting),
            soundness_delta=float(soundness_delta),
        )
    else:
        s_lb = Fraction(0, 1)

    hmin = hmin_lower_bound_bits_from_chsh(s_lb)
    if not transcript.has_structure_addition:
        hmin = 0.0

    return RNGMetric(
        chsh=s,
        n_per_setting=int(dataset.n_per_setting),
        hmin_lower_bound_bits=float(hmin),
        epsilon=float(soundness_delta),
    )


__all__ = [
    "RNGMetric",
    "rng_metric",
]
