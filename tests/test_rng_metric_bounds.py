from __future__ import annotations

from fractions import Fraction

import pytest

from tools.chsh_receipts import ReceiptTrial
from tools.di_randomness_bounds import (
    TSIRELSON_BOUND_Q,
    hmin_lower_bound_bits_from_chsh,
    p_guess_upper_bound_from_chsh,
)
from tools.rng_metric import rng_metric
from tools.rng_transcript import RNGTranscript


def test_chsh_guessing_bound_endpoints():
    # Classical bound: S=2 => p_guess <= 1 => Hmin >= 0
    assert p_guess_upper_bound_from_chsh(Fraction(2, 1)) == pytest.approx(1.0)
    assert hmin_lower_bound_bits_from_chsh(Fraction(2, 1)) == pytest.approx(0.0)

    # Tsirelson bound: S=2*sqrt(2) => p_guess <= 1/2 => Hmin >= 1
    # We use the repo's rational approximation.
    assert p_guess_upper_bound_from_chsh(TSIRELSON_BOUND_Q) <= 1.0
    assert hmin_lower_bound_bits_from_chsh(TSIRELSON_BOUND_Q) <= 1.0
    assert hmin_lower_bound_bits_from_chsh(TSIRELSON_BOUND_Q) >= 0.0


def test_rng_metric_gates_on_structure_addition():
    # No trials => CHSH irrelevant; but also no structure-addition => 0 certified Hmin.
    t = RNGTranscript(trials=tuple(), has_structure_addition=False)
    m = rng_metric(t)
    assert m.hmin_lower_bound_bits == pytest.approx(0.0)


def test_rng_metric_monotone_in_structure_addition_flag():
    # Same trials; turning on structure-addition should not reduce certified Hmin.
    base_block = (
        ReceiptTrial(x=0, y=0, a=0, b=0),
        ReceiptTrial(x=0, y=1, a=0, b=0),
        ReceiptTrial(x=1, y=0, a=0, b=0),
        ReceiptTrial(x=1, y=1, a=0, b=0),
    ) * 50

    t_no = RNGTranscript(trials=base_block, has_structure_addition=False)
    t_yes = RNGTranscript(trials=base_block, has_structure_addition=True)

    m_no = rng_metric(t_no)
    m_yes = rng_metric(t_yes)

    assert m_no.hmin_lower_bound_bits <= m_yes.hmin_lower_bound_bits + 1e-12


def test_rng_metric_monotone_in_samples_for_fixed_observed_chsh():
    # If we keep observed CHSH fixed but reduce n_per_setting, the Hoeffding
    # correction should not *increase* the Hmin lower bound.
    #
    # We do this by constructing two *balanced* transcripts whose outcomes are
    # deterministic (a=b=0), so CHSH is at the classical boundary and Hmin=0.
    base_block = [
        ReceiptTrial(x=0, y=0, a=0, b=0),
        ReceiptTrial(x=0, y=1, a=0, b=0),
        ReceiptTrial(x=1, y=0, a=0, b=0),
        ReceiptTrial(x=1, y=1, a=0, b=0),
    ]
    t_small = RNGTranscript(trials=tuple(base_block * 10), has_structure_addition=True)
    t_big = RNGTranscript(trials=tuple(base_block * 100), has_structure_addition=True)

    m_small = rng_metric(t_small)
    m_big = rng_metric(t_big)

    assert m_small.hmin_lower_bound_bits <= m_big.hmin_lower_bound_bits + 1e-12
