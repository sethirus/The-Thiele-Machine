#!/usr/bin/env python3
"""
Tests for QM-divergent falsifiable predictions (QD1–QD6).

Each test verifies:
  1. Internal consistency of the μ-framework predictions
  2. Numerical precision of derived constants
  3. Correct sign / magnitude of QM–Thiele deltas
  4. Monotonicity and limiting behaviour
"""
from __future__ import annotations

import math
import pytest

from experiments.qm_divergent_predictions import (
    H_PLANCK, H_BAR, K_B, LN2, T_PLANCK, C_LIGHT, MU_0,
    tau_mu, d_mu,
    s_max_thiele,
    s_temperature_corrected,
    bell_correlator_qm, bell_correlator_thiele,
    gamma_mu,
    entropy_correction,
    QD1_PlanckTimeRatio,
    QD2_ModifiedTsirelson,
    QD3_TemperatureSuppression,
    QD4_CorrectedCorrelator,
    QD5_DecoherenceRate,
    QD6_EntropyCorrection,
)

SQRT2 = math.sqrt(2)
TSIRELSON = 2 * SQRT2


# ═══════════════════════════════════════════════════════════════
# QD1: Planck-time ratio
# ═══════════════════════════════════════════════════════════════
class TestQD1PlanckTimeRatio:

    def test_ratio_matches_analytical(self):
        """τ_μ(T_Planck) / t_Planck = π / (2·ln2)."""
        qd1 = QD1_PlanckTimeRatio.compute()
        expected = math.pi / (2 * LN2)
        assert abs(qd1.thiele_value - expected) / expected < 1e-3

    def test_tau_mu_room_temperature(self):
        """τ_μ(300K) ≈ 58 fs."""
        tau = tau_mu(300.0)
        assert 50e-15 < tau < 70e-15, f"Expected ~58 fs, got {tau:.2e}"

    def test_d_mu_room_temperature(self):
        """d_μ(300K) ≈ 17 μm."""
        d = d_mu(300.0)
        assert 15e-6 < d < 20e-6, f"Expected ~17 μm, got {d:.2e}"

    def test_tau_mu_inversely_proportional_to_T(self):
        """τ_μ ∝ 1/T."""
        ratio = tau_mu(100.0) / tau_mu(300.0)
        assert abs(ratio - 3.0) < 0.01

    def test_tau_mu_positive(self):
        """τ_μ > 0 for all T > 0."""
        for T in [0.001, 1.0, 300.0, 1e6, T_PLANCK]:
            assert tau_mu(T) > 0

    def test_d_mu_equals_c_times_tau(self):
        """d_μ = c · τ_μ exactly."""
        for T in [4.2, 77.0, 300.0]:
            assert abs(d_mu(T) - C_LIGHT * tau_mu(T)) < 1e-30


# ═══════════════════════════════════════════════════════════════
# QD2: Modified Tsirelson bound
# ═══════════════════════════════════════════════════════════════
class TestQD2ModifiedTsirelson:

    def test_zero_budget_gives_zero(self):
        """With μ=0, no Bell violation is possible: S_max = 0."""
        assert s_max_thiele(0.0) == 0.0

    def test_infinite_budget_recovers_tsirelson(self):
        """μ→∞ recovers S = 2√2."""
        assert abs(s_max_thiele(1e6) - TSIRELSON) < 1e-10

    def test_monotonically_increasing(self):
        """S_max increases with μ-budget."""
        prev = 0.0
        for mu in [0.01, 0.1, 0.5, 1.0, 5.0, 100.0]:
            s = s_max_thiele(mu)
            assert s > prev, f"S_max({mu}) = {s} should exceed {prev}"
            prev = s

    def test_always_at_most_tsirelson(self):
        """S_max(μ) ≤ 2√2 for all finite μ (< at low μ)."""
        for mu in [0.001, 0.1, 1.0, 10.0]:
            assert s_max_thiele(mu) < TSIRELSON
        # At extreme μ, float precision saturates
        assert s_max_thiele(1000.0) <= TSIRELSON

    def test_one_bit_budget(self):
        """At μ = ln(2) (one Landauer bit), S ≈ 2√2·(1−1/e) ≈ 1.789."""
        s = s_max_thiele(LN2)
        expected = TSIRELSON * (1 - 1 / math.e)
        assert abs(s - expected) < 1e-10

    def test_deficit_nonnegative(self):
        """QM − Thiele deficit is non-negative for finite μ."""
        table = QD2_ModifiedTsirelson.compute_table()
        for row in table:
            assert row.deficit >= 0
        # Strictly positive for small budgets
        assert table[0].deficit > 0

    def test_deficit_decreases_with_budget(self):
        """Deficit shrinks as μ increases."""
        table = QD2_ModifiedTsirelson.compute_table()
        for i in range(1, len(table)):
            assert table[i].deficit < table[i - 1].deficit


# ═══════════════════════════════════════════════════════════════
# QD3: Temperature-dependent CHSH suppression
# ═══════════════════════════════════════════════════════════════
class TestQD3TemperatureSuppression:

    def test_zero_temperature_gives_tsirelson(self):
        """At T→0, no suppression: S = 2√2."""
        s = s_temperature_corrected(0.0, 1e-19)
        assert abs(s - TSIRELSON) < 1e-15

    def test_suppression_increases_with_T(self):
        """Larger T → larger suppression."""
        prev = 0.0
        for T in [1.0, 10.0, 100.0, 300.0]:
            s = s_temperature_corrected(T, 1e-19)
            suppression = TSIRELSON - s
            assert suppression > prev
            prev = suppression

    def test_suppression_ppm_at_room_temp(self):
        """At 300K with E_sys=1eV (0.16 aJ), suppression is measurable."""
        table = QD3_TemperatureSuppression.compute_table()
        room = [r for r in table if r.temperature == 300.0][0]
        assert room.suppression_ppm > 0
        # ~3% suppression (28700 ppm) — large enough to be falsifiable
        assert room.suppression_ppm < 1e6  # Not > 100%

    def test_high_energy_suppresses_less(self):
        """Higher E_system → smaller correction."""
        s_low_E = s_temperature_corrected(300.0, 1e-19)
        s_high_E = s_temperature_corrected(300.0, 1e-15)
        assert (TSIRELSON - s_low_E) > (TSIRELSON - s_high_E)

    def test_saturates_at_zero(self):
        """S can't go below zero."""
        s = s_temperature_corrected(1e30, 1e-30)  # extreme T, tiny E
        assert s >= 0.0


# ═══════════════════════════════════════════════════════════════
# QD4: μ-corrected Bell correlator
# ═══════════════════════════════════════════════════════════════
class TestQD4CorrectedCorrelator:

    def test_qm_at_zero(self):
        """E_QM(0) = −1."""
        assert bell_correlator_qm(0.0) == -1.0

    def test_qm_at_pi_over_2(self):
        """E_QM(π/2) = 0."""
        assert abs(bell_correlator_qm(math.pi / 2)) < 1e-15

    def test_correction_zero_at_theta_zero(self):
        """At θ=0, sin²(0)=0 so no μ-correction."""
        e_qm = bell_correlator_qm(0.0)
        e_th = bell_correlator_thiele(0.0, 300.0, 3e15)
        assert abs(e_th - e_qm) < 1e-15

    def test_correction_maximal_at_pi_over_2(self):
        """At θ=π/2, sin²(θ)=1 so μ-correction is maximal."""
        T, omega = 300.0, 3e15
        delta_mu = 2 * K_B * T * LN2 / (H_BAR * omega)
        e_th = bell_correlator_thiele(math.pi / 2, T, omega)
        e_qm = bell_correlator_qm(math.pi / 2)
        assert abs((e_th - e_qm) - delta_mu) < 1e-15

    def test_correction_positive(self):
        """δ_μ > 0 so E_thiele > E_qm at θ ∈ (0, π)."""
        for theta in [0.1, 0.5, 1.0, 1.5]:
            e_qm = bell_correlator_qm(theta)
            e_th = bell_correlator_thiele(theta, 300.0, 3e15)
            assert e_th >= e_qm

    def test_delta_mu_magnitude(self):
        """δ_μ at T=300K, ω=3×10¹⁵ is small but measurable (~10⁻²)."""
        delta_mu = 2 * K_B * 300 * LN2 / (H_BAR * 3e15)
        assert 1e-4 < delta_mu < 1.0  # O(10⁻²)

    def test_table_has_entries(self):
        table = QD4_CorrectedCorrelator.compute_table()
        assert len(table) == 5


# ═══════════════════════════════════════════════════════════════
# QD5: Decoherence rate
# ═══════════════════════════════════════════════════════════════
class TestQD5DecoherenceRate:

    def test_gamma_proportional_to_T(self):
        """γ_μ ∝ T."""
        ratio = gamma_mu(600.0) / gamma_mu(300.0)
        assert abs(ratio - 2.0) < 1e-10

    def test_gamma_at_room_temp(self):
        """γ_μ(300K) ~ 10¹³ Hz (THz regime)."""
        g = gamma_mu(300.0)
        assert 1e12 < g < 1e14

    def test_gamma_positive(self):
        for T in [0.001, 4.2, 300.0]:
            assert gamma_mu(T) > 0

    def test_decoherence_time_order(self):
        """Higher T → shorter decoherence time."""
        table = QD5_DecoherenceRate.compute_table()
        for i in range(1, len(table)):
            assert table[i].tau_decoherence_s < table[i - 1].tau_decoherence_s

    def test_formula_consistency(self):
        """γ_μ = 1/τ_decoherence."""
        table = QD5_DecoherenceRate.compute_table()
        for row in table:
            assert abs(row.gamma_mu_hz * row.tau_decoherence_s - 1.0) < 1e-10

    def test_gamma_matches_landauer_formula(self):
        """γ_μ = k_B T ln2 / ℏ exactly."""
        T = 42.0
        expected = K_B * T * LN2 / H_BAR
        assert abs(gamma_mu(T) - expected) < 1e-10


# ═══════════════════════════════════════════════════════════════
# QD6: Entanglement entropy correction
# ═══════════════════════════════════════════════════════════════
class TestQD6EntropyCorrection:

    def test_correction_linear_in_N(self):
        """μ-correction scales linearly with N_qubits."""
        c1 = entropy_correction(1, 0.015, 1e-23)
        c4 = entropy_correction(4, 0.015, 1e-23)
        assert abs(c4 - 4 * c1) < 1e-30

    def test_correction_linear_in_T(self):
        """μ-correction scales linearly with temperature."""
        c_low = entropy_correction(1, 0.010, 1e-23)
        c_high = entropy_correction(1, 0.020, 1e-23)
        assert abs(c_high - 2 * c_low) < 1e-30

    def test_correction_positive(self):
        """μ always adds entropy."""
        for N in [1, 5, 20]:
            assert entropy_correction(N, 0.015, 1e-23) > 0

    def test_thiele_exceeds_qm(self):
        """S_thiele > S_qm always."""
        table = QD6_EntropyCorrection.compute_table()
        for row in table:
            assert row.S_thiele > row.S_qm

    def test_correction_small_at_low_T(self):
        """At mK temperatures, correction should be << 1."""
        table = QD6_EntropyCorrection.compute_table(T=0.015, E_gap=1e-23)
        for row in table:
            assert row.correction < 1.0

    def test_table_has_expected_sizes(self):
        table = QD6_EntropyCorrection.compute_table()
        assert len(table) == 6
        assert table[0].N_qubits == 1
        assert table[-1].N_qubits == 50


# ═══════════════════════════════════════════════════════════════
# Cross-cutting consistency
# ═══════════════════════════════════════════════════════════════
class TestCrossCuttingConsistency:

    def test_mu_0_is_ln2(self):
        """Natural μ unit is ln(2)."""
        assert MU_0 == LN2

    def test_planck_constant_emerges_from_tau_mu(self):
        """h = 4 · E_landauer · τ_μ at any temperature."""
        for T in [4.2, 77.0, 300.0, 1000.0]:
            E_landauer = K_B * T * LN2
            h_derived = 4 * E_landauer * tau_mu(T)
            assert abs(h_derived - H_PLANCK) / H_PLANCK < 1e-12

    def test_tau_and_gamma_reciprocal(self):
        """τ_μ(T) and γ_μ(T) are NOT exact reciprocals.
        τ_μ = h/(4 k T ln2), γ_μ = k T ln2/ℏ
        γ_μ · τ_μ = π/2 ≈ 1.5708."""
        for T in [4.2, 300.0]:
            product = gamma_mu(T) * tau_mu(T)
            assert abs(product - math.pi / 2) < 1e-10

    def test_all_predictions_have_sign_convention(self):
        """Thiele always predicts MORE dissipation / cost than QM."""
        # QD2: S_thiele < S_qm (less violation)
        assert s_max_thiele(1.0) < TSIRELSON
        # QD3: suppression is positive
        assert TSIRELSON - s_temperature_corrected(300.0, 1e-19) > 0
        # QD4: E_thiele >= E_qm
        assert bell_correlator_thiele(1.0, 300.0, 3e15) >= bell_correlator_qm(1.0)
        # QD6: entropy correction positive
        assert entropy_correction(1, 0.015, 1e-23) > 0

    def test_script_runs(self):
        """The main summary prints without error."""
        from experiments.qm_divergent_predictions import print_summary
        import io, contextlib
        f = io.StringIO()
        with contextlib.redirect_stdout(f):
            print_summary()
        output = f.getvalue()
        assert "QD1" in output
        assert "QD6" in output
        assert "FALSIFICATION" in output
