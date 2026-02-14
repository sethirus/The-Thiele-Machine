#!/usr/bin/env python3
"""
QD3 vs Published CHSH Data — Literature Comparison
====================================================

Compares the Thiele QD3 prediction:

    S(T) = 2√2 · (1 − k_B T ln2 / E_sys)

against published experimental CHSH S-values from superconducting
qubit experiments.

Usage:
    python experiments/qd3_literature_comparison.py

Author: Devon Thiele
Date:   February 2026
"""
from __future__ import annotations

import math
import json
import sys
from dataclasses import dataclass, asdict
from typing import Optional

# ── Physical constants (2019 SI, exact) ──────────────────────
H_PLANCK  = 6.62607015e-34       # J·s
H_BAR     = H_PLANCK / (2 * math.pi)
K_B       = 1.380649e-23         # J/K
LN2       = math.log(2)
TSIRELSON = 2 * math.sqrt(2)     # ≈ 2.82843


# ── QD3 prediction ───────────────────────────────────────────
def s_qd3(T_kelvin: float, E_sys_joules: float) -> float:
    """S(T) predicted by QD3 for given temperature and system energy."""
    correction = K_B * T_kelvin * LN2 / E_sys_joules
    return TSIRELSON * max(0.0, 1.0 - correction)


def t_violation_lost(E_sys_joules: float) -> float:
    """Temperature at which QD3 predicts S < 2 (violation lost)."""
    # S < 2  ⟺  1 - kT ln2/E < 1/√2  ⟺  T > (1 - 1/√2)·E / (k ln2)
    return (1.0 - 1.0 / math.sqrt(2)) * E_sys_joules / (K_B * LN2)


def ds_dt(E_sys_joules: float) -> float:
    """Predicted slope dS/dT (per Kelvin). No free parameters."""
    return -TSIRELSON * K_B * LN2 / E_sys_joules


# ── Published data ───────────────────────────────────────────
@dataclass
class ExperimentalPoint:
    """A published CHSH S-value measurement."""
    label: str
    year: int
    S_measured: float
    S_uncertainty: float
    T_mK: float
    f_GHz: float               # qubit / cavity frequency
    readout_corrected: bool
    reference: str
    notes: str = ""

    @property
    def T_kelvin(self) -> float:
        return self.T_mK * 1e-3

    @property
    def E_sys(self) -> float:
        return H_PLANCK * self.f_GHz * 1e9


PUBLISHED_DATA = [
    ExperimentalPoint(
        label="Loophole-free cryolink",
        year=2023,
        S_measured=2.0747,
        S_uncertainty=0.0033,
        T_mK=15,
        f_GHz=5.0,
        readout_corrected=False,
        reference="Storz et al., Nature 2023",
        notes="30-meter cryogenic link; loss-dominated gap",
    ),
    ExperimentalPoint(
        label="Remote entanglement (raw)",
        year=2019,
        S_measured=2.237,
        S_uncertainty=0.036,
        T_mK=15,
        f_GHz=6.0,
        readout_corrected=False,
        reference="Zhong et al., 2019",
        notes="78 cm transmission line",
    ),
    ExperimentalPoint(
        label="Remote entanglement (corrected)",
        year=2019,
        S_measured=2.629,
        S_uncertainty=0.028,
        T_mK=15,
        f_GHz=6.0,
        readout_corrected=True,
        reference="Zhong et al., 2019",
        notes="Readout-error corrected; closest to ideal",
    ),
    ExperimentalPoint(
        label="Phase qubits",
        year=2009,
        S_measured=2.05,
        S_uncertainty=0.03,
        T_mK=25,
        f_GHz=8.0,
        readout_corrected=False,
        reference="Ansmann et al., Nature 2009",
        notes="Josephson phase qubits; early experiment",
    ),
]


# ── Analysis ─────────────────────────────────────────────────
@dataclass
class ComparisonRow:
    label: str
    year: int
    T_mK: float
    f_GHz: float
    S_measured: float
    S_uncertainty: float
    S_qd3: float
    qd3_correction_pct: float   # % below Tsirelson due to QD3
    expt_gap_pct: float         # % below Tsirelson observed
    qd3_within_gap: bool        # Is QD3 correction < experimental gap?
    readout_corrected: bool


def analyze() -> list[ComparisonRow]:
    rows = []
    for pt in PUBLISHED_DATA:
        s_pred = s_qd3(pt.T_kelvin, pt.E_sys)
        qd3_pct = (TSIRELSON - s_pred) / TSIRELSON * 100
        expt_pct = (TSIRELSON - pt.S_measured) / TSIRELSON * 100
        rows.append(ComparisonRow(
            label=pt.label,
            year=pt.year,
            T_mK=pt.T_mK,
            f_GHz=pt.f_GHz,
            S_measured=pt.S_measured,
            S_uncertainty=pt.S_uncertainty,
            S_qd3=s_pred,
            qd3_correction_pct=qd3_pct,
            expt_gap_pct=expt_pct,
            qd3_within_gap=qd3_pct < expt_pct,
            readout_corrected=pt.readout_corrected,
        ))
    return rows


def print_report() -> None:
    rows = analyze()

    print("=" * 90)
    print("QD3 PREDICTION vs PUBLISHED CHSH S-VALUES")
    print("=" * 90)
    print()
    print(f"Standard QM:  S = 2√2 = {TSIRELSON:.6f}  (temperature-independent)")
    print(f"Thiele QD3:   S(T) = 2√2 · (1 − k_B T ln2 / E_sys)")
    print(f"              No free parameters once T and E_sys = hf are specified.")
    print()

    # ── Table 1: Comparison ──
    hdr = f"{'Experiment':<32} {'Year':>4} {'T':>5} {'f':>5} {'S_meas':>8} {'S_QD3':>8} {'QD3%':>6} {'Gap%':>6} {'Corr':>4}"
    print(hdr)
    print("-" * len(hdr))
    for r in rows:
        corr_flag = "R" if r.readout_corrected else ""
        print(
            f"{r.label:<32} {r.year:>4} {r.T_mK:>4.0f} {r.f_GHz:>5.1f}"
            f" {r.S_measured:>8.4f} {r.S_qd3:>8.4f}"
            f" {r.qd3_correction_pct:>5.1f}% {r.expt_gap_pct:>5.1f}% {corr_flag:>4}"
        )
    print()

    # ── Table 2: Temperature scan predictions for common qubits ──
    print("=" * 90)
    print("PREDICTED S(T) FOR TEMPERATURE-SCAN EXPERIMENT")
    print("=" * 90)
    print()
    print("If a group measures CHSH on the SAME qubit at multiple temperatures,")
    print("QD3 predicts a specific linear decrease beyond standard decoherence.")
    print()

    for f_GHz in [5.0, 7.5, 10.0]:
        E = H_PLANCK * f_GHz * 1e9
        t_loss = t_violation_lost(E) * 1e3  # mK
        slope = ds_dt(E)
        print(f"  ── f = {f_GHz:.1f} GHz   (dS/dT = {slope:.4f} /K = {slope*1e-3:.2e} /mK,  S<2 at T>{t_loss:.0f} mK) ──")
        print(f"  {'T (mK)':>8}  {'S_QD3':>8}  {'Correction':>10}  {'Violates?':>9}")
        for T_mK in [10, 15, 20, 30, 42, 50, 75, 100, 150, 200, 250]:
            T = T_mK * 1e-3
            s = s_qd3(T, E)
            corr_pct = (TSIRELSON - s) / TSIRELSON * 100
            violates = "YES" if s > 2 else "NO"
            print(f"  {T_mK:>8}  {s:>8.4f}  {corr_pct:>9.2f}%  {violates:>9}")
        print()

    # ── 42 mK threshold analysis ──
    print("=" * 90)
    print("42 mK THRESHOLD (Dynamical Casimir Photons, 10 GHz)")
    print("=" * 90)
    print()
    E_10 = H_PLANCK * 10e9
    s_42 = s_qd3(0.042, E_10)
    t_qd3 = t_violation_lost(E_10) * 1e3
    print(f"  Observed:  violations lost entirely above ~42 mK")
    print(f"  QD3 at 42 mK:  S = {s_42:.4f}  (correction = {(TSIRELSON-s_42)/TSIRELSON*100:.2f}%)")
    print(f"  QD3 predicts S < 2 at:  T > {t_qd3:.0f} mK")
    print()
    print(f"  The 42 mK threshold is 5× LOWER than QD3's S<2 point ({t_qd3:.0f} mK).")
    print(f"  This means other decoherence mechanisms (thermal photons, quasiparticles)")
    print(f"  destroy violation BEFORE the QD3 correction alone would.")
    print(f"  QD3 is an ADDITIONAL suppression on top of standard decoherence.")
    print()

    # ── 250 mK niobium trilayer ──
    print("=" * 90)
    print("250 mK NIOBIUM TRILAYER QUBITS — STRONG-REGIME TEST")
    print("=" * 90)
    print()
    print("  Niobium-trilayer junctions can operate at 250 mK (Huang et al. 2025).")
    print("  QD3 makes a STRONG prediction at this temperature:")
    print()
    for f_GHz in [5.0, 7.5, 10.0, 12.5, 15.0]:
        E = H_PLANCK * f_GHz * 1e9
        s = s_qd3(0.250, E)
        corr = (TSIRELSON - s) / TSIRELSON * 100
        viol = "YES" if s > 2.0 else "NO"
        print(f"  f = {f_GHz:>5.1f} GHz:  S_QD3 = {s:.4f}  ({corr:.1f}% correction)  Violates? {viol}")
    print()
    print(f"  FALSIFICATION CONDITION:")
    f_critical = (1 - 1/math.sqrt(2))**(-1) * K_B * 0.250 * LN2 / H_PLANCK / 1e9
    print(f"  If CHSH violation is observed at 250 mK with f < {f_critical:.1f} GHz")
    print(f"  (after readout correction), QD3 is FALSIFIED.")
    print()

    # ── Key distinguishing test ──
    print("=" * 90)
    print("THE DISTINGUISHING EXPERIMENT")
    print("=" * 90)
    print("""
  Standard QM says: S degradation with temperature comes entirely from
  T1/T2 decoherence. After correcting for measured T1(T) and T2(T),
  the residual S should be independent of T.

  QD3 says: After correcting for decoherence, there is STILL a linear
  residual suppression:

      ΔS_residual(T) = −2√2 · k_B · ln2 / E_sys · T

  This slope has NO FREE PARAMETERS (only fundamental constants + qubit frequency).

  Protocol:
    1. Fix one transmon qubit (known f, known coupling)
    2. Measure CHSH S at T = 15, 30, 50, 100 mK
    3. At each T, independently measure T1(T) and T2(T)
    4. Model expected S_QM(T) from decoherence alone
    5. Plot residual: S_measured − S_QM(T)
    6. Fit line: slope should be −2√2·k_B·ln2/(hf)

  Required precision to distinguish QD3:
""")
    for f_GHz in [5.0, 7.5, 10.0]:
        E = H_PLANCK * f_GHz * 1e9
        # QD3 effect between 15 mK and 100 mK
        dT = 0.085  # 85 mK span
        dS = abs(ds_dt(E)) * dT
        print(f"  f = {f_GHz:.1f} GHz:  ΔS over 15→100 mK = {dS:.4f}  ({dS/TSIRELSON*100:.2f}%)")
        print(f"               Need S precision ≲ {dS/3:.4f} per point (3σ)")
    print()

    # ─── Save machine-readable results ───
    output = {
        "prediction": "S(T) = 2*sqrt(2) * (1 - k_B * T * ln2 / E_sys)",
        "constants": {
            "h": H_PLANCK, "hbar": H_BAR, "k_B": K_B,
            "ln2": LN2, "Tsirelson": TSIRELSON,
        },
        "literature_comparison": [asdict(r) for r in rows],
        "temperature_scan_5GHz": [
            {"T_mK": T, "S_qd3": s_qd3(T*1e-3, H_PLANCK*5e9)}
            for T in [10, 15, 20, 30, 42, 50, 75, 100, 150, 200, 250]
        ],
        "falsification_at_250mK": {
            "min_freq_GHz_for_violation": round(f_critical, 2),
            "condition": f"CHSH violation at 250 mK with f < {f_critical:.1f} GHz falsifies QD3",
        },
    }
    with open("artifacts/qd3_literature_comparison.json", "w") as fp:
        json.dump(output, fp, indent=2)
    print("  Results saved to artifacts/qd3_literature_comparison.json")
    print()


if __name__ == "__main__":
    print_report()
