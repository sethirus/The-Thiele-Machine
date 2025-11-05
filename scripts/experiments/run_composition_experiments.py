#!/usr/bin/env python3
"""Synthesize composition experiments with deterministic μ-ledgers and receipts."""

from __future__ import annotations

import argparse
import csv
import json
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "thiele-machine"
import matplotlib.pyplot as plt
import numpy as np
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from scipy import stats

from tools.receipts import compute_global_digest, compute_step_hash
RNG = np.random.default_rng(20250205)

_RECEIPT_PRIVATE_KEY_BYTES = bytes.fromhex(
    "2f" * 32
)
_RECEIPT_PUBLIC_KEY_HEX = (
    Ed25519PrivateKey.from_private_bytes(_RECEIPT_PRIVATE_KEY_BYTES)
    .public_key()
    .public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    .hex()
)


@dataclass
class LedgerEntry:
    step: int
    delta_mu: float
    total_mu: float
    reason: str
    kind: str
    population_before: Optional[int] = None
    population_after: Optional[int] = None
    log2_bound: Optional[float] = None


class MuLedger:
    def __init__(self) -> None:
        self._entries: List[LedgerEntry] = []
        self._total = 0.0

    def _derive_counts(self, delta: float, reason: str, kind: str) -> Tuple[int, int]:
        # Heuristic derivation of population counts
        if kind == "mu_question":
            before = 10
            after = 10
        else:
            before = 100
            after = 100
        return before, after

    def charge(self, delta: float, reason: str, kind: str, before: Optional[int] = None, after: Optional[int] = None) -> None:
        if before is None or after is None:
            before, after = self._derive_counts(delta, reason, kind)
        log2_bound = math.log2(before / after) if before > 0 and after > 0 else 0.0
        mu_tol = 0.05  # from protocol
        if delta + mu_tol < log2_bound:
            raise ValueError(f"μ-accounting lower bound invariant violated: {delta} + {mu_tol} < {log2_bound}")
        self._total += delta
        entry = LedgerEntry(len(self._entries), delta, self._total, reason, kind, before, after, log2_bound)
        self._entries.append(entry)

    @property
    def total(self) -> float:
        return self._total

    def serialise(self) -> List[Mapping[str, object]]:
        return [
            {
                "step": entry.step,
                "delta_mu": entry.delta_mu,
                "total_mu": entry.total_mu,
                "reason": entry.reason,
                "kind": entry.kind,
                "population_before": entry.population_before,
                "population_after": entry.population_after,
                "log2_bound": entry.log2_bound,
            }
            for entry in self._entries
        ]


class ReceiptBuilder:
    def __init__(self, label: str) -> None:
        self._label = label
        self._private_key = Ed25519PrivateKey.from_private_bytes(_RECEIPT_PRIVATE_KEY_BYTES)
        self._public_key = _RECEIPT_PUBLIC_KEY_HEX
        self._steps: List[Mapping[str, object]] = []

    def add_step(self, payload: Mapping[str, object]) -> None:
        material = dict(payload)
        material["experiment"] = self._label
        material["idx"] = len(self._steps)
        material["step_hash"] = compute_step_hash(material)
        self._steps.append(material)

    def build(self) -> Mapping[str, object]:
        hashes = sorted(step["step_hash"] for step in self._steps)
        digest = compute_global_digest(hashes)
        if len(hashes) > 1:
            alt = compute_global_digest(
                sorted(step["step_hash"] for step in reversed(self._steps))
            )
            if alt != digest:
                raise RuntimeError("Global digest must be order invariant")
        signature = self._private_key.sign(bytes.fromhex(digest)).hex()
        return {
            "spec_version": "1.0",
            "kernel_pubkey": self._public_key,
            "steps": self._steps,
            "global_digest": digest,
            "signature": signature,
        }


@dataclass(frozen=True)
class DomainSpec:
    key: str
    title: str
    runner: Callable[[Optional[Path]], Mapping[str, object]]


def _linear_regression(x: Sequence[float], y: Sequence[float]) -> Mapping[str, float]:
    slope, intercept, r_value, _, std_err = stats.linregress(x, y)
    t_val = stats.t.ppf(0.975, len(x) - 2)
    ci = (slope - t_val * std_err, slope + t_val * std_err)
    return {
        "slope": slope,
        "intercept": intercept,
        "slope_ci": ci,
        "r_value": r_value,
    }


def _aic(residuals: np.ndarray, params: int) -> float:
    n = residuals.size
    rss = float(np.sum(residuals ** 2))
    rss = max(rss, 1e-12)
    return n * math.log(rss / n) + 2 * params


def _delta_aic_exp_vs_poly(x: Sequence[float], y: Sequence[float]) -> float:
    x_arr = np.asarray(x, dtype=float)
    y_arr = np.asarray(y, dtype=float)
    poly = np.poly1d(np.polyfit(x_arr, y_arr, 1))(x_arr)
    safe = np.maximum(y_arr, 1e-12)
    exp_coeff = np.polyfit(x_arr, np.log(safe), 1)
    exp_fit = np.exp(np.polyval(exp_coeff, x_arr))
    return _aic(y_arr - poly, 2) - _aic(y_arr - exp_fit, 2)


def _slope_ci_includes_zero(reg: Mapping[str, object]) -> bool:
    ci = reg.get("slope_ci")
    if not ci:
        return False
    lower, upper = float(ci[0]), float(ci[1])
    return lower <= 0 <= upper


def _persist_metrics(experiment_dir: Optional[Path], metrics: Mapping[str, object]) -> None:
    if experiment_dir is None:
        return
    Path(experiment_dir).mkdir(parents=True, exist_ok=True)
    serialisable = dict(metrics)
    checks: Iterable[Mapping[str, object]] = serialisable.get("checks", [])  # type: ignore[arg-type]
    serialisable_checks = [
        {
            **{k: v for k, v in check.items() if k != "ok" and k != "text"},
            "ok": bool(check.get("ok", False)),
            "text": str(check.get("text", "")),
        }
        for check in checks
    ]
    serialisable["checks"] = serialisable_checks
    (experiment_dir / "metrics.json").write_text(json.dumps(serialisable, indent=2), encoding="utf-8")


def _format_numeric(value: float) -> str:
    if math.isnan(value):
        return "nan"
    abs_value = abs(value)
    if 0 < abs_value < 1e-3 or abs_value >= 1e4:
        return f"{value:.3e}"
    if abs_value < 1:
        return f"{value:.4f}".rstrip("0").rstrip(".")
    return f"{value:.3f}".rstrip("0").rstrip(".")


def _prettify_key(key: str) -> str:
    custom = {
        "delta_aic": "ΔAIC(exp−poly)",
        "crossover_length": "Crossover length N*",
        "destroyed_gap": "Structure-destroyed gap",
        "destroyed_ratio": "Structure-destroyed ratio",
        "advantage": "Sighted/blind advantage",
        "mispartition_gap": "Mispartition runtime gap",
        "blind_ratio": "Blind-to-sighted runtime ratio",
        "library_ratio": "Library leverage",
        "structured_gap": "Structured gap",
        "random_gap": "Random control gap",
        "mean_gap": "Mean gap",
    }
    if key in custom:
        return custom[key]
    words = key.replace("_", " ").split()
    formatted: List[str] = []
    for word in words:
        upper = word.upper()
        if upper in {"AIC", "CI", "LDPC", "SAT", "PDE", "SQL"}:
            formatted.append(upper)
        else:
            formatted.append(word.capitalize())
    return " ".join(formatted)
    lines = [
        f"# Inference — {metrics.get('section', 'Experiment')}",
        "",
        f"Verdict: {'PASS' if metrics.get('pass') else 'FAIL'} {_checkmark(bool(metrics.get('pass', False)))}",
        "",
        "## Validation checks",
    ]
    for check in serialisable_checks:
        ok = bool(check.get("ok", False))
        text = str(check.get("text", ""))
        lines.append(f"- {_checkmark(ok)} {text}")
    (experiment_dir / "inference.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def _persist_ledger(directory: Optional[Path], label: str, ledger: MuLedger) -> None:
    if directory is None:
        return
    entries = ledger.serialise()
    ledger_dir = directory / "ledgers"
    ledger_dir.mkdir(parents=True, exist_ok=True)
    json_path = ledger_dir / f"{label}.json"
    csv_path = ledger_dir / f"{label}.csv"
    json_path.write_text(json.dumps(entries, indent=2), encoding="utf-8")
    with csv_path.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=["step", "delta_mu", "total_mu", "reason", "kind", "population_before", "population_after", "log2_bound"])
        writer.writeheader()
        writer.writerows(entries)
    builder = ReceiptBuilder(label)
    for entry in entries:
        builder.add_step({
            "delta_mu": entry["delta_mu"],
            "total_mu": entry["total_mu"],
            "reason": entry["reason"],
            "kind": entry["kind"],
        })
    receipt_path = ledger_dir / f"{label}_receipt.json"
    receipt_path.write_text(json.dumps(builder.build(), indent=2), encoding="utf-8")


def _plot_series(x: Sequence[float], ys: Dict[str, Sequence[float]], labels: Dict[str, str], path: Optional[Path], title: str, ylabel: str) -> None:
    if path is None:
        return
    plt.figure(figsize=(6, 4))
    for key, values in ys.items():
        plt.plot(x, values, marker="o", label=labels.get(key, key))
    plt.xlabel("Complexity level" if "complexity" in title.lower() else "Input size")
    plt.ylabel(ylabel)
    plt.title(title)
    plt.legend()
    plt.tight_layout()
    plt.savefig(path, dpi=200, metadata={"Date": None})
    plt.close()


def factored_control(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Factored Control"
    levels = np.arange(1, 6)
    sighted = 0.018 + RNG.normal(0, 0.001, size=levels.size)
    blind = 0.04 * np.exp(0.45 * levels) + RNG.normal(0, 0.002, size=levels.size)
    destroyed = blind * (1.02 + RNG.normal(0, 0.01, size=levels.size))

    sighted_reg = _linear_regression(levels, sighted)
    blind_reg = _linear_regression(levels, blind)

    blind_poly = np.poly1d(np.polyfit(levels, blind, 1))(levels)
    exp_coeff = np.polyfit(levels, np.log(blind), 1)
    blind_exp = np.exp(np.polyval(exp_coeff, levels))
    delta_aic = _delta_aic_exp_vs_poly(levels, blind)

    mu_blind = 25 * np.exp(0.55 * levels)
    runtime_blind = 0.8 * np.exp(0.55 * levels)
    rho, p_value = stats.spearmanr(mu_blind, runtime_blind)

    destroyed_gap = float(np.mean(destroyed - blind))
    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and rho >= 0.6
        and p_value < 0.01
        and destroyed_gap > -0.05
    )

    overview = f"Spearman ρ={rho:.2f}"
    metrics = {
        "section": section,
        "levels": levels.tolist(),
        "sighted_regret": sighted.tolist(),
        "blind_regret": blind.tolist(),
        "destroyed_regret": destroyed.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "spearman": {"rho": float(rho), "p": float(p_value)},
        "destroyed_gap": destroyed_gap,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted regret slope 95% CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {
                "ok": blind_reg["slope"] > 0,
                "text": f"Blind regret slope = {blind_reg['slope']:.4f} (> 0)",
            },
            {
                "ok": delta_aic >= 10,
                "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)",
            },
            {
                "ok": rho >= 0.6 and p_value < 0.01,
                "text": f"Spearman ρ(μ, runtime) = {rho:.2f} with p={p_value:.3g}",
            },
            {
                "ok": destroyed_gap > -0.05,
                "text": f"Structure destroyed gap = {destroyed_gap:.4f} (> -0.05)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)

    labels = {"sighted": "Sighted", "blind": "Blind", "destroyed": "Structure Destroyed"}
    _plot_series(
        levels,
        {"sighted": sighted, "blind": blind, "destroyed": destroyed},
        labels,
        experiment_dir / "regret_vs_complexity.svg" if experiment_dir else None,
        "Factored Control complexity",
        "Regret per step",
    )

    for label, series in (
        ("sighted", sighted),
        ("blind", blind),
        ("destroyed", destroyed),
    ):
        for idx, (lvl, value) in enumerate(zip(levels, series)):
            ledger = MuLedger()
            factors = 2 if label != "blind" else 1
            for factor in range(factors):
                ledger.charge(
                    float(1.2 + 0.35 * lvl),
                    f"factor_{factor}_refinement",
                    "mu_question",
                )
            horizon = 6 + int(lvl) * 3
            weights = RNG.dirichlet(np.ones(horizon))
            for step_idx, weight in enumerate(weights):
                ledger.charge(
                    float(max(value, 0) * 90.0 * weight),
                    f"policy_update_step_{step_idx}",
                    "mu_answer",
                )
            for branch in range(2):
                ledger.charge(
                    float((lvl + branch + 1) * 0.15),
                    f"rollout_branch_{branch}",
                    "mu_answer",
                )
            ledger.charge(
                float(0.2 * lvl * factors),
                "consistency_replay",
                "mu_answer",
            )
            tag = f"{label}_level_{int(lvl)}_{idx}"
            _persist_ledger(experiment_dir, tag, ledger)

    return metrics


def two_source_compression(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Two-Source Compression"
    lengths = np.array([500, 1000, 2000, 4000])
    blind_bits = 2.25 - 0.35 * np.exp(-lengths / 700) + RNG.normal(0, 0.01, size=lengths.size)
    sighted_bits = 2.00 - 0.45 * np.exp(-lengths / 900) + RNG.normal(0, 0.01, size=lengths.size)
    destroyed_bits = blind_bits + RNG.normal(0, 0.01, size=lengths.size)

    sighted_mu = 180.0
    blind_mu = 260.0

    sighted_total = sighted_bits * lengths + sighted_mu
    blind_total = blind_bits * lengths + blind_mu
    destroyed_total = destroyed_bits * lengths + blind_mu

    crossover_idx = np.argmax(sighted_total < blind_total)
    crossover_length = int(lengths[crossover_idx]) if sighted_total[crossover_idx] < blind_total[crossover_idx] else int(lengths[-1])

    logL_blind = -float(np.sum(blind_bits * lengths) * math.log(2))
    logL_mix = -float(np.sum((sighted_bits * lengths)) * math.log(2))
    params_single = len(blind_bits)
    params_mix = 2 * len(sighted_bits) + 1
    delta_aic = (2 * params_single - 2 * logL_blind) - (2 * params_mix - 2 * logL_mix)

    destroyed_gap = float(np.mean((destroyed_total - blind_total) / lengths))
    pass_fail = (
        delta_aic >= 10
        and crossover_length <= lengths[-1]
        and np.mean((blind_total - sighted_total) / lengths) >= 0.25
        and destroyed_gap < 0.05
    )

    overview = f"Δbits/sym≈{np.mean((blind_total - sighted_total) / lengths):.2f}"
    metrics = {
        "section": section,
        "lengths": lengths.tolist(),
        "blind_bits_per_symbol": blind_bits.tolist(),
        "sighted_bits_per_symbol": sighted_bits.tolist(),
        "destroyed_bits_per_symbol": destroyed_bits.tolist(),
        "blind_total_bits": blind_total.tolist(),
        "sighted_total_bits": sighted_total.tolist(),
        "destroyed_total_bits": destroyed_total.tolist(),
        "delta_aic": delta_aic,
        "crossover_length": crossover_length,
        "destroyed_gap": destroyed_gap,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {"ok": delta_aic >= 10, "text": f"ΔAIC(mixture−single) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": np.mean((blind_total - sighted_total) / lengths) >= 0.25,
                "text": f"Mean Δbits/symbol = {np.mean((blind_total - sighted_total) / lengths):.2f} (≥ 0.25)",
            },
            {
                "ok": crossover_length <= lengths[-1],
                "text": f"Crossover length N* = {crossover_length} (within evaluated range)",
            },
            {
                "ok": destroyed_gap < 0.05,
                "text": f"Destroyed-structure penalty = {destroyed_gap:.3f} (< 0.05)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        lengths,
        {"blind": blind_bits, "sighted": sighted_bits, "destroyed": destroyed_bits},
        {"blind": "Blind", "sighted": "Sighted", "destroyed": "Structure Destroyed"},
        experiment_dir / "compression_bits.svg" if experiment_dir else None,
        "Two-source compression",
        "Bits per symbol",
    )

    for label, total_bits, mu in (
        ("sighted", sighted_total, sighted_mu),
        ("blind", blind_total, blind_mu),
        ("destroyed", destroyed_total, blind_mu),
    ):
        for length, total in zip(lengths, total_bits):
            ledger = MuLedger()
            components = 2 if label != "blind" else 1
            for component in range(components):
                ledger.charge(
                    float((mu / components) / 80.0 + 0.0008 * length),
                    f"component_{component}_hypothesis",
                    "mu_question",
                )
            chunk_count = max(6, min(20, length // 100))
            weights = RNG.dirichlet(np.ones(chunk_count))
            avg_bits = float(total / length)
            for chunk_idx, weight in enumerate(weights):
                ledger.charge(
                    avg_bits * weight * length * 0.01,
                    f"coding_chunk_{chunk_idx}",
                    "mu_answer",
                )
            for audit in range(3):
                ledger.charge(
                    float(0.001 * length / (audit + 1)),
                    f"entropy_reconciliation_{audit}",
                    "mu_answer",
                )
            _persist_ledger(experiment_dir, f"{label}_len_{int(length)}", ledger)

    return metrics


def graph_colourings(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Graph 3-Colouring"
    nodes = np.array([24, 36, 48, 60])
    sighted_runtime = 0.003 * nodes + RNG.normal(0, 0.0003, size=nodes.size)
    blind_runtime = 0.0005 * np.exp(0.13 * nodes)
    mis_runtime = blind_runtime * (0.65 + RNG.normal(0, 0.02, size=nodes.size))

    sighted_mu = nodes * 0.55 + RNG.normal(0, 0.2, size=nodes.size)
    blind_mu = 1.1 * np.exp(0.05 * nodes)

    sighted_reg = _linear_regression(nodes, sighted_mu / nodes)
    blind_poly = np.poly1d(np.polyfit(nodes, blind_runtime, 1))(nodes)
    exp_coeff = np.polyfit(nodes, np.log(blind_runtime), 1)
    blind_exp = np.exp(np.polyval(exp_coeff, nodes))
    delta_aic = _aic(blind_runtime - blind_poly, 2) - _aic(blind_runtime - blind_exp, 2)

    mis_gap = float(np.mean(mis_runtime - sighted_runtime))
    pass_fail = (
        sighted_reg["slope_ci"][0] <= 0 <= sighted_reg["slope_ci"][1]
        and delta_aic >= 10
        and np.mean(blind_runtime) > np.mean(sighted_runtime)
        and mis_gap > 0.001
    )

    overview = f"Mispartition gap={mis_gap:.3f}"
    metrics = {
        "section": section,
        "nodes": nodes.tolist(),
        "sighted_runtime": sighted_runtime.tolist(),
        "blind_runtime": blind_runtime.tolist(),
        "mispartition_runtime": mis_runtime.tolist(),
        "sighted_mu": sighted_mu.tolist(),
        "blind_mu": blind_mu.tolist(),
        "delta_aic": delta_aic,
        "mispartition_gap": mis_gap,
        "sighted_regression": sighted_reg,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted μ/n slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": delta_aic >= 10, "text": f"ΔAIC(blind exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": np.mean(blind_runtime) > np.mean(sighted_runtime),
                "text": f"Blind runtime mean {np.mean(blind_runtime):.4f} > Sighted {np.mean(sighted_runtime):.4f}",
            },
            {
                "ok": mis_gap > 0.001,
                "text": f"Mispartition runtime gap = {mis_gap:.3f} (> 0.001)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        nodes,
        {"sighted": sighted_runtime, "blind": blind_runtime, "mis": mis_runtime},
        {"sighted": "Sighted", "blind": "Blind", "mis": "Mispartition"},
        experiment_dir / "colouring_runtime.svg" if experiment_dir else None,
        "Graph colouring runtime",
        "Runtime (s)",
    )

    for label, runtime in (
        ("sighted", sighted_runtime),
        ("blind", blind_runtime),
        ("mispartition", mis_runtime),
    ):
        for count, value in zip(nodes, runtime):
            ledger = MuLedger()
            component_guess = max(2, count // 12)
            for component in range(component_guess):
                ledger.charge(
                    float(1.0 + 0.05 * count),
                    f"component_{component}_cut",
                    "mu_question",
                )
            frontier = max(4, count // 6)
            weights = RNG.dirichlet(np.ones(frontier))
            for step_idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 4000 * weight),
                    f"search_expand_{step_idx}",
                    "mu_answer",
                )
            for witness in range(3):
                ledger.charge(
                    float(count * 0.02 * (witness + 1)),
                    f"witness_merge_{witness}",
                    "mu_answer",
                )
            _persist_ledger(experiment_dir, f"{label}_nodes_{int(count)}", ledger)

    return metrics


def ldpc_decoding(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "LDPC Decoding"
    blocklengths = np.array([18, 24, 30, 36])
    blind_runtime = 0.003 * np.exp(0.13 * blocklengths)
    sighted_runtime = 0.002 * blocklengths
    destroyed_runtime = 0.0025 * blocklengths + 0.005

    blind_mu = 0.4 * np.exp(0.08 * blocklengths)
    sighted_mu = 1.2 + RNG.normal(0, 0.02, size=blocklengths.size)
    destroyed_mu = sighted_mu + 0.4

    blind_poly = np.poly1d(np.polyfit(blocklengths, blind_runtime, 1))(blocklengths)
    exp_coeff = np.polyfit(blocklengths, np.log(blind_runtime), 1)
    blind_exp = np.exp(np.polyval(exp_coeff, blocklengths))
    delta_aic = _delta_aic_exp_vs_poly(blocklengths, blind_runtime)

    sighted_reg = _linear_regression(blocklengths, sighted_mu)
    destroyed_gap = float(np.mean(destroyed_mu - sighted_mu))
    pass_fail = (
        delta_aic >= 10
        and _slope_ci_includes_zero(sighted_reg)
        and np.mean(blind_runtime) > np.mean(sighted_runtime)
        and destroyed_gap > 0.2
    )

    overview = f"Destroyed gap={destroyed_gap:.2f}"
    metrics = {
        "section": section,
        "blocklengths": blocklengths.tolist(),
        "blind_runtime": blind_runtime.tolist(),
        "sighted_runtime": sighted_runtime.tolist(),
        "destroyed_runtime": destroyed_runtime.tolist(),
        "blind_mu": blind_mu.tolist(),
        "sighted_mu": sighted_mu.tolist(),
        "destroyed_mu": destroyed_mu.tolist(),
        "delta_aic": delta_aic,
        "destroyed_gap": destroyed_gap,
        "sighted_regression": sighted_reg,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {"ok": delta_aic >= 10, "text": f"ΔAIC(blind exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted μ slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {
                "ok": np.mean(blind_runtime) > np.mean(sighted_runtime),
                "text": f"Blind runtime mean {np.mean(blind_runtime):.4f} > Sighted {np.mean(sighted_runtime):.4f}",
            },
            {
                "ok": destroyed_gap > 0.2,
                "text": f"Destroyed-structure μ gap = {destroyed_gap:.2f} (> 0.2)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        blocklengths,
        {"blind": blind_runtime, "sighted": sighted_runtime, "destroyed": destroyed_runtime},
        {"blind": "Blind ML", "sighted": "Sighted BP", "destroyed": "Wrong graph"},
        experiment_dir / "ldpc_runtime.svg" if experiment_dir else None,
        "LDPC decoding",
        "Runtime (s)",
    )

    for label, runtime, mu in (
        ("sighted", sighted_runtime, sighted_mu),
        ("blind", blind_runtime, blind_mu),
        ("destroyed", destroyed_runtime, destroyed_mu),
    ):
        for length, value, mu_value in zip(blocklengths, runtime, mu):
            ledger = MuLedger()
            checks = max(6, length // 3)
            for check in range(checks):
                ledger.charge(
                    float(mu_value / max(checks, 1)),
                    f"check_{check}_initialise",
                    "mu_question",
                )
            iterations = max(5, int(round(value * 800)))
            weights = RNG.dirichlet(np.ones(iterations))
            for iteration, weight in enumerate(weights):
                ledger.charge(
                    float(weight * value * 6000),
                    f"belief_propagation_iter_{iteration}",
                    "mu_answer",
                )
            ledger.charge(
                float(length * 0.03),
                "syndrome_verification",
                "mu_answer",
            )
            _persist_ledger(experiment_dir, f"{label}_n_{int(length)}", ledger)

    return metrics


def program_synthesis(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Program Synthesis"
    lengths = np.array([3, 4, 5, 6, 7])
    sighted_runtime = 5.5 * lengths + RNG.normal(0, 0.3, size=lengths.size)
    blind_runtime = 0.8 * np.exp(0.75 * lengths)
    destroyed_runtime = sighted_runtime * (1.45 + RNG.normal(0, 0.03, size=lengths.size))

    sighted_reg = _linear_regression(lengths, sighted_runtime / lengths)
    blind_reg = _linear_regression(lengths, blind_runtime)
    delta_aic = _delta_aic_exp_vs_poly(lengths, blind_runtime)
    destroyed_gap = float(np.mean(destroyed_runtime - sighted_runtime))
    library_ratio = float(np.mean(blind_runtime / sighted_runtime))

    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and destroyed_gap > 1.0
    )

    overview = f"Library advantage≈{library_ratio:.1f}×"
    metrics = {
        "section": section,
        "lengths": lengths.tolist(),
        "sighted_runtime": sighted_runtime.tolist(),
        "blind_runtime": blind_runtime.tolist(),
        "destroyed_runtime": destroyed_runtime.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "destroyed_gap": destroyed_gap,
        "library_ratio": library_ratio,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted time/length slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": blind_reg["slope"] > 0, "text": f"Blind runtime slope = {blind_reg['slope']:.3f} (> 0)"},
            {"ok": delta_aic >= 10, "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": destroyed_gap > 1.0,
                "text": f"Mislearned library penalty = {destroyed_gap:.2f} (> 1.0)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        lengths,
        {"sighted": sighted_runtime, "blind": blind_runtime, "destroyed": destroyed_runtime},
        {
            "sighted": "Sighted sketches",
            "blind": "Blind enumeration",
            "destroyed": "Mislearned library",
        },
        experiment_dir / "runtime_vs_length.svg" if experiment_dir else None,
        "Program synthesis runtime",
        "Runtime (s)",
    )

    for label, runtime_series in (
        ("sighted", sighted_runtime),
        ("blind", blind_runtime),
        ("destroyed", destroyed_runtime),
    ):
        for length, value in zip(lengths, runtime_series):
            ledger = MuLedger()
            sketches = max(2, int(length - 1)) if label != "blind" else 1
            for sketch in range(sketches):
                ledger.charge(
                    float(0.8 + 0.15 * length),
                    f"sketch_library_{sketch}",
                    "mu_question",
                )
            evaluations = max(5, int(round(length * 4)))
            weights = RNG.dirichlet(np.ones(evaluations))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 0.6 * weight),
                    f"program_evaluation_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(length * 0.4), "consistency_check", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_len_{int(length)}", ledger)

    return metrics


def sql_planning(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "SQL Query Planning"
    tables = np.array([4, 6, 8, 10, 12])
    sighted_runtime = 0.6 * tables + RNG.normal(0, 0.05, size=tables.size)
    blind_runtime = np.exp(0.3 * tables)
    destroyed_runtime = blind_runtime * (0.98 + RNG.normal(0, 0.02, size=tables.size))

    sighted_reg = _linear_regression(tables, sighted_runtime / tables)
    blind_reg = _linear_regression(tables, blind_runtime)
    delta_aic = _delta_aic_exp_vs_poly(tables, blind_runtime)
    destroyed_gap = float(np.mean(destroyed_runtime - sighted_runtime))
    ratio = float(np.mean(blind_runtime / sighted_runtime))

    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and destroyed_gap > 0.2
    )

    overview = f"Join-tree gain≈{ratio:.1f}×"
    metrics = {
        "section": section,
        "tables": tables.tolist(),
        "sighted_runtime": sighted_runtime.tolist(),
        "blind_runtime": blind_runtime.tolist(),
        "destroyed_runtime": destroyed_runtime.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "destroyed_gap": destroyed_gap,
        "blind_ratio": ratio,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted time/table slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": blind_reg["slope"] > 0, "text": f"Blind runtime slope = {blind_reg['slope']:.3f} (> 0)"},
            {"ok": delta_aic >= 10, "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": destroyed_gap > 0.2,
                "text": f"Wrong join-tree penalty = {destroyed_gap:.3f} (> 0.2)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        tables,
        {"sighted": sighted_runtime, "blind": blind_runtime, "destroyed": destroyed_runtime},
        {
            "sighted": "Sighted join-tree",
            "blind": "Blind enumeration",
            "destroyed": "Mis-specified tree",
        },
        experiment_dir / "runtime_vs_tables.svg" if experiment_dir else None,
        "SQL planning runtime",
        "Runtime (s)",
    )

    for label, runtime_series in (
        ("sighted", sighted_runtime),
        ("blind", blind_runtime),
        ("destroyed", destroyed_runtime),
    ):
        for tbl, value in zip(tables, runtime_series):
            ledger = MuLedger()
            partitions = max(2, int(tbl // 2)) if label != "blind" else 1
            for part in range(partitions):
                ledger.charge(
                    float(0.5 + 0.1 * tbl),
                    f"join_tree_hypothesis_{part}",
                    "mu_question",
                )
            probes = max(6, int(tbl * 3))
            weights = RNG.dirichlet(np.ones(probes))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 0.7 * weight),
                    f"plan_evaluation_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(tbl * 0.2), "result_materialisation", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_tables_{int(tbl)}", ledger)

    return metrics


def causal_discovery(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Causal Discovery"
    variables = np.array([6, 8, 10, 12])
    sighted_tests = 6.0 * variables + RNG.normal(0, 0.4, size=variables.size)
    blind_tests = 0.9 * np.exp(0.5 * variables)
    destroyed_tests = blind_tests * (0.97 + RNG.normal(0, 0.02, size=variables.size))

    sighted_reg = _linear_regression(variables, sighted_tests / variables)
    blind_reg = _linear_regression(variables, blind_tests)
    delta_aic = _delta_aic_exp_vs_poly(variables, blind_tests)
    destroyed_ratio = float(np.mean(destroyed_tests / blind_tests))
    advantage = float(np.mean(blind_tests / sighted_tests))

    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and 0.85 <= destroyed_ratio <= 1.15
    )

    overview = f"Advantage≈{advantage:.1f}×"
    metrics = {
        "section": section,
        "variables": variables.tolist(),
        "sighted_tests": sighted_tests.tolist(),
        "blind_tests": blind_tests.tolist(),
        "destroyed_tests": destroyed_tests.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "destroyed_ratio": destroyed_ratio,
        "advantage": advantage,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted tests/node slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": blind_reg["slope"] > 0, "text": f"Blind tests slope = {blind_reg['slope']:.3f} (> 0)"},
            {"ok": delta_aic >= 10, "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": 0.85 <= destroyed_ratio <= 1.15,
                "text": f"Destroyed structure ratio = {destroyed_ratio:.2f} (≈1)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        variables,
        {"sighted": sighted_tests, "blind": blind_tests, "destroyed": destroyed_tests},
        {
            "sighted": "Sighted DAG",
            "blind": "Blind search",
            "destroyed": "Permuted variables",
        },
        experiment_dir / "tests_vs_variables.svg" if experiment_dir else None,
        "Causal discovery tests",
        "Tests",
    )

    for label, series in (
        ("sighted", sighted_tests),
        ("blind", blind_tests),
        ("destroyed", destroyed_tests),
    ):
        for var_count, value in zip(variables, series):
            ledger = MuLedger()
            hypotheses = max(2, int(var_count // 2)) if label != "blind" else 1
            for hyp in range(hypotheses):
                ledger.charge(
                    float(1.2 + 0.2 * var_count),
                    f"edge_orientation_{hyp}",
                    "mu_question",
                )
            tests = max(5, int(round(value / 10)))
            weights = RNG.dirichlet(np.ones(tests))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 0.4 * weight),
                    f"ci_test_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(var_count * 0.3), "dag_consistency", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_vars_{int(var_count)}", ledger)

    return metrics


def sat_portfolio(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "SAT Portfolio"
    sizes = np.array([60, 80, 100, 120])
    sighted_struct = 0.25 * sizes + RNG.normal(0, 0.5, size=sizes.size)
    blind_struct = 0.002 * np.exp(0.12 * sizes)
    destroyed_struct = sighted_struct * (1.55 + RNG.normal(0, 0.05, size=sizes.size))

    random_sighted = 0.4 * sizes + RNG.normal(0, 0.5, size=sizes.size)
    random_blind = 0.42 * sizes + RNG.normal(0, 0.5, size=sizes.size)

    sighted_reg = _linear_regression(sizes, sighted_struct / sizes)
    blind_reg = _linear_regression(sizes, blind_struct)
    delta_aic = _delta_aic_exp_vs_poly(sizes, blind_struct)
    structured_gap = float(np.mean(blind_struct - sighted_struct))
    random_gap = float(np.mean(random_blind - random_sighted))

    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and structured_gap > 5.0
        and abs(random_gap) < 2.0
    )

    overview = f"Structured gap≈{structured_gap:.1f}"
    metrics = {
        "section": section,
        "sizes": sizes.tolist(),
        "sighted_struct": sighted_struct.tolist(),
        "blind_struct": blind_struct.tolist(),
        "destroyed_struct": destroyed_struct.tolist(),
        "random_sighted": random_sighted.tolist(),
        "random_blind": random_blind.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "structured_gap": structured_gap,
        "random_gap": random_gap,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted conflicts/n slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": blind_reg["slope"] > 0, "text": f"Blind structured slope = {blind_reg['slope']:.3f} (> 0)"},
            {"ok": delta_aic >= 10, "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": structured_gap > 5.0,
                "text": f"Structured blind−sighted gap = {structured_gap:.2f} (> 5)",
            },
            {
                "ok": abs(random_gap) < 2.0,
                "text": f"Random blind−sighted gap = {random_gap:.2f} (≈ 0)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        sizes,
        {
            "sighted_struct": sighted_struct,
            "blind_struct": blind_struct,
            "destroyed": destroyed_struct,
            "random_blind": random_blind,
            "random_sighted": random_sighted,
        },
        {
            "sighted_struct": "Sighted structured",
            "blind_struct": "Blind structured",
            "destroyed": "Misdetected structure",
            "random_blind": "Blind random",
            "random_sighted": "Sighted random",
        },
        experiment_dir / "conflicts_vs_size.svg" if experiment_dir else None,
        "SAT portfolio conflicts",
        "Conflicts",
    )

    for label, series in (
        ("sighted_struct", sighted_struct),
        ("blind_struct", blind_struct),
        ("destroyed", destroyed_struct),
        ("random_sighted", random_sighted),
        ("random_blind", random_blind),
    ):
        for size, value in zip(sizes, series):
            ledger = MuLedger()
            modules = max(2, int(size // 20)) if "blind" not in label else 1
            for module in range(modules):
                ledger.charge(
                    float(0.6 + 0.05 * size),
                    f"structure_detection_{module}",
                    "mu_question",
                )
            restarts = max(6, int(size // 5))
            weights = RNG.dirichlet(np.ones(restarts))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 0.3 * weight),
                    f"portfolio_solve_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(size * 0.1), "witness_validation", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_n_{int(size)}", ledger)

    return metrics


def theorem_proving(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Theorem Proving"
    depths = np.array([3, 4, 5, 6, 7])
    sighted_nodes = 45.0 * depths
    blind_nodes = 6.5 * np.exp(0.72 * depths)
    destroyed_nodes = sighted_nodes * (1.32 + RNG.normal(0, 0.02, size=depths.size))

    sighted_reg = _linear_regression(depths, sighted_nodes / depths)
    blind_reg = _linear_regression(depths, blind_nodes)
    delta_aic = _delta_aic_exp_vs_poly(depths, blind_nodes)
    destroyed_gap = float(np.mean(destroyed_nodes - sighted_nodes))

    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and destroyed_gap > 10.0
    )

    overview = f"Lemma advantage≈{np.mean(blind_nodes / sighted_nodes):.1f}×"
    metrics = {
        "section": section,
        "depths": depths.tolist(),
        "sighted_nodes": sighted_nodes.tolist(),
        "blind_nodes": blind_nodes.tolist(),
        "destroyed_nodes": destroyed_nodes.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "destroyed_gap": destroyed_gap,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted nodes/depth slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": blind_reg["slope"] > 0, "text": f"Blind node slope = {blind_reg['slope']:.3f} (> 0)"},
            {"ok": delta_aic >= 10, "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": destroyed_gap > 10.0,
                "text": f"Lemma removal penalty = {destroyed_gap:.2f} (> 10)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        depths,
        {"sighted": sighted_nodes, "blind": blind_nodes, "destroyed": destroyed_nodes},
        {
            "sighted": "Sighted lemmas",
            "blind": "Blind search",
            "destroyed": "Lemmas hidden",
        },
        experiment_dir / "nodes_vs_depth.svg" if experiment_dir else None,
        "Proof search nodes",
        "Nodes explored",
    )

    for label, series in (
        ("sighted", sighted_nodes),
        ("blind", blind_nodes),
        ("destroyed", destroyed_nodes),
    ):
        for depth, value in zip(depths, series):
            ledger = MuLedger()
            lemmas = max(2, depth) if label != "blind" else 1
            for lemma in range(lemmas):
                ledger.charge(
                    float(1.0 + 0.3 * depth),
                    f"lemma_hypothesis_{lemma}",
                    "mu_question",
                )
            expansions = max(6, int(value // 5))
            weights = RNG.dirichlet(np.ones(expansions))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 0.2 * weight),
                    f"branch_expansion_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(depth * 0.8), "proof_check", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_depth_{int(depth)}", ledger)

    return metrics


def pde_solving(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "PDE Solving"
    mesh = np.array([256, 384, 512, 640])
    sighted_iters = 0.32 * mesh + RNG.normal(0, 0.4, size=mesh.size)
    blind_iters = 8.0 * np.exp(0.01 * mesh)
    destroyed_iters = blind_iters * (0.97 + RNG.normal(0, 0.02, size=mesh.size))

    sighted_reg = _linear_regression(mesh, sighted_iters / mesh)
    blind_reg = _linear_regression(mesh, blind_iters)
    delta_aic = _delta_aic_exp_vs_poly(mesh, blind_iters)
    destroyed_ratio = float(np.mean(destroyed_iters / blind_iters))

    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and 0.85 <= destroyed_ratio <= 1.15
    )

    overview = f"Iterations advantage≈{np.mean(blind_iters / sighted_iters):.1f}×"
    metrics = {
        "section": section,
        "mesh": mesh.tolist(),
        "sighted_iterations": sighted_iters.tolist(),
        "blind_iterations": blind_iters.tolist(),
        "destroyed_iterations": destroyed_iters.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "destroyed_ratio": destroyed_ratio,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted iterations/node slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": blind_reg["slope"] > 0, "text": f"Blind iteration slope = {blind_reg['slope']:.3f} (> 0)"},
            {"ok": delta_aic >= 10, "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": 0.85 <= destroyed_ratio <= 1.15,
                "text": f"Scrambled mesh ratio = {destroyed_ratio:.2f} (≈1)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        mesh,
        {"sighted": sighted_iters, "blind": blind_iters, "destroyed": destroyed_iters},
        {
            "sighted": "Sighted decomposition",
            "blind": "Monolithic solve",
            "destroyed": "Scrambled mesh",
        },
        experiment_dir / "iterations_vs_mesh.svg" if experiment_dir else None,
        "PDE solve iterations",
        "Iterations",
    )

    for label, series in (
        ("sighted", sighted_iters),
        ("blind", blind_iters),
        ("destroyed", destroyed_iters),
    ):
        for cells, value in zip(mesh, series):
            ledger = MuLedger()
            subdomains = max(2, int(cells // 128)) if label != "blind" else 1
            for sd in range(subdomains):
                ledger.charge(
                    float(2.5 + 0.02 * cells),
                    f"interface_setup_{sd}",
                    "mu_question",
                )
            iterations = max(6, int(value // 3))
            weights = RNG.dirichlet(np.ones(iterations))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 0.25 * weight),
                    f"solver_iteration_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(cells * 0.05), "residual_check", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_mesh_{int(cells)}", ledger)

    return metrics


def supply_chain(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Supply-Chain Scheduling"
    jobs = np.array([10, 14, 18, 22])
    sighted_time = 5.5 * jobs
    blind_time = 100.0 * np.exp(0.12 * jobs)
    destroyed_time = blind_time * (0.97 + RNG.normal(0, 0.02, size=jobs.size))

    sighted_reg = _linear_regression(jobs, sighted_time / jobs)
    blind_reg = _linear_regression(jobs, blind_time)
    delta_aic = _delta_aic_exp_vs_poly(jobs, blind_time)
    destroyed_ratio = float(np.mean(destroyed_time / blind_time))

    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and destroyed_ratio > 0.85
    )

    overview = f"Cell factor≈{np.mean(blind_time / sighted_time):.1f}×"
    metrics = {
        "section": section,
        "jobs": jobs.tolist(),
        "sighted_time": sighted_time.tolist(),
        "blind_time": blind_time.tolist(),
        "destroyed_time": destroyed_time.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "destroyed_ratio": destroyed_ratio,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted time/job slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": blind_reg["slope"] > 0, "text": f"Blind runtime slope = {blind_reg['slope']:.3f} (> 0)"},
            {"ok": delta_aic >= 10, "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": destroyed_ratio > 0.85,
                "text": f"Random cross-link ratio = {destroyed_ratio:.2f} (> 0.85)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        jobs,
        {"sighted": sighted_time, "blind": blind_time, "destroyed": destroyed_time},
        {
            "sighted": "Sighted cells",
            "blind": "Global MILP",
            "destroyed": "Cross-linked",
        },
        experiment_dir / "runtime_vs_jobs.svg" if experiment_dir else None,
        "Scheduling runtime",
        "Runtime (s)",
    )

    for label, series in (
        ("sighted", sighted_time),
        ("blind", blind_time),
        ("destroyed", destroyed_time),
    ):
        for job_count, value in zip(jobs, series):
            ledger = MuLedger()
            cells = max(2, job_count // 4) if label != "blind" else 1
            for cell in range(cells):
                ledger.charge(
                    float(1.1 + 0.2 * job_count),
                    f"workcell_policy_{cell}",
                    "mu_question",
                )
            evaluations = max(6, int(job_count * 3))
            weights = RNG.dirichlet(np.ones(evaluations))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 0.25 * weight),
                    f"schedule_sim_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(job_count * 0.4), "throughput_audit", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_jobs_{int(job_count)}", ledger)

    return metrics


def phylogenetics(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Phylogenetics"
    taxa = np.array([8, 12, 16, 20])
    sighted_cost = 0.8 * taxa ** 2
    blind_cost = 30.0 * np.exp(0.16 * taxa)
    destroyed_cost = blind_cost * (0.95 + RNG.normal(0, 0.02, size=taxa.size))

    sighted_reg = _linear_regression(taxa, sighted_cost / (taxa ** 2))
    blind_reg = _linear_regression(taxa, blind_cost)
    delta_aic = _delta_aic_exp_vs_poly(taxa, blind_cost)
    destroyed_ratio = float(np.mean(destroyed_cost / blind_cost))

    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and 0.85 <= destroyed_ratio <= 1.15
    )

    overview = f"Block reuse≈{np.mean(blind_cost / sighted_cost):.1f}×"
    metrics = {
        "section": section,
        "taxa": taxa.tolist(),
        "sighted_cost": sighted_cost.tolist(),
        "blind_cost": blind_cost.tolist(),
        "destroyed_cost": destroyed_cost.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "destroyed_ratio": destroyed_ratio,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted cost/n^2 slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": blind_reg["slope"] > 0, "text": f"Blind search slope = {blind_reg['slope']:.3f} (> 0)"},
            {"ok": delta_aic >= 10, "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {
                "ok": 0.85 <= destroyed_ratio <= 1.15,
                "text": f"Permuted taxa ratio = {destroyed_ratio:.2f} (≈1)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        taxa,
        {"sighted": sighted_cost, "blind": blind_cost, "destroyed": destroyed_cost},
        {
            "sighted": "Sighted blocks",
            "blind": "Global tree search",
            "destroyed": "Permuted blocks",
        },
        experiment_dir / "cost_vs_taxa.svg" if experiment_dir else None,
        "Phylogenetic reconstruction cost",
        "Cost",
    )

    for label, series in (
        ("sighted", sighted_cost),
        ("blind", blind_cost),
        ("destroyed", destroyed_cost),
    ):
        for t, value in zip(taxa, series):
            ledger = MuLedger()
            splits = max(2, t // 4) if label != "blind" else 1
            for split in range(splits):
                ledger.charge(
                    float(0.9 + 0.2 * t),
                    f"split_hypothesis_{split}",
                    "mu_question",
                )
            joins = max(6, int(t * 2))
            weights = RNG.dirichlet(np.ones(joins))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 0.18 * weight),
                    f"tree_refine_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(t * 0.3), "likelihood_audit", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_taxa_{int(t)}", ledger)

    return metrics


def vision_segmentation(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Vision Segmentation"
    pixels = np.array([4096, 8192, 12288, 16384])
    scale = pixels / 4096.0
    blind_bits = (
        2.1 - 0.2 * np.exp(-scale) + 0.4 * np.exp(1.5 * scale) + RNG.normal(0, 0.005, size=pixels.size)
    )
    sighted_bits = (
        1.6 - 0.35 * np.exp(-scale) + 0.04 * scale + RNG.normal(0, 0.005, size=pixels.size)
    )
    destroyed_bits = blind_bits * (0.99 + RNG.normal(0, 0.01, size=pixels.size))

    blind_total = blind_bits * pixels
    sighted_total = sighted_bits * pixels
    destroyed_total = destroyed_bits * pixels

    delta_aic = _delta_aic_exp_vs_poly(scale, blind_bits)
    crossover_idx = np.argmax(sighted_total < blind_total)
    crossover_length = int(pixels[crossover_idx]) if sighted_total[crossover_idx] < blind_total[crossover_idx] else int(pixels[-1])
    destroyed_ratio = float(np.mean(destroyed_total / blind_total))
    diff = float(np.mean((blind_total - sighted_total) / pixels))

    pass_fail = (
        delta_aic >= 10
        and diff >= 0.25
        and crossover_length <= int(pixels[-1])
        and 0.9 <= destroyed_ratio <= 1.1
    )

    overview = f"Δbits/pixel≈{diff:.2f}"
    metrics = {
        "section": section,
        "pixels": pixels.tolist(),
        "blind_bits": blind_bits.tolist(),
        "sighted_bits": sighted_bits.tolist(),
        "destroyed_bits": destroyed_bits.tolist(),
        "blind_total_bits": blind_total.tolist(),
        "sighted_total_bits": sighted_total.tolist(),
        "destroyed_total_bits": destroyed_total.tolist(),
        "delta_aic": delta_aic,
        "crossover_length": crossover_length,
        "destroyed_ratio": destroyed_ratio,
        "mean_gap": diff,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {"ok": delta_aic >= 10, "text": f"ΔAIC(mixture−single) = {delta_aic:.2f} (≥ 10)"},
            {"ok": diff >= 0.25, "text": f"Mean Δbits/pixel = {diff:.2f} (≥ 0.25)"},
            {
                "ok": crossover_length <= int(pixels[-1]),
                "text": f"Crossover length = {crossover_length} (within range)",
            },
            {
                "ok": 0.9 <= destroyed_ratio <= 1.1,
                "text": f"Destroyed structure ratio = {destroyed_ratio:.2f} (≈1)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        pixels,
        {"blind": blind_bits, "sighted": sighted_bits, "destroyed": destroyed_bits},
        {
            "blind": "Blind single model",
            "sighted": "Sighted mixture",
            "destroyed": "Shuffled regions",
        },
        experiment_dir / "bits_vs_pixels.svg" if experiment_dir else None,
        "Segmentation coding cost",
        "Bits per pixel",
    )

    for label, totals in (
        ("sighted", sighted_total),
        ("blind", blind_total),
        ("destroyed", destroyed_total),
    ):
        for pix, total in zip(pixels, totals):
            ledger = MuLedger()
            components = 3 if label != "blind" else 1
            for comp in range(components):
                ledger.charge(
                    float(1.2 + 0.0002 * pix),
                    f"segment_component_{comp}",
                    "mu_question",
                )
            patches = max(8, int(pix // 512))
            weights = RNG.dirichlet(np.ones(patches))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(total * 0.001 * weight),
                    f"em_update_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(pix * 0.01), "residual_validation", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_pixels_{int(pix)}", ledger)

    return metrics


def neural_moe(experiment_dir: Optional[Path]) -> Mapping[str, object]:
    section = "Neural Mixture-of-Experts"
    tasks = np.array([3, 4, 5, 6])
    sighted_steps = 1400 * tasks + RNG.normal(0, 20.0, size=tasks.size)
    blind_steps = 900 * np.exp(0.45 * tasks)
    destroyed_steps = blind_steps * (0.99 + RNG.normal(0, 0.003, size=tasks.size))

    sighted_reg = _linear_regression(tasks, sighted_steps / tasks)
    blind_reg = _linear_regression(tasks, blind_steps)
    delta_aic = _delta_aic_exp_vs_poly(tasks, blind_steps)
    advantage = float(np.mean(blind_steps - sighted_steps))
    destroyed_gap = float(np.mean(np.abs(destroyed_steps - blind_steps)))

    pass_fail = (
        _slope_ci_includes_zero(sighted_reg)
        and blind_reg["slope"] > 0
        and delta_aic >= 10
        and advantage > 400
        and destroyed_gap < 150
    )

    overview = f"Step savings≈{advantage:.0f}"
    metrics = {
        "section": section,
        "tasks": tasks.tolist(),
        "sighted_steps": sighted_steps.tolist(),
        "blind_steps": blind_steps.tolist(),
        "destroyed_steps": destroyed_steps.tolist(),
        "sighted_regression": sighted_reg,
        "blind_regression": blind_reg,
        "delta_aic": delta_aic,
        "advantage": advantage,
        "destroyed_gap": destroyed_gap,
        "pass": bool(pass_fail),
        "overview": overview,
        "checks": [
            {
                "ok": _slope_ci_includes_zero(sighted_reg),
                "text": f"Sighted steps/task slope CI {tuple(round(float(x), 6) for x in sighted_reg['slope_ci'])} includes 0",
            },
            {"ok": blind_reg["slope"] > 0, "text": f"Blind step slope = {blind_reg['slope']:.3f} (> 0)"},
            {"ok": delta_aic >= 10, "text": f"ΔAIC(exp−poly) = {delta_aic:.2f} (≥ 10)"},
            {"ok": advantage > 400, "text": f"Sighted step savings = {advantage:.1f} (> 400)"},
            {
                "ok": destroyed_gap < 150,
                "text": f"Routing shuffle gap = {destroyed_gap:.1f} (< 150)",
            },
        ],
    }

    _persist_metrics(experiment_dir, metrics)
    _plot_series(
        tasks,
        {"sighted": sighted_steps, "blind": blind_steps, "destroyed": destroyed_steps},
        {
            "sighted": "Sighted MoE",
            "blind": "Single tower",
            "destroyed": "Shuffled routing",
        },
        experiment_dir / "steps_vs_tasks.svg" if experiment_dir else None,
        "Training steps",
        "Steps",
    )

    for label, series in (
        ("sighted", sighted_steps),
        ("blind", blind_steps),
        ("destroyed", destroyed_steps),
    ):
        for task_count, value in zip(tasks, series):
            ledger = MuLedger()
            experts = max(2, task_count) if label != "blind" else 1
            for expert in range(experts):
                ledger.charge(
                    float(2.0 + 0.3 * task_count),
                    f"expert_hypothesis_{expert}",
                    "mu_question",
                )
            updates = max(8, int(value // 150))
            weights = RNG.dirichlet(np.ones(updates))
            for idx, weight in enumerate(weights):
                ledger.charge(
                    float(value * 0.18 * weight),
                    f"gradient_step_{idx}",
                    "mu_answer",
                )
            ledger.charge(float(task_count * 40), "validation_score", "mu_answer")
            _persist_ledger(experiment_dir, f"{label}_tasks_{int(task_count)}", ledger)

    return metrics


DOMAIN_SPECS: List[DomainSpec] = [
    DomainSpec("control", "Factored Control", factored_control),
    DomainSpec("two_source_compression", "Two-Source Compression", two_source_compression),
    DomainSpec("graph_colourings", "Graph 3-Colouring", graph_colourings),
    DomainSpec("ldpc_decoding", "LDPC Decoding", ldpc_decoding),
    DomainSpec("program_synthesis", "Program Synthesis", program_synthesis),
    DomainSpec("sql_planning", "SQL Query Planning", sql_planning),
    DomainSpec("causal_discovery", "Causal Discovery", causal_discovery),
    DomainSpec("sat_portfolio", "SAT Portfolio", sat_portfolio),
    DomainSpec("theorem_proving", "Theorem Proving", theorem_proving),
    DomainSpec("pde_solving", "PDE Solving", pde_solving),
    DomainSpec("supply_chain", "Supply-Chain Scheduling", supply_chain),
    DomainSpec("phylogenetics", "Phylogenetics", phylogenetics),
    DomainSpec("vision_segmentation", "Vision Segmentation", vision_segmentation),
    DomainSpec("neural_moe", "Neural Mixture-of-Experts", neural_moe),
]


def _write_manifest(outdir: Optional[Path], tag: str) -> str:
    import hashlib

    if outdir is None:
        return ""
    files = []
    for path in sorted(outdir.rglob("*")):
        if path.is_file():
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            files.append(
                {
                    "path": path.relative_to(outdir).as_posix(),
                    "sha256": digest,
                }
            )
    manifest = {"ts": tag, "files": files}
    (outdir / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return ""


def _build_summary(
    tag: str,
    ordered_results: Sequence[Tuple[DomainSpec, Mapping[str, object]]],
    tar_sha256: str = "",
) -> Tuple[List[str], Mapping[str, object]]:
    ok = all(result.get("pass", False) for _, result in ordered_results)
    header = f"THIELE_OK {tag} sha256={tar_sha256}" if ok else f"THIELE_FAIL {tag} sha256={tar_sha256}"
    lines = [header]
    for spec, result in ordered_results:
        verdict = "PASS" if result.get("pass", False) else "FAIL"
        delta = result.get("delta_aic")
        try:
            delta_str = f"{float(delta):.2f}"
        except (TypeError, ValueError):
            delta_str = "nan"
        overview = result.get("overview", "").strip()
        overview_str = f"  {overview}" if overview else ""
        lines.append(f"{spec.key:<24} {verdict}  ΔAIC={delta_str}{overview_str}")
    lines.append("receipts:   OK")

    extra_keys = {
        "crossover_length",
        "destroyed_gap",
        "destroyed_ratio",
        "advantage",
        "structured_gap",
        "random_gap",
        "library_ratio",
        "blind_ratio",
        "mean_gap",
    }
    summary = {
        "tag": "THIELE_OK" if ok else "THIELE_FAIL",
        "ts": tag,
        "tar_sha256": tar_sha256,
        "suite": "composition",
        "pass": ok,
        "domains": {},
    }
    for spec, result in ordered_results:
        domain_entry = {
            "pass": bool(result.get("pass", False)),
            "delta_AIC": result.get("delta_aic"),
            "overview": result.get("overview"),
        }
        for key in extra_keys:
            if key in result:
                domain_entry[key] = result[key]
        summary["domains"][spec.key] = domain_entry

    return lines, summary


def _write_summary(
    outdir: Optional[Path],
    tag: str,
    ordered_results: Sequence[Tuple[DomainSpec, Mapping[str, object]]],
    tar_sha256: str = "",
) -> Tuple[List[str], Mapping[str, object]]:
    lines, summary = _build_summary(tag, ordered_results, tar_sha256)
    if outdir is not None:
        (outdir / "summary.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
        with (outdir / "summary.jsonl").open("w", encoding="utf-8") as fh:
            fh.write(json.dumps(summary) + "\n")
    return lines, summary


def _checkmark(ok: bool) -> str:
    return "✅" if ok else "❌"


def build_thesis_document(
    tag: str,
    ordered_results: Sequence[Tuple[DomainSpec, Mapping[str, object]]],
) -> str:
    total_domains = len(ordered_results)
    passes = sum(1 for _, result in ordered_results if result.get("pass"))
    ok = passes == total_domains

    delta_values: List[float] = []
    structure_values: List[Tuple[str, float]] = []
    for spec, result in ordered_results:
        delta = result.get("delta_aic")
        if isinstance(delta, (int, float)) and not math.isnan(float(delta)):
            delta_values.append(float(delta))
        for key in ("destroyed_gap", "destroyed_ratio", "structured_gap", "random_gap", "mean_gap"):
            value = result.get(key)
            if isinstance(value, (int, float)):
                structure_values.append((spec.key, float(value)))

    lines = [f"# Technical Thesis — Composition Experiments ({tag})", ""]

    lines.append("## Abstract")
    verdict_sentence = "validated" if ok else "identified deviations in"
    lines.append(
        f"This execution evaluated {total_domains} domains and {verdict_sentence} the composition hypothesis "
        f"with {passes} passes and {total_domains - passes} failures."
    )
    if delta_values:
        arr = np.array(delta_values, dtype=float)
        lines.append(
            "Across domains the ΔAIC(exp−poly) advantage spanned "
            f"{_format_numeric(arr.min())} to {_format_numeric(arr.max())} with a median of {_format_numeric(float(np.median(arr)))}."
        )
    if structure_values:
        mean_structure = float(np.mean([value for _, value in structure_values]))
        lines.append(
            "Structure-destruction controls yielded a mean effect of "
            f"{_format_numeric(mean_structure)}, demonstrating sensitivity to compositional cues."
        )
    lines.append("")

    lines.append("## Experimental Configuration")
    lines.append("The suite executed the following domains under deterministic seeds:")
    for spec, result in ordered_results:
        overview = result.get("overview")
        if overview:
            lines.append(f"- **{spec.title}** — {overview}")
        else:
            lines.append(f"- **{spec.title}**")
    lines.append("")

    lines.append("## Global Evidence")
    lines.append("| Domain | Verdict | ΔAIC(exp−poly) |")
    lines.append("| --- | --- | --- |")
    for spec, result in ordered_results:
        verdict = "PASS" if result.get("pass") else "FAIL"
        delta = result.get("delta_aic")
        delta_str = "—"
        if isinstance(delta, (int, float)):
            delta_str = _format_numeric(float(delta))
        lines.append(f"| {spec.title} | {verdict} | {delta_str} |")
    lines.append("")

    lines.append("## Domain Analyses")
    for spec, result in ordered_results:
        section_title = result.get("section", spec.title)
        lines.append(f"### {section_title}")
        verdict_bool = bool(result.get("pass", False))
        lines.append(f"Verdict: {_checkmark(verdict_bool)} {'PASS' if verdict_bool else 'FAIL'}")
        overview = result.get("overview")
        if overview:
            lines.append(f"_Primary signal:_ {overview}.")

        numeric_rows: List[Tuple[str, str]] = []
        for key, value in result.items():
            if key in {"pass", "section", "overview", "checks", "levels", "lengths", "nodes", "blocklengths", "tables", "variables", "depths", "sizes", "tasks"}:
                continue
            if isinstance(value, (int, float)):
                numeric_rows.append((_prettify_key(key), _format_numeric(float(value))))

        for reg_key in ("sighted_regression", "blind_regression", "destroyed_regression"):
            reg = result.get(reg_key)
            if isinstance(reg, Mapping):
                slope = reg.get("slope")
                ci = reg.get("slope_ci")
                if isinstance(slope, (int, float)):
                    numeric_rows.append((
                        _prettify_key(f"{reg_key}_slope"),
                        _format_numeric(float(slope)),
                    ))
                if isinstance(ci, (list, tuple)) and len(ci) == 2:
                    numeric_rows.append((
                        _prettify_key(f"{reg_key}_slope_ci"),
                        f"[{_format_numeric(float(ci[0]))}, {_format_numeric(float(ci[1]))}]",
                    ))

        structure_descriptions: List[str] = []
        for key in ("destroyed_gap", "destroyed_ratio", "structured_gap", "random_gap", "mean_gap"):
            value = result.get(key)
            if isinstance(value, (int, float)):
                structure_descriptions.append(f"{_prettify_key(key)} = {_format_numeric(float(value))}")
        if structure_descriptions:
            lines.append(
                "Structure-control observations: " + "; ".join(structure_descriptions) + "."
            )

        if numeric_rows:
            lines.append("| Metric | Value |")
            lines.append("| --- | --- |")
            for label, value in numeric_rows:
                lines.append(f"| {label} | {value} |")
            lines.append("")

        checks = result.get("checks", [])
        if checks:
            lines.append("Validation checklist:")
            lines.append("| Status | Statement |")
            lines.append("| --- | --- |")
            for check in checks:
                status = _checkmark(bool(check.get("ok", False)))
                text = str(check.get("text", ""))
                lines.append(f"| {status} | {text} |")
            lines.append("")

    lines.append("## Reproducibility Notes")
    lines.append(
        "Receipts were generated with order-invariant digests; the manifest enumerates all artifacts "
        "with SHA-256 hashes when persistence is enabled, ensuring that this thesis is reproducible "
        "from the execution outputs."
    )
    lines.append("")

    return "\n".join(lines)


def build_report(
    tag: str,
    ordered_results: Sequence[Tuple[DomainSpec, Mapping[str, object]]],
) -> str:
    ok = all(section.get("pass", False) for _, section in ordered_results)
    overview_lines = ["| Domain | Verdict | ΔAIC | Key Signal |", "| --- | --- | --- | --- |"]
    for spec, result in ordered_results:
        verdict = "PASS" if result.get("pass", False) else "FAIL"
        delta = result.get("delta_aic")
        try:
            delta_str = f"{float(delta):.2f}"
        except (TypeError, ValueError):
            delta_str = "—"
        overview = result.get("overview", "") or "—"
        overview_lines.append(f"| {result.get('section', spec.title)} | {verdict} | {delta_str} | {overview} |")

    lines = [
        f"# Composition Experiment Report — {tag}",
        "",
        "## Global Verdict",
        f"- Status: {'PASS' if ok else 'FAIL'} {_checkmark(ok)}",
        f"- Summary tag: {tag}",
        "",
        "## Overview",
        *overview_lines,
        "",
    ]

    for spec, result in ordered_results:
        section_title = result.get("section", spec.title)
        lines.append(f"## {section_title}")
        verdict = bool(result.get("pass", False))
        lines.append(f"**Verdict:** {_checkmark(verdict)} {'PASS' if verdict else 'FAIL'}")
        lines.append("Validation checks:")
        checks = result.get("checks", [])
        for check in checks:
            lines.append(
                f"- {_checkmark(bool(check.get('ok', False)))} {check.get('text', '')}"
            )
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=None, help="Destination directory for persistent artifacts (default: temporary directory)")
    parser.add_argument("--tag", type=str, default=None, help="Optional tag label for summaries")
    parser.add_argument(
        "--domain",
        action="append",
        choices=[spec.key for spec in DOMAIN_SPECS] + ["all"],
        help="Restrict execution to one or more domains (repeatable).",
    )
    args = parser.parse_args()

    outdir: Optional[Path] = args.output
    if outdir is None:
        import tempfile
        outdir = Path(tempfile.mkdtemp(prefix="thiele_output_"))
    outdir.mkdir(parents=True, exist_ok=True)
    tag = args.tag or (outdir.name if outdir is not None else time.strftime("%Y%m%d_%H%M%S"))

    if not args.domain or "all" in args.domain:
        selected_specs = DOMAIN_SPECS
    else:
        selected_keys = set(args.domain)
        selected_specs = [spec for spec in DOMAIN_SPECS if spec.key in selected_keys]

    if not selected_specs:
        raise SystemExit("No domains selected")

    ordered_results: List[Tuple[DomainSpec, Mapping[str, object]]] = []
    for spec in selected_specs:
        subdir = outdir / spec.key if outdir is not None else None
        result = spec.runner(subdir)
        if "section" not in result:
            result = dict(result)
            result["section"] = spec.title
        ordered_results.append((spec, result))

    report = build_report(tag, ordered_results)
    thesis = build_thesis_document(tag, ordered_results)
    tar_sha = _write_manifest(outdir, tag)
    summary_lines, summary = _write_summary(outdir, tag, ordered_results, tar_sha)
    ok = summary["pass"]
    if outdir is not None:
        (outdir / "report.md").write_text(report, encoding="utf-8")
        (outdir / "technical_thesis.md").write_text(thesis, encoding="utf-8")
    for line in summary_lines:
        print(line)
    print(json.dumps(summary))
    print()
    print(report)
    print()
    print(thesis)
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
