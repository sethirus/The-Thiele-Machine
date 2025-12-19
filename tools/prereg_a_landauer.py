"""PREREG A: µ predicts finite-time Landauer/erasure work (bound form).

This is an *auditable*, manifest-bound pipeline:
  init -> ingest -> analyze

It does not download copyrighted paper PDFs.
Instead it consumes digitized numeric points (facts) with provenance fields.

Default model is conservative (no tightening): it will usually FAIL the
"tighter-than-Landauer" prereg criteria until a valid µ term is provided.
"""

from __future__ import annotations

import sys
import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

# Ensure repository root is importable when running as a file path.
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.prereg_common import (
    ManifestSpec,
    init_manifest,
    read_json,
    require_artifact_hashes,
    require_manifest,
    safe_relpath,
    update_manifest_artifacts,
    verify_params_exact,
    verify_tool_hashes,
    write_json,
)


DEFAULT_ROOT = REPO_ROOT / "benchmarks" / "mu_landauer_a"
MANIFEST_NAME = "MANIFEST_A.json"

TOOL_FILES = [
    REPO_ROOT / "tools" / "prereg_common.py",
    REPO_ROOT / "tools" / "prereg_a_landauer.py",
    REPO_ROOT / "physics" / "landauer" / "mu_models.py",
]


@dataclass(frozen=True)
class DataPoint:
    paper_id: str
    figure_id: str
    dataset_id: str
    curve_id: str
    value_kind: str
    tau_unit: str
    tau_s: float
    work_over_kT: float
    work_err_over_kT: Optional[float]
    digitize_sigma_work: Optional[float]
    digitize_sigma_logtau: Optional[float]
    info_bits_removed: float


def _iter_csv_rows(path: Path) -> Iterable[Dict[str, str]]:
    with path.open("r", newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            yield row


def _parse_optional_float(v: str) -> Optional[float]:
    v = (v or "").strip()
    if not v:
        return None
    return float(v)


REQUIRED_COLUMNS = {
    "paper_id",
    "figure_id",
    "dataset_id",
    "value_kind",
    "tau_unit",
    # Legacy name; load_datapoints also accepts tau_value.
    "tau_s",
    "work_over_kT",
    "work_err_over_kT",
    "info_bits_removed",
}


ALLOWED_VALUE_KINDS = {
    # Direct work measurement at a given protocol duration.
    "work_over_kT",
    # Dimensionless coefficient a in (W-ln2)/kT = a * Var/(D*tau).
    # In this mode, work_over_kT stores the coefficient a (not W/kT).
    "a_coeff",
}


ALLOWED_TAU_UNITS = {
    # Seconds.
    "s",
    # Dimensionless reduced time τ/τ0 (paper-defined). This is evaluable for the
    # baseline Landauer inequality but does NOT trigger the finite-time tightening
    # term (which is gated to D_tau_over_Var).
    "tau_over_tau0",
    # Dimensionless: D·tau / Var(x), as used in some Landauer literature.
    "D_tau_over_Var",
    # Not applicable (used for coefficient-only rows).
    "none",
}


def load_datapoints(data_dir: Path) -> List[DataPoint]:
    csvs = sorted(data_dir.glob("*.csv"))
    if not csvs:
        raise FileNotFoundError(
            f"No CSV files found in {data_dir}. Add digitized datasets as CSV."
        )

    points: List[DataPoint] = []
    for csv_path in csvs:
        for row in _iter_csv_rows(csv_path):
            # Backward compatible parsing: allow tau_value in place of tau_s.
            missing = (REQUIRED_COLUMNS - set(row.keys()))
            if missing == {"tau_s"} and ("tau_value" in row):
                missing = set()
            if missing:
                raise ValueError(
                    f"{csv_path} missing columns: {sorted(missing)} (has {sorted(row.keys())})"
                )

            tau_str = (row.get("tau_value") or row.get("tau_s") or "").strip()
            if not tau_str:
                raise ValueError(f"{csv_path} row missing tau_s/tau_value")

            points.append(
                DataPoint(
                    paper_id=row["paper_id"].strip(),
                    figure_id=row["figure_id"].strip(),
                    dataset_id=row["dataset_id"].strip(),
                    curve_id=(row.get("curve_id") or "").strip(),
                    value_kind=row["value_kind"].strip(),
                    tau_unit=row["tau_unit"].strip(),
                    tau_s=float(tau_str),
                    work_over_kT=float(row["work_over_kT"]),
                    work_err_over_kT=_parse_optional_float(row["work_err_over_kT"]),
                    digitize_sigma_work=_parse_optional_float(row.get("digitize_sigma_work", "")),
                    digitize_sigma_logtau=_parse_optional_float(row.get("digitize_sigma_logtau", "")),
                    info_bits_removed=float(row["info_bits_removed"]),
                )
            )

    # Basic sanity checks.
    for p in points:
        if p.value_kind not in ALLOWED_VALUE_KINDS:
            raise ValueError(
                f"value_kind must be one of {sorted(ALLOWED_VALUE_KINDS)}, got {p.value_kind!r}"
            )
        if p.tau_s <= 0:
            raise ValueError(f"tau_s must be >0, got {p.tau_s}")
        if p.tau_unit not in ALLOWED_TAU_UNITS:
            raise ValueError(
                f"tau_unit must be one of {sorted(ALLOWED_TAU_UNITS)}, got {p.tau_unit!r}"
            )
        if p.value_kind == "work_over_kT" and p.tau_unit == "none":
            raise ValueError("tau_unit='none' is only allowed for value_kind='a_coeff'")
        if p.value_kind == "a_coeff" and p.tau_unit not in {"none", "D_tau_over_Var"}:
            raise ValueError(
                "For value_kind='a_coeff', tau_unit must be 'none' or 'D_tau_over_Var'"
            )
        if p.info_bits_removed <= 0:
            raise ValueError(f"info_bits_removed must be >0, got {p.info_bits_removed}")
    return points


def _compute_qc_for_series(series: List[DataPoint]) -> Dict[str, Any]:
    """Dataset-level QC diagnostics (reported, not enforced)."""

    if not series:
        return {}
    pts = sorted(series, key=lambda p: p.tau_s)
    taus = [p.tau_s for p in pts]
    works = [p.work_over_kT for p in pts]

    logtaus = [math.log10(t) for t in taus if t > 0]
    slopes: List[float] = []
    jumps: List[float] = []

    for i in range(len(pts) - 1):
        dt = logtaus[i + 1] - logtaus[i]
        dw = works[i + 1] - works[i]
        jumps.append(float(dw))
        if abs(dt) > 1e-12:
            slopes.append(float(dw / dt))

    n_slope = len(slopes) or 1
    frac_pos = sum(1 for s in slopes if s > 0) / n_slope
    frac_neg = sum(1 for s in slopes if s < 0) / n_slope

    tail_n = max(5, int(0.10 * len(pts)))
    tail = works[-tail_n:]
    tail_mean = sum(tail) / len(tail)
    tail_var = sum((x - tail_mean) ** 2 for x in tail) / max(1, len(tail) - 1)
    tail_std = math.sqrt(tail_var)

    ln2 = math.log(2.0)
    below_ln2 = sum(1 for w in works if w < ln2)

    return {
        "n_points": len(pts),
        "tau_range": [min(taus), max(taus)],
        "work_range": [min(works), max(works)],
        "frac_dW_dlogtau_pos": frac_pos,
        "frac_dW_dlogtau_neg": frac_neg,
        "max_abs_jump_work": max(abs(j) for j in jumps) if jumps else 0.0,
        "tail": {
            "n": len(tail),
            "mean_work_over_kT": tail_mean,
            "std_work_over_kT": tail_std,
            "mean_minus_ln2": float(tail_mean - ln2),
        },
        "below_ln2": {
            "count": below_ln2,
            "fraction": below_ln2 / max(1, len(works)),
        },
    }


def landauer_lower_bound_over_kT(*, info_bits_removed: float) -> float:
    # Landauer for erasing 1 bit: kT ln 2 per bit.
    return float(info_bits_removed) * math.log(2.0)


def mu_lower_bound_over_kT(*, info_bits_removed: float, tau_value: float, tau_unit: str) -> float:
    # Delegate µ term to a locked model module.
    from physics.landauer.mu_models import ProtocolPoint, extra_term_over_kT, mu_protocol

    # For now, feed through the tau value as provided.
    # If tau_unit != "s", tau_value is dimensionless and the model is
    # responsible for interpreting it.
    point = ProtocolPoint(tau_s=tau_value, tau_unit=str(tau_unit), work_over_kT=float("nan"))
    mu = float(mu_protocol(point))
    extra = float(extra_term_over_kT(mu=mu, point=point))
    if extra < -1e-12:
        raise RuntimeError(f"extra_term_over_kT must be >=0, got {extra}")
    return landauer_lower_bound_over_kT(info_bits_removed=info_bits_removed) + max(extra, 0.0)


def cmd_init(args: argparse.Namespace) -> int:
    root: Path = args.root
    root.mkdir(parents=True, exist_ok=True)
    spec = ManifestSpec(name=MANIFEST_NAME, root=root)

    params = {
        "sources": list(args.sources),
        "split_policy": args.split_policy,
        "calibration_dataset": args.calibration_dataset,
        "pass_max_violation_fraction": float(args.pass_max_violation_fraction),
        "pass_tighten_fraction": float(args.pass_tighten_fraction),
    }

    init_manifest(spec, params=params, tool_files=TOOL_FILES)
    print(f"Wrote {spec.path}")
    return 0


def cmd_ingest(args: argparse.Namespace) -> int:
    root: Path = args.root
    spec = ManifestSpec(name=MANIFEST_NAME, root=root)
    manifest = require_manifest(spec)
    verify_tool_hashes(manifest, TOOL_FILES)
    verify_params_exact(
        manifest,
        {
            "sources": list(args.sources),
            "split_policy": args.split_policy,
            "calibration_dataset": args.calibration_dataset,
            "pass_max_violation_fraction": float(args.pass_max_violation_fraction),
            "pass_tighten_fraction": float(args.pass_tighten_fraction),
        },
    )

    data_dir: Path = args.data_dir
    all_points = load_datapoints(data_dir)
    sources = set(args.sources)
    points = [p for p in all_points if p.paper_id in sources]
    if not points:
        raise RuntimeError(
            f"No datapoints matched --sources={sorted(sources)} in {data_dir}. "
            "Check paper_id values in CSVs."
        )

    out_path = root / "DATA_A_INDEX.json"
    payload = {
        "data_dir": safe_relpath(data_dir, REPO_ROOT),
        "csv_files": [safe_relpath(p, REPO_ROOT) for p in sorted(data_dir.glob("*.csv"))],
        "n_points": len(points),
        "datasets": sorted({p.dataset_id for p in points}),
        "value_kinds": sorted({p.value_kind for p in points}),
        "sources": sorted(sources),
    }
    write_json(out_path, payload)

    update_manifest_artifacts(
        spec,
        artifact_paths={
            "data_index_json": out_path,
        },
    )

    print(f"Wrote {out_path}")
    return 0


def _split_points(points: List[DataPoint], *, split_policy: str, calibration_dataset: str) -> Tuple[List[DataPoint], List[DataPoint]]:
    if split_policy == "fit_none":
        # No fitting: everything is test.
        return [], points
    if split_policy == "fit_global_on_one_dataset":
        train = [p for p in points if p.dataset_id == calibration_dataset]
        test = [p for p in points if p.dataset_id != calibration_dataset]
        if not train:
            raise RuntimeError(
                f"No points found for calibration_dataset={calibration_dataset}"
            )
        if not test:
            raise RuntimeError(
                "Holdout is empty. Add at least one additional dataset_id for testing."
            )
        return train, test
    raise ValueError(f"Unknown split_policy: {split_policy}")


def _allowed_noise_over_kT(p: DataPoint) -> float:
    allowed = 0.0
    if p.work_err_over_kT is not None:
        allowed = float(p.work_err_over_kT)
    if p.digitize_sigma_work is not None:
        allowed = max(float(allowed), float(p.digitize_sigma_work))
    return float(allowed)


def _series_key(p: DataPoint) -> Tuple[str, str, str, str]:
    return (p.paper_id, p.figure_id, p.dataset_id, p.curve_id or "")


def _series_id_from_key(key: Tuple[str, str, str, str]) -> str:
    paper_id, figure_id, dataset_id, curve_id = key
    return f"{paper_id}:{figure_id}:{dataset_id}:{curve_id or 'NO_CURVE_ID'}"


def _summarize_bound_checks(
    rows: List[Dict[str, Any]],
    *,
    tighten_eps_over_kT: float,
) -> Dict[str, Any]:
    """Summarize per-point bound checks for a set of rows.

    rows are expected to have keys:
      - work_over_kT, mu_lb_over_kT, landauer_lb_over_kT, allowed_noise_over_kT
    """

    n = len(rows)
    if n == 0:
        return {
            "n": 0,
            "violation_fraction": None,
            "tighten_fraction": None,
            "tighten_fraction_over_noise": None,
        }

    violations = 0
    tightened = 0
    tightened_over_noise = 0
    for r in rows:
        work = float(r["work_over_kT"])
        mu_lb = float(r["mu_lb_over_kT"])
        land = float(r["landauer_lb_over_kT"])
        allowed = float(r.get("allowed_noise_over_kT") or 0.0)

        if work + allowed < mu_lb:
            violations += 1
        if mu_lb > land + float(tighten_eps_over_kT):
            tightened += 1
        if mu_lb > land + allowed + float(tighten_eps_over_kT):
            tightened_over_noise += 1

    return {
        "n": n,
        "violation_fraction": float(violations / n),
        "tighten_fraction": float(tightened / n),
        "tighten_fraction_over_noise": float(tightened_over_noise / n),
        "violations": int(violations),
        "tightened": int(tightened),
        "tightened_over_noise": int(tightened_over_noise),
    }


def cmd_analyze(args: argparse.Namespace) -> int:
    root: Path = args.root
    spec = ManifestSpec(name=MANIFEST_NAME, root=root)
    manifest = require_manifest(spec)
    verify_tool_hashes(manifest, TOOL_FILES)
    verify_params_exact(
        manifest,
        {
            "sources": list(args.sources),
            "split_policy": args.split_policy,
            "calibration_dataset": args.calibration_dataset,
            "pass_max_violation_fraction": float(args.pass_max_violation_fraction),
            "pass_tighten_fraction": float(args.pass_tighten_fraction),
        },
    )

    data_index = root / "DATA_A_INDEX.json"
    require_artifact_hashes(spec, required={"data_index_json": data_index})

    all_points = load_datapoints(args.data_dir)
    sources = set(args.sources)
    points = [p for p in all_points if p.paper_id in sources]
    if not points:
        raise RuntimeError(
            f"No datapoints matched --sources={sorted(sources)} in {args.data_dir}. "
            "Check paper_id values in CSVs."
        )

    work_points = [p for p in points if p.value_kind == "work_over_kT"]
    coeff_points = [p for p in points if p.value_kind == "a_coeff"]
    if not work_points:
        # Not evaluable for the primary bound test, but still write analysis.
        analysis = {
            "manifest": {"path": MANIFEST_NAME, "params": manifest.get("params")},
            "counts": {
                "total": len(points),
                "work_points": 0,
                "a_coeff_points": len(coeff_points),
                "train": 0,
                "test": 0,
            },
            "metrics": {
                "violation_fraction": None,
                "tighten_fraction": None,
            },
            "passes": {
                "max_violation_fraction": False,
                "tighten_fraction": False,
                "evaluable": False,
            },
            "notes": {
                "reason": "No value_kind='work_over_kT' rows. Primary bound test requires work measurements at a protocol duration.",
                "sources": sorted(sources),
            },
        }
        out_path = root / "analysis_A.json"
        write_json(out_path, analysis)
        update_manifest_artifacts(spec, artifact_paths={"analysis_json": out_path})
        print("\n=== PREREG A Summary ===")
        print("Not evaluable: no work points")
        print("FAIL")
        return 1

    # PREREG_A tightening term is *unit-gated*: we only apply the finite-time
    # correction when tau_unit=='D_tau_over_Var' (tau_hat). Other units remain
    # evaluable for the baseline Landauer inequality (they simply do not
    # contribute to tighten_fraction).
    tau_units = sorted({p.tau_unit for p in work_points})

    train, test = _split_points(
        work_points,
        split_policy=args.split_policy,
        calibration_dataset=args.calibration_dataset,
    )

    # QC metrics are reported across all work points (pre-split) so they are
    # invariant to split policy and help audit digitization quality.
    qc_series: Dict[str, Any] = {}
    grouped: Dict[Tuple[str, str, str, str], List[DataPoint]] = {}
    for p in work_points:
        key = (p.paper_id, p.figure_id, p.dataset_id, p.curve_id or "")
        grouped.setdefault(key, []).append(p)
    for (paper_id, figure_id, dataset_id, curve_id), pts in grouped.items():
        series_id = f"{paper_id}:{figure_id}:{dataset_id}:{curve_id or 'NO_CURVE_ID'}"
        qc_series[series_id] = _compute_qc_for_series(pts)

    # Fitting policy: only a single global scale factor allowed, optional.
    # Default: scale=1.
    scale = 1.0
    if args.split_policy == "fit_global_on_one_dataset":
        # Fit scale to minimize squared error *above* the bound is not allowed.
        # We fit only on the *observed* work to prevent tuning the bound.
        # This is conservative and can make the bound looser.
        xs: List[float] = []
        ys: List[float] = []
        for p in train:
            base = landauer_lower_bound_over_kT(info_bits_removed=p.info_bits_removed)
            xs.append(base)
            ys.append(p.work_over_kT)
        num = sum(x * y for x, y in zip(xs, ys))
        den = sum(x * x for x in xs) or 1.0
        scale = num / den

    tighten_eps_over_kT = 1e-6

    rows: List[Dict[str, Any]] = []

    for p in test:
        land = scale * landauer_lower_bound_over_kT(info_bits_removed=p.info_bits_removed)
        # Unit-gated tightening: only tau_hat rows get the finite-time correction.
        if p.tau_unit == "D_tau_over_Var":
            mu_bound = scale * mu_lower_bound_over_kT(
                info_bits_removed=p.info_bits_removed,
                tau_value=p.tau_s,
                tau_unit=p.tau_unit,
            )
        else:
            mu_bound = land
        if mu_bound < land - 1e-12:
            raise RuntimeError("µ-bound must be >= Landauer bound")

        allowed = _allowed_noise_over_kT(p)

        rows.append(
            {
                "paper_id": p.paper_id,
                "dataset_id": p.dataset_id,
                "figure_id": p.figure_id,
                "curve_id": p.curve_id,
                "tau_unit": p.tau_unit,
                "tau_s": p.tau_s,
                "tau_value": p.tau_s,
                "work_over_kT": p.work_over_kT,
                "work_err_over_kT": p.work_err_over_kT,
                "digitize_sigma_work": p.digitize_sigma_work,
                "digitize_sigma_logtau": p.digitize_sigma_logtau,
                "info_bits_removed": p.info_bits_removed,
                "landauer_lb_over_kT": land,
                "mu_lb_over_kT": mu_bound,
                "allowed_noise_over_kT": allowed,
                "tightening_applicable": bool(p.tau_unit == "D_tau_over_Var"),
            }
        )

    overall = _summarize_bound_checks(rows, tighten_eps_over_kT=tighten_eps_over_kT)
    violation_fraction = float(overall["violation_fraction"] or 0.0)
    tighten_fraction = float(overall["tighten_fraction"] or 0.0)

    # Per-series breakdown (for the sanity check you requested).
    by_series: Dict[str, List[Dict[str, Any]]] = {}
    for r in rows:
        sid = _series_id_from_key(
            (
                str(r["paper_id"]),
                str(r["figure_id"]),
                str(r["dataset_id"]),
                str(r.get("curve_id") or ""),
            )
        )
        by_series.setdefault(sid, []).append(r)

    series_metrics: Dict[str, Any] = {}
    for sid, srows in sorted(by_series.items()):
        tau_units_series = sorted({str(x["tau_unit"]) for x in srows})
        series_metrics[sid] = {
            "tau_units": tau_units_series,
            "tightening_applicable_units": ["D_tau_over_Var"],
            **_summarize_bound_checks(srows, tighten_eps_over_kT=tighten_eps_over_kT),
        }

    applicable_rows = [r for r in rows if r.get("tightening_applicable")]
    applicable = _summarize_bound_checks(applicable_rows, tighten_eps_over_kT=tighten_eps_over_kT)

    analysis = {
        "manifest": {"path": MANIFEST_NAME, "params": manifest.get("params")},
        "counts": {
            "total": len(points),
            "work_points": len(work_points),
            "a_coeff_points": len(coeff_points),
            "train": len(train),
            "test": len(test),
        },
        "fit": {"scale": scale},
        "metrics": {
            "violation_fraction": violation_fraction,
            "tighten_fraction": tighten_fraction,
            "tighten_eps_over_kT": tighten_eps_over_kT,
            "tau_units_found": tau_units,
            "applicability": {
                "tightening_applicable_units": ["D_tau_over_Var"],
                "n_applicable": int(len(applicable_rows)),
                "n_total": int(len(rows)),
                "tighten_fraction_applicable_units": applicable.get("tighten_fraction"),
                "tighten_fraction_over_noise_applicable_units": applicable.get(
                    "tighten_fraction_over_noise"
                ),
            },
        },
        "qc": {
            "series": qc_series,
        },
        "series_metrics": series_metrics,
        "passes": {
            "max_violation_fraction": violation_fraction <= float(args.pass_max_violation_fraction),
            "tighten_fraction": tighten_fraction >= float(args.pass_tighten_fraction),
            "evaluable": True,
        },
    }

    out_path = root / "analysis_A.json"
    write_json(out_path, analysis)
    update_manifest_artifacts(spec, artifact_paths={"analysis_json": out_path})

    print("\n=== PREREG A Summary ===")
    print(
        f"Test points={len(test)}  violations={int(overall.get('violations', 0))}  violation_fraction={violation_fraction:.3f}"
    )
    print(f"tighten_fraction={tighten_fraction:.3f} (fraction where µ-bound > Landauer)")
    if applicable.get("tighten_fraction") is not None:
        print(
            "tighten_fraction_applicable_units={:.3f} (units={})".format(
                float(applicable["tighten_fraction"]),
                ",".join(["D_tau_over_Var"]),
            )
        )

    ok = bool(analysis["passes"]["max_violation_fraction"]) and bool(
        analysis["passes"]["tighten_fraction"]
    )
    if not ok:
        print("FAIL")
        return 1

    print("PASS")
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="PREREG A: finite-time Landauer bound")
    p.add_argument("--root", type=Path, default=DEFAULT_ROOT)

    sub = p.add_subparsers(dest="cmd", required=True)

    p_init = sub.add_parser("init")
    p_init.add_argument(
        "--sources",
        nargs="+",
        default=[
            "JunGavrilovBechhoefer2014_arXiv1408.5089",
            "ProesmansEhrichBechhoefer2020_arXiv2006.03242",
        ],
    )
    p_init.add_argument(
        "--split-policy",
        choices=["fit_none", "fit_global_on_one_dataset"],
        default="fit_none",
    )
    p_init.add_argument("--calibration-dataset", default="Berut2012")
    p_init.add_argument("--pass-max-violation-fraction", type=float, default=0.05)
    p_init.add_argument("--pass-tighten-fraction", type=float, default=0.20)
    p_init.set_defaults(func=cmd_init)

    p_ing = sub.add_parser("ingest")
    p_ing.add_argument(
        "--data-dir",
        type=Path,
        default=REPO_ROOT / "DATA_A",
    )
    p_ing.add_argument(
        "--sources",
        nargs="+",
        default=[
            "Berut2012",
            "JunGavrilovBechhoefer2014",
            "ProesmansEhrichBechhoefer2020",
        ],
    )
    p_ing.add_argument(
        "--split-policy",
        choices=["fit_none", "fit_global_on_one_dataset"],
        default="fit_none",
    )
    p_ing.add_argument("--calibration-dataset", default="Berut2012")
    p_ing.add_argument("--pass-max-violation-fraction", type=float, default=0.05)
    p_ing.add_argument("--pass-tighten-fraction", type=float, default=0.20)
    p_ing.set_defaults(func=cmd_ingest)

    p_an = sub.add_parser("analyze")
    p_an.add_argument(
        "--data-dir",
        type=Path,
        default=REPO_ROOT / "DATA_A",
    )
    p_an.add_argument(
        "--sources",
        nargs="+",
        default=[
            "Berut2012",
            "JunGavrilovBechhoefer2014",
            "ProesmansEhrichBechhoefer2020",
        ],
    )
    p_an.add_argument(
        "--split-policy",
        choices=["fit_none", "fit_global_on_one_dataset"],
        default="fit_none",
    )
    p_an.add_argument("--calibration-dataset", default="Berut2012")
    p_an.add_argument("--pass-max-violation-fraction", type=float, default=0.05)
    p_an.add_argument("--pass-tighten-fraction", type=float, default=0.20)
    p_an.set_defaults(func=cmd_analyze)

    return p


def main() -> int:
    args = build_parser().parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
