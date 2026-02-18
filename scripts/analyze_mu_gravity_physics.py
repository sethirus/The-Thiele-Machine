#!/usr/bin/env python3
"""Physics-facing empirical analysis for MuGravity.

Provides two concrete outputs from snapshot datasets:
1) Coupling scaling fit: estimate k in K ~= k * Laplacian.
2) Horizon deviation predictions: compare defect-based entropy vs GR-style area law.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

from scripts.validate_mu_gravity_calibration import (
    Snapshot,
    angle_defect_curvature,
    load_snapshots,
    mu_laplacian,
)


def horizon_area(snapshot: Snapshot, horizon: list[int], neighborhood_mode: str) -> int:
    module_ids = {m.module_id for m in snapshot.modules}
    horizon_set = {m for m in horizon if m in module_ids}

    if neighborhood_mode == "adjacent":
        module_map = {m.module_id: m for m in snapshot.modules}

        def neighbors(mid: int) -> list[int]:
            center = module_map.get(mid)
            if center is None:
                return []
            out: list[int] = []
            for other in snapshot.modules:
                if other.module_id == mid:
                    continue
                if any(x in set(other.region) for x in center.region):
                    out.append(other.module_id)
            return out

    else:

        def neighbors(mid: int) -> list[int]:
            return [m.module_id for m in snapshot.modules if m.module_id != mid]

    area = 0
    for m in horizon_set:
        for n in neighbors(m):
            if n not in horizon_set:
                area += 1
    return area


def horizon_total_defect(snapshot: Snapshot, horizon: list[int], neighborhood_mode: str) -> float:
    module_ids = {m.module_id for m in snapshot.modules}
    horizon_set = [m for m in horizon if m in module_ids]
    return sum(angle_defect_curvature(snapshot, mid, neighborhood_mode) for mid in horizon_set)


def estimate_coupling(snapshots: list[Snapshot], neighborhood_mode: str) -> dict[str, Any]:
    pairs: list[tuple[float, float]] = []  # (lap, K)
    for snap in snapshots:
        for module in snap.modules:
            lap = mu_laplacian(snap, module.module_id, neighborhood_mode)
            k = angle_defect_curvature(snap, module.module_id, neighborhood_mode)
            pairs.append((lap, k))

    denom = sum(lap * lap for lap, _ in pairs)
    if denom == 0.0:
        return {
            "point_count": len(pairs),
            "k_hat": math.pi,
            "rmse_fit": None,
            "rmse_pi": None,
            "k_hat_over_pi": 1.0,
            "note": "Degenerate data (all laplacians zero); using pi fallback.",
        }

    k_hat = sum(lap * k for lap, k in pairs) / denom

    def rmse(scale: float) -> float:
        mse = sum((k - scale * lap) ** 2 for lap, k in pairs) / max(len(pairs), 1)
        return math.sqrt(mse)

    rmse_fit = rmse(k_hat)
    rmse_pi = rmse(math.pi)

    return {
        "point_count": len(pairs),
        "k_hat": k_hat,
        "rmse_fit": rmse_fit,
        "rmse_pi": rmse_pi,
        "k_hat_over_pi": (k_hat / math.pi) if math.pi != 0 else None,
        "fit_improves_over_pi": bool(rmse_fit <= rmse_pi),
    }


def horizon_deviation_predictions(
    snapshots: list[Snapshot],
    neighborhood_mode: str,
    gravitational_constant: float,
    derived_h: float,
) -> dict[str, Any]:
    denom = 4.0 * gravitational_constant * derived_h
    if denom == 0.0:
        raise ValueError("4*G*h must be non-zero")

    predictions: list[dict[str, Any]] = []
    rel_errors: list[float] = []

    for snap in snapshots:
        horizon = [m.module_id for m in snap.modules]
        area = horizon_area(snap, horizon, neighborhood_mode)
        defect = horizon_total_defect(snap, horizon, neighborhood_mode)

        s_info = abs(defect) / denom
        s_gr = float(area) / denom
        delta = s_info - s_gr
        rel = delta / s_gr if s_gr != 0.0 else 0.0
        rel_errors.append(abs(rel))

        predictions.append(
            {
                "fuel": snap.fuel,
                "horizon_module_count": len(horizon),
                "horizon_area": area,
                "horizon_total_defect": defect,
                "entropy_info": s_info,
                "entropy_gr": s_gr,
                "entropy_delta": delta,
                "entropy_relative_delta": rel,
            }
        )

    return {
        "count": len(predictions),
        "predictions": predictions,
        "mean_abs_relative_delta": (sum(rel_errors) / len(rel_errors)) if rel_errors else 0.0,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Derive coupling and horizon deviation predictions from MuGravity snapshots.")
    parser.add_argument("--input", required=True, help="Path to snapshot JSON payload.")
    parser.add_argument("--output", default="artifacts/mu_gravity_physics_report.json", help="Output report path.")
    parser.add_argument("--neighborhood", choices=["complete", "adjacent"], default="complete")
    parser.add_argument("--gravitational-constant", type=float, default=1.0)
    parser.add_argument("--derived-h", type=float, default=1.0)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    snapshots = load_snapshots(Path(args.input))

    coupling = estimate_coupling(snapshots, args.neighborhood)
    horizon = horizon_deviation_predictions(
        snapshots,
        args.neighborhood,
        gravitational_constant=float(args.gravitational_constant),
        derived_h=float(args.derived_h),
    )

    report = {
        "snapshot_count": len(snapshots),
        "neighborhood_mode": args.neighborhood,
        "coupling_estimate": coupling,
        "horizon_predictions": horizon,
    }

    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2), encoding="utf-8")

    print(f"[mu-gravity-physics] snapshots={len(snapshots)}")
    print(f"[mu-gravity-physics] k_hat={coupling.get('k_hat')}")
    print(f"[mu-gravity-physics] report={out}")


if __name__ == "__main__":
    main()
