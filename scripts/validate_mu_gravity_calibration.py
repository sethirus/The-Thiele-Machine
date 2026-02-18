#!/usr/bin/env python3
"""Empirical validator for MuGravity calibration predicates.

This script bridges runtime traces/snapshots to the obligations introduced in
`coq/kernel/MuGravity.v`:

- `dynamically_self_calibrates`
- source normalization against `mu_laplacian`

It computes Coq-aligned quantities from snapshot graphs and can emit a Coq
hypotheses file containing assumption stubs for modules/snapshots that pass
chosen tolerances.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


@dataclass(frozen=True)
class ModuleSnapshot:
    module_id: int
    region: list[int]
    axioms: list[str]


@dataclass(frozen=True)
class Snapshot:
    fuel: int
    modules: list[ModuleSnapshot]


def _normalize_axioms(raw_axioms: Any) -> list[str]:
    if raw_axioms is None:
        return []
    if isinstance(raw_axioms, list):
        return [str(item) for item in raw_axioms]
    return [str(raw_axioms)]


def _extract_modules_from_graph(graph: dict[str, Any]) -> list[ModuleSnapshot]:
    modules_out: list[ModuleSnapshot] = []

    if isinstance(graph.get("modules"), list):
        for item in graph["modules"]:
            if not isinstance(item, dict):
                continue
            module_id = int(item.get("id", item.get("module_id", -1)))
            if module_id < 0:
                continue
            region_raw = item.get("region", item.get("module_region", []))
            region = [int(x) for x in region_raw] if isinstance(region_raw, list) else []
            axioms = _normalize_axioms(item.get("axioms", item.get("module_axioms", [])))
            modules_out.append(ModuleSnapshot(module_id=module_id, region=region, axioms=axioms))
        return modules_out

    # Support VMState-like pg_modules encoding: [[id, {module_region=..., module_axioms=...}], ...]
    pg_modules = graph.get("pg_modules")
    if isinstance(pg_modules, list):
        for pair in pg_modules:
            if not (isinstance(pair, list) and len(pair) == 2):
                continue
            module_id = int(pair[0])
            payload = pair[1] if isinstance(pair[1], dict) else {}
            region_raw = payload.get("module_region", payload.get("region", []))
            region = [int(x) for x in region_raw] if isinstance(region_raw, list) else []
            axioms = _normalize_axioms(payload.get("module_axioms", payload.get("axioms", [])))
            modules_out.append(ModuleSnapshot(module_id=module_id, region=region, axioms=axioms))
    return modules_out


def _extract_snapshot(item: dict[str, Any], default_fuel: int) -> Snapshot:
    fuel = int(item.get("fuel", item.get("step", default_fuel)))
    graph = item.get("graph", item.get("vm_graph", {}))
    if not isinstance(graph, dict):
        graph = {}
    modules = _extract_modules_from_graph(graph)
    return Snapshot(fuel=fuel, modules=modules)


def load_snapshots(path: Path) -> list[Snapshot]:
    payload = json.loads(path.read_text(encoding="utf-8"))

    if isinstance(payload, dict) and isinstance(payload.get("snapshots"), list):
        raw_list = payload["snapshots"]
    elif isinstance(payload, list):
        raw_list = payload
    elif isinstance(payload, dict):
        raw_list = [payload]
    else:
        raise ValueError("Unsupported snapshot JSON structure")

    snapshots: list[Snapshot] = []
    for index, item in enumerate(raw_list):
        if not isinstance(item, dict):
            continue
        snapshots.append(_extract_snapshot(item, default_fuel=index))
    return snapshots


def _module_map(snapshot: Snapshot) -> dict[int, ModuleSnapshot]:
    return {m.module_id: m for m in snapshot.modules}


def _module_structural_mass(snapshot: Snapshot, module_id: int) -> int:
    modules = _module_map(snapshot)
    m = modules.get(module_id)
    if m is None:
        return 0
    return len(m.region) + len(m.axioms)


def _mu_module_distance(snapshot: Snapshot, m1: int, m2: int) -> int:
    if m1 == m2:
        return 0
    return 1 + _module_structural_mass(snapshot, m1) + _module_structural_mass(snapshot, m2)


def _module_neighbors_complete(snapshot: Snapshot, module_id: int) -> list[int]:
    return [m.module_id for m in snapshot.modules if m.module_id != module_id]


def _disjoint(xs: Iterable[int], ys: Iterable[int]) -> bool:
    y_set = set(ys)
    return all(x not in y_set for x in xs)


def _module_neighbors_adjacent(snapshot: Snapshot, module_id: int) -> list[int]:
    modules = _module_map(snapshot)
    center = modules.get(module_id)
    if center is None:
        return []
    neighbors: list[int] = []
    for other in snapshot.modules:
        if other.module_id == module_id:
            continue
        if not _disjoint(center.region, other.region):
            neighbors.append(other.module_id)
    return neighbors


def _module_neighbors(snapshot: Snapshot, module_id: int, neighborhood_mode: str) -> list[int]:
    if neighborhood_mode == "adjacent":
        return _module_neighbors_adjacent(snapshot, module_id)
    return _module_neighbors_complete(snapshot, module_id)


def _triangle_angle(snapshot: Snapshot, a: int, b: int, c: int) -> float:
    dab = _mu_module_distance(snapshot, a, b)
    dac = _mu_module_distance(snapshot, a, c)
    dbc = _mu_module_distance(snapshot, b, c)
    if dab == 0 or dac == 0:
        return 0.0
    return math.pi * float(dbc) / float(1 + dab + dac + dbc)


def _sum_angles(snapshot: Snapshot, module_id: int, neighborhood_mode: str) -> float:
    neighbors = _module_neighbors(snapshot, module_id, neighborhood_mode)
    total = 0.0
    for n1 in neighbors:
        for n2 in neighbors:
            if n1 == n2:
                continue
            total += _triangle_angle(snapshot, module_id, n1, n2)
    return total


def angle_defect_curvature(snapshot: Snapshot, module_id: int, neighborhood_mode: str) -> float:
    return 2.0 * math.pi - _sum_angles(snapshot, module_id, neighborhood_mode)


def _mu_cost_density(snapshot: Snapshot, module_id: int) -> float:
    modules = _module_map(snapshot)
    m = modules.get(module_id)
    return float(len(m.axioms)) if m is not None else 0.0


def mu_laplacian(snapshot: Snapshot, module_id: int, neighborhood_mode: str) -> float:
    center_density = _mu_cost_density(snapshot, module_id)
    total = 0.0
    for n in _module_neighbors(snapshot, module_id, neighborhood_mode):
        total += _mu_cost_density(snapshot, n) - center_density
    return total


def stress_energy(snapshot: Snapshot, module_id: int) -> float:
    modules = _module_map(snapshot)
    m = modules.get(module_id)
    if m is None:
        return 0.0
    encoding_length = sum(len(ax) for ax in m.axioms)
    return float(encoding_length + len(m.region))


def evaluate_snapshots(
    snapshots: list[Snapshot],
    neighborhood_mode: str,
    calibration_tol: float,
    source_tol: float,
    gravitational_constant: float,
    curvature_coupling: float,
) -> dict[str, Any]:
    snapshot_reports: list[dict[str, Any]] = []
    calibrated_total = 0
    module_total = 0

    for snap in snapshots:
        module_reports: list[dict[str, Any]] = []
        for module in snap.modules:
            k = angle_defect_curvature(snap, module.module_id, neighborhood_mode)
            lap = mu_laplacian(snap, module.module_id, neighborhood_mode)
            t = stress_energy(snap, module.module_id)
            calibration_residual = abs(k - curvature_coupling * lap)
            source_residual = abs((curvature_coupling * lap) - (16.0 * math.pi * gravitational_constant * t))
            calibrated = calibration_residual <= calibration_tol
            source_normalized = source_residual <= source_tol
            if calibrated:
                calibrated_total += 1
            module_total += 1
            module_reports.append(
                {
                    "module_id": module.module_id,
                    "angle_defect_curvature": k,
                    "mu_laplacian": lap,
                    "stress_energy": t,
                    "calibration_residual": calibration_residual,
                    "source_residual": source_residual,
                    "calibrated": calibrated,
                    "source_normalized": source_normalized,
                }
            )

        snapshot_reports.append(
            {
                "fuel": snap.fuel,
                "module_count": len(snap.modules),
                "modules": module_reports,
            }
        )

    calibration_rate = float(calibrated_total) / float(module_total) if module_total else 0.0
    report = {
        "snapshot_count": len(snapshot_reports),
        "module_count": module_total,
        "calibrated_modules": calibrated_total,
        "calibration_rate": calibration_rate,
        "neighborhood_mode": neighborhood_mode,
        "calibration_tol": calibration_tol,
        "source_tol": source_tol,
        "gravitational_constant": gravitational_constant,
        "curvature_coupling": curvature_coupling,
        "snapshots": snapshot_reports,
    }
    annotate_descent_metrics(report)
    annotate_semantic_delta_metrics(report)
    annotate_active_policy_metrics(report)
    annotate_global_descent_summary(report)
    annotate_prefix_theorem_coverage(report)
    annotate_semantic_delta_coverage(report)
    return report


def annotate_descent_metrics(report: dict[str, Any]) -> None:
    snapshots = report.get("snapshots", [])
    if not isinstance(snapshots, list):
        return

    for idx in range(1, len(snapshots)):
        prev_snap = snapshots[idx - 1]
        curr_snap = snapshots[idx]
        prev_modules = {
            int(m.get("module_id")): m for m in prev_snap.get("modules", []) if isinstance(m, dict)
        }
        for module in curr_snap.get("modules", []):
            if not isinstance(module, dict):
                continue
            module_id = int(module.get("module_id", -1))
            if module_id not in prev_modules:
                continue
            prev_res = float(prev_modules[module_id].get("calibration_residual", 0.0))
            curr_res = float(module.get("calibration_residual", 0.0))
            delta = curr_res - prev_res
            module["residual_delta_from_prev"] = delta
            module["strict_descent_from_prev"] = bool(delta < 0.0)
            module["prefix_residual_positive_prev"] = bool(prev_res > 0.0)


def annotate_semantic_delta_metrics(report: dict[str, Any]) -> None:
    snapshots = report.get("snapshots", [])
    if not isinstance(snapshots, list):
        return

    for idx in range(1, len(snapshots)):
        prev_snap = snapshots[idx - 1]
        curr_snap = snapshots[idx]
        prev_modules = {
            int(m.get("module_id")): m for m in prev_snap.get("modules", []) if isinstance(m, dict)
        }
        for module in curr_snap.get("modules", []):
            if not isinstance(module, dict):
                continue
            module_id = int(module.get("module_id", -1))
            prev_module = prev_modules.get(module_id)
            if prev_module is None:
                continue

            prev_gap = float(prev_module.get("angle_defect_curvature", 0.0)) - float(
                report.get("curvature_coupling", math.pi)
            ) * float(prev_module.get("mu_laplacian", 0.0))
            curr_gap = float(module.get("angle_defect_curvature", 0.0)) - float(
                report.get("curvature_coupling", math.pi)
            ) * float(module.get("mu_laplacian", 0.0))
            gap_delta = curr_gap - prev_gap

            module["calibration_gap_prev"] = prev_gap
            module["calibration_gap_curr"] = curr_gap
            module["calibration_gap_delta_from_prev"] = gap_delta

            window_ok = bool((prev_gap > 0.0) and ((-2.0 * prev_gap) < gap_delta < 0.0))
            module["semantic_delta_window_pos"] = window_ok


def annotate_active_policy_metrics(report: dict[str, Any]) -> None:
    snapshots = report.get("snapshots", [])
    if not isinstance(snapshots, list):
        return

    for idx in range(1, len(snapshots)):
        prev_snap = snapshots[idx - 1]
        curr_snap = snapshots[idx]
        prev_modules = {
            int(m.get("module_id")): m for m in prev_snap.get("modules", []) if isinstance(m, dict)
        }
        curr_modules = {
            int(m.get("module_id")): m for m in curr_snap.get("modules", []) if isinstance(m, dict)
        }

        prev_ids = set(prev_modules.keys())
        curr_ids = set(curr_modules.keys())

        created_modules = sorted(curr_ids - prev_ids)
        removed_modules = sorted(prev_ids - curr_ids)

        changed_existing = []
        for module_id in sorted(prev_ids & curr_ids):
            p = prev_modules[module_id]
            c = curr_modules[module_id]
            if p.get("stress_energy") != c.get("stress_energy"):
                changed_existing.append(module_id)

        active_transition = bool(created_modules or removed_modules or changed_existing)
        curr_snap["active_transition_from_prev"] = active_transition
        curr_snap["created_modules_from_prev"] = created_modules
        curr_snap["removed_modules_from_prev"] = removed_modules
        curr_snap["changed_existing_modules_from_prev"] = changed_existing

        for module in curr_snap.get("modules", []):
            if not isinstance(module, dict):
                continue
            module["prefix_policy_premises_proxy"] = bool(
                module.get("prefix_residual_positive_prev", False) and active_transition
            )
            module["prefix_theorem_outcome_proxy"] = bool(module.get("strict_descent_from_prev", False))


def annotate_global_descent_summary(report: dict[str, Any]) -> None:
    snapshots = report.get("snapshots", [])
    if not isinstance(snapshots, list):
        return

    compared = 0
    strict = 0
    nonincreasing = 0

    for snap in snapshots:
        if not isinstance(snap, dict):
            continue
        modules = snap.get("modules", [])
        if not isinstance(modules, list):
            continue
        for module in modules:
            if not isinstance(module, dict):
                continue
            if "residual_delta_from_prev" not in module:
                continue
            compared += 1
            delta = float(module["residual_delta_from_prev"])
            if delta < 0.0:
                strict += 1
            if delta <= 0.0:
                nonincreasing += 1

    report["descent_summary"] = {
        "compared_module_pairs": compared,
        "strict_descent_pairs": strict,
        "nonincreasing_pairs": nonincreasing,
        "strict_descent_rate": (float(strict) / float(compared)) if compared else 0.0,
        "nonincreasing_rate": (float(nonincreasing) / float(compared)) if compared else 0.0,
    }


def annotate_prefix_theorem_coverage(report: dict[str, Any]) -> None:
    snapshots = report.get("snapshots", [])
    if not isinstance(snapshots, list):
        return

    total_modules = 0
    premises_true = 0
    outcome_true = 0
    implication_hits = 0

    for snap in snapshots:
        if not isinstance(snap, dict):
            continue
        modules = snap.get("modules", [])
        if not isinstance(modules, list):
            continue
        for module in modules:
            if not isinstance(module, dict):
                continue
            if "prefix_policy_premises_proxy" not in module:
                continue
            total_modules += 1
            premise = bool(module.get("prefix_policy_premises_proxy", False))
            outcome = bool(module.get("prefix_theorem_outcome_proxy", False))
            if premise:
                premises_true += 1
            if outcome:
                outcome_true += 1
            if (not premise) or outcome:
                implication_hits += 1

    report["prefix_theorem_coverage"] = {
        "evaluated_modules": total_modules,
        "premises_true": premises_true,
        "outcomes_true": outcome_true,
        "implication_holds_count": implication_hits,
        "premise_rate": (float(premises_true) / float(total_modules)) if total_modules else 0.0,
        "outcome_rate": (float(outcome_true) / float(total_modules)) if total_modules else 0.0,
        "implication_hold_rate": (float(implication_hits) / float(total_modules)) if total_modules else 0.0,
    }


def annotate_semantic_delta_coverage(report: dict[str, Any]) -> None:
    snapshots = report.get("snapshots", [])
    if not isinstance(snapshots, list):
        return

    evaluated = 0
    window_true = 0
    strict_descent_when_window = 0

    for snap in snapshots:
        if not isinstance(snap, dict):
            continue
        modules = snap.get("modules", [])
        if not isinstance(modules, list):
            continue
        for module in modules:
            if not isinstance(module, dict):
                continue
            if "semantic_delta_window_pos" not in module:
                continue
            evaluated += 1
            window_ok = bool(module.get("semantic_delta_window_pos", False))
            strict_descent = bool(module.get("strict_descent_from_prev", False))
            if window_ok:
                window_true += 1
                if strict_descent:
                    strict_descent_when_window += 1

    report["semantic_delta_coverage"] = {
        "evaluated_modules": evaluated,
        "window_true": window_true,
        "strict_descent_when_window": strict_descent_when_window,
        "window_rate": (float(window_true) / float(evaluated)) if evaluated else 0.0,
        "strict_descent_given_window_rate": (
            float(strict_descent_when_window) / float(window_true) if window_true else 0.0
        ),
    }


def build_coq_hypotheses(report: dict[str, Any], include_source: bool) -> str:
    lines: list[str] = []
    lines.append("(* Auto-generated empirical hypotheses for MuGravity obligations. *)")
    lines.append("From Kernel Require Import VMState.")
    lines.append("From Kernel Require Import VMStep.")
    lines.append("From Kernel Require Import MuGravity.")
    lines.append("")
    lines.append("Parameter trace : list vm_instruction.")
    lines.append("Parameter s : VMState.")
    lines.append("")

    snapshots = report.get("snapshots", [])
    if not isinstance(snapshots, list):
        snapshots = []

    for idx, snap in enumerate(snapshots):
        fuel = int(snap.get("fuel", 0))
        prev_fuel = int(snapshots[idx - 1].get("fuel", fuel - 1)) if idx > 0 and isinstance(snapshots[idx - 1], dict) else max(fuel - 1, 0)
        for module in snap.get("modules", []):
            module_id = int(module.get("module_id", 0))
            if module.get("calibrated", False):
                lines.append(
                    f"Axiom empirical_dynamically_self_calibrates_f{fuel}_m{module_id} : "
                    f"dynamically_self_calibrates {fuel} trace s {module_id}."
                )
            if include_source and module.get("source_normalized", False):
                lines.append(
                    f"Axiom empirical_source_normalization_f{fuel}_m{module_id} : "
                    f"(curvature_coupling * mu_laplacian (run_vm {fuel} trace s) {module_id})%R = "
                    f"(16 * PI * gravitational_constant * stress_energy (run_vm {fuel} trace s) {module_id})%R."
                )
            if module.get("semantic_delta_window_pos", False):
                ax_name = f"empirical_semantic_delta_window_pos_f{prev_fuel}_m{module_id}"
                lines.append(
                    f"Axiom {ax_name} : "
                    f"(0 < calibration_gap (run_vm {prev_fuel} trace s) {module_id})%R /\\ "
                    f"(-2 * calibration_gap (run_vm {prev_fuel} trace s) {module_id} < "
                    f"(calibration_gap (run_vm {fuel} trace s) {module_id} - calibration_gap (run_vm {prev_fuel} trace s) {module_id}) < 0)%R."
                )
                if fuel == prev_fuel + 1:
                    lines.append(
                        f"Lemma empirical_semantic_progress_f{prev_fuel}_m{module_id} : "
                        f"(calibration_residual (run_vm {fuel} trace s) {module_id} < "
                        f"calibration_residual (run_vm {prev_fuel} trace s) {module_id})%R."
                    )
                    lines.append("Proof.")
                    lines.append(
                        f"  apply (calibration_progress_consecutive_run_vm_from_gap_window trace s {prev_fuel} {module_id})."
                    )
                    lines.append(f"  exact {ax_name}.")
                    lines.append("Qed.")

    if len(lines) <= 8:
        lines.append("(* No hypotheses passed configured tolerances. *)")
    lines.append("")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Validate MuGravity calibration residuals from JSON snapshots.")
    parser.add_argument("--input", required=True, help="Path to JSON snapshot payload (single snapshot, list, or {snapshots:[...]}).")
    parser.add_argument("--output", default="artifacts/mu_gravity_calibration_report.json", help="Path to write JSON report.")
    parser.add_argument(
        "--neighborhood",
        choices=["complete", "adjacent"],
        default="complete",
        help="Neighborhood model: complete (legacy) or adjacent (region-overlap locality).",
    )
    parser.add_argument("--calibration-tol", type=float, default=1e-9, help="Tolerance for |K - Δμ| calibration residual.")
    parser.add_argument("--source-tol", type=float, default=1e-9, help="Tolerance for source normalization residual.")
    parser.add_argument(
        "--gravitational-constant",
        type=float,
        default=1.0,
        help="Numeric G used for source residual checks in this empirical pass.",
    )
    parser.add_argument(
        "--curvature-coupling",
        type=float,
        default=math.pi,
        help="Numeric coupling k used in K = k*Δμ calibration checks.",
    )
    parser.add_argument(
        "--emit-coq-hypotheses",
        default=None,
        help="Optional path for generated .v hypotheses stubs from passing modules.",
    )
    parser.add_argument(
        "--include-source-hypotheses",
        action="store_true",
        help="When emitting Coq hypotheses, also include source-normalization assumptions.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    input_path = Path(args.input)
    output_path = Path(args.output)

    snapshots = load_snapshots(input_path)
    report = evaluate_snapshots(
        snapshots=snapshots,
        neighborhood_mode=args.neighborhood,
        calibration_tol=float(args.calibration_tol),
        source_tol=float(args.source_tol),
        gravitational_constant=float(args.gravitational_constant),
        curvature_coupling=float(args.curvature_coupling),
    )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(report, indent=2), encoding="utf-8")

    if args.emit_coq_hypotheses:
        hyp_path = Path(args.emit_coq_hypotheses)
        hyp_path.parent.mkdir(parents=True, exist_ok=True)
        hyp_path.write_text(
            build_coq_hypotheses(report, include_source=bool(args.include_source_hypotheses)),
            encoding="utf-8",
        )

    print(f"[mu-gravity] snapshots={report['snapshot_count']} modules={report['module_count']}")
    print(f"[mu-gravity] calibrated={report['calibrated_modules']} rate={report['calibration_rate']:.6f}")
    print(f"[mu-gravity] report={output_path}")
    if args.emit_coq_hypotheses:
        print(f"[mu-gravity] coq_hypotheses={args.emit_coq_hypotheses}")


if __name__ == "__main__":
    main()
