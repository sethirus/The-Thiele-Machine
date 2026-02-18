#!/usr/bin/env python3
"""Run long random partition traces and evaluate MuGravity calibration residuals.

This script executes random instruction-like state transitions using canonical
`thielecpu.state.State` operations and periodically snapshots the VM graph in the
JSON schema consumed by `scripts/validate_mu_gravity_calibration.py`.
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path
from typing import Any

from thielecpu._types import ModuleId
from thielecpu.state import MASK_WIDTH, State

from scripts.validate_mu_gravity_calibration import (
    ModuleSnapshot,
    Snapshot,
    evaluate_snapshots,
)


def _snapshot_from_state(step: int, state: State) -> Snapshot:
    modules = [
        ModuleSnapshot(
            module_id=int(module_id),
            region=sorted(list(region)),
            axioms=list(state.axioms.get(ModuleId(module_id), [])),
        )
        for module_id, region in sorted(state.regions.modules.items(), key=lambda item: item[0])
    ]
    return Snapshot(fuel=step, modules=modules)


def _snapshot_json(snapshot: Snapshot) -> dict[str, Any]:
    return {
        "fuel": snapshot.fuel,
        "graph": {
            "modules": [
                {
                    "id": int(module.module_id),
                    "region": list(module.region),
                    "axioms": list(module.axioms),
                }
                for module in snapshot.modules
            ]
        },
    }


def _random_region(rng: random.Random) -> set[int]:
    region_size = rng.randint(1, 4)
    return set(rng.sample(range(MASK_WIDTH), k=region_size))


def _choose_module_with_size_at_least(state: State, min_size: int, rng: random.Random) -> int | None:
    candidates = [mid for mid, region in state.regions.modules.items() if len(region) >= min_size]
    if not candidates:
        return None
    return int(rng.choice(candidates))


def _op_pnew(state: State, rng: random.Random) -> str:
    for _ in range(32):
        region = _random_region(rng)
        overlaps = any(not region.isdisjoint(existing) for existing in state.regions.modules.values())
        if overlaps:
            continue
        try:
            state.pnew(region)
            return "PNEW"
        except ValueError:
            continue
    return _op_lassert(state, rng, -1)


def _op_lassert(state: State, rng: random.Random, step: int) -> str:
    if not state.regions.modules:
        state.pnew(_random_region(rng))
        return "PNEW"
    module_id = int(rng.choice(list(state.regions.modules.keys())))
    module_key = ModuleId(module_id)
    axioms = state.axioms.setdefault(module_key, [])
    token = f"rand_ax_{step % 1024}_{rng.randint(0, 255)}"
    if len(axioms) < 4:
        axioms.append(token)
    else:
        axioms[rng.randrange(len(axioms))] = token
    return "LASSERT"


def _op_psplit(state: State, rng: random.Random) -> str:
    module_id = _choose_module_with_size_at_least(state, 2, rng)
    if module_id is None:
        return _op_pnew(state, rng)
    region = list(state.regions[ModuleId(module_id)])
    rng.shuffle(region)
    cut = rng.randint(1, len(region) - 1)
    left = set(region[:cut])
    right = set(region[cut:])
    try:
        state.psplit_explicit(ModuleId(module_id), left, right)
        return "PSPLIT"
    except ValueError:
        return _op_lassert(state, rng, -1)


def _op_pmerge(state: State, rng: random.Random) -> str:
    module_ids = list(state.regions.modules.keys())
    if len(module_ids) < 2:
        return _op_pnew(state, rng)
    rng.shuffle(module_ids)
    for i in range(len(module_ids)):
        for j in range(i + 1, len(module_ids)):
            m1 = ModuleId(int(module_ids[i]))
            m2 = ModuleId(int(module_ids[j]))
            if state.regions[m1].isdisjoint(state.regions[m2]):
                try:
                    state.pmerge(m1, m2)
                    return "PMERGE"
                except ValueError:
                    continue
    return _op_lassert(state, rng, -1)


def run_random_trace(steps: int, sample_interval: int, seed: int) -> tuple[list[Snapshot], dict[str, int]]:
    rng = random.Random(seed)
    state = State()

    op_counts = {
        "PNEW": 0,
        "LASSERT": 0,
        "PSPLIT": 0,
        "PMERGE": 0,
    }

    snapshots: list[Snapshot] = [_snapshot_from_state(step=0, state=state)]

    for step in range(1, steps + 1):
        # Keep dynamic but stable growth under module cap.
        if state.num_modules == 0:
            op = _op_pnew(state, rng)
        else:
            roll = rng.random()
            if roll < 0.50:
                op = _op_lassert(state, rng, step)
            elif roll < 0.72:
                op = _op_pnew(state, rng)
            elif roll < 0.88:
                op = _op_psplit(state, rng)
            else:
                op = _op_pmerge(state, rng)

        op_counts[op] = op_counts.get(op, 0) + 1

        if step % sample_interval == 0 or step == steps:
            snapshots.append(_snapshot_from_state(step=step, state=state))

    return snapshots, op_counts


def _find_first_nonzero(report: dict[str, Any]) -> dict[str, Any] | None:
    snapshots = report.get("snapshots", [])
    if not isinstance(snapshots, list):
        return None

    for snapshot in snapshots:
        if not isinstance(snapshot, dict):
            continue
        fuel = int(snapshot.get("fuel", -1))
        modules = snapshot.get("modules", [])
        if not isinstance(modules, list):
            continue
        for module in modules:
            if not isinstance(module, dict):
                continue
            residual = float(module.get("calibration_residual", 0.0))
            if residual != 0.0:
                return {
                    "fuel": fuel,
                    "module_id": int(module.get("module_id", -1)),
                    "calibration_residual": residual,
                }
    return None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run million-step random trace and validate MuGravity residuals.")
    parser.add_argument("--steps", type=int, default=1_000_000, help="Number of random instructions to execute.")
    parser.add_argument("--sample-interval", type=int, default=1000, help="Snapshot sampling interval in steps.")
    parser.add_argument("--seed", type=int, default=1337, help="Random seed for reproducibility.")
    parser.add_argument("--neighborhood", choices=["complete", "adjacent"], default="complete")
    parser.add_argument("--calibration-tol", type=float, default=1e-9)
    parser.add_argument("--source-tol", type=float, default=1e-9)
    parser.add_argument("--gravitational-constant", type=float, default=1.0)
    parser.add_argument("--curvature-coupling", type=float, default=3.141592653589793)
    parser.add_argument(
        "--trace-output",
        default="artifacts/mu_gravity_random_trace_1m.json",
        help="Path to write sampled trace snapshots.",
    )
    parser.add_argument(
        "--report-output",
        default="artifacts/mu_gravity_random_trace_1m_report.json",
        help="Path to write calibration report with zero-check summary.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    snapshots, op_counts = run_random_trace(
        steps=int(args.steps),
        sample_interval=max(1, int(args.sample_interval)),
        seed=int(args.seed),
    )

    report = evaluate_snapshots(
        snapshots=snapshots,
        neighborhood_mode=str(args.neighborhood),
        calibration_tol=float(args.calibration_tol),
        source_tol=float(args.source_tol),
        gravitational_constant=float(args.gravitational_constant),
        curvature_coupling=float(args.curvature_coupling),
    )

    max_residual = 0.0
    snapshots_report = report.get("snapshots", [])
    if isinstance(snapshots_report, list):
        for snapshot in snapshots_report:
            if not isinstance(snapshot, dict):
                continue
            modules = snapshot.get("modules", [])
            if not isinstance(modules, list):
                continue
            for module in modules:
                if not isinstance(module, dict):
                    continue
                max_residual = max(max_residual, float(module.get("calibration_residual", 0.0)))

    first_nonzero = _find_first_nonzero(report)
    report["run_metadata"] = {
        "steps": int(args.steps),
        "sample_interval": int(args.sample_interval),
        "seed": int(args.seed),
        "instruction_counts": op_counts,
    }
    report["zero_residual_check"] = {
        "all_sampled_module_residuals_zero": first_nonzero is None,
        "max_calibration_residual": max_residual,
        "first_nonzero": first_nonzero,
    }

    trace_payload = {
        "metadata": report["run_metadata"],
        "snapshots": [_snapshot_json(snapshot) for snapshot in snapshots],
    }

    trace_path = Path(args.trace_output)
    trace_path.parent.mkdir(parents=True, exist_ok=True)
    trace_path.write_text(json.dumps(trace_payload, indent=2), encoding="utf-8")

    report_path = Path(args.report_output)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")

    print(f"[mu-gravity-random] steps={args.steps} seed={args.seed} interval={args.sample_interval}")
    print(f"[mu-gravity-random] snapshots={len(snapshots)} modules={report.get('module_count', 0)}")
    print(
        "[mu-gravity-random] zero_residual="
        f"{report['zero_residual_check']['all_sampled_module_residuals_zero']} "
        f"max_residual={report['zero_residual_check']['max_calibration_residual']:.12f}"
    )
    print(f"[mu-gravity-random] trace={trace_path}")
    print(f"[mu-gravity-random] report={report_path}")


if __name__ == "__main__":
    main()
