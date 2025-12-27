#!/usr/bin/env python3
"""Run genesis_compression ablations with receipts + replay verification.

This script runs multiple deterministic configurations (variants) across many
seeds, emits per-run receipts/GIFs, verifies each receipt, and writes a
consolidated CSV/JSON summary.

It is intentionally conservative about runtime and artifact sizes.
"""

from __future__ import annotations

import csv
import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Tuple


REPO_ROOT = Path(__file__).resolve().parent.parent
PYTHON = sys.executable


@dataclass(frozen=True)
class Variant:
    name: str
    include_control: bool
    budget_bits: int
    pressure_stride: int


def _run(cmd: list[str], *, cwd: Path) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    return proc.returncode, (proc.stdout + "\n" + proc.stderr)


def _extract_genesis_result(receipt_path: Path) -> dict | None:
    try:
        with receipt_path.open("r", encoding="utf-8") as handle:
            for line in handle:
                obj = json.loads(line)
                if obj.get("event") == "genesis_compression_result":
                    return obj.get("result")
    except OSError:
        return None
    return None


def _write_csv(path: Path, rows: Iterable[Mapping[str, object]], *, fieldnames: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({k: row.get(k, "") for k in fieldnames})


def run_ablation(*, out_root: Path, seeds: Tuple[int, ...], variants: Tuple[Variant, ...]) -> tuple[Path, Path]:
    stamp = time.strftime("%Y%m%d_%H%M%S")
    out_root = out_root.resolve()
    batch_dir = (out_root / f"genesis_ablation_{stamp}").resolve()
    batch_dir.mkdir(parents=True, exist_ok=True)

    rows: List[Dict[str, object]] = []

    for variant in variants:
        for seed in seeds:
            run_dir = (batch_dir / variant.name / f"seed_{seed}").resolve()
            run_dir.mkdir(parents=True, exist_ok=True)

            receipt_path = (run_dir / "receipt.jsonl").resolve()
            gif_path = (run_dir / "genesis.gif").resolve()

            cmd = [
                PYTHON,
                str((REPO_ROOT / "tools" / "make_nusd_receipt.py").resolve()),
                "--domain",
                "genesis_compression",
                "--output",
                str(receipt_path),
                "--no-calibration",
                "--genesis-rule",
                "critters",
                "--genesis-width",
                "128",
                "--genesis-height",
                "128",
                "--genesis-steps",
                "4000",
                "--genesis-seed",
                str(seed),
                "--genesis-budget-bits",
                str(variant.budget_bits),
                "--genesis-dictionary-size",
                "8",
                "--genesis-pressure-stride",
                str(variant.pressure_stride),
                "--genesis-sample-every",
                "200",
                "--genesis-sample-steps",
                "0",
                "1000",
                "2000",
                "3000",
                "4000",
                "--genesis-display-phase-invert",
                "--genesis-init-density",
                "0.50",
                "--genesis-init-patch-frac",
                "1.0",
                "--genesis-render-hud",
                "--genesis-no-render-delta",
                "--genesis-render-motion",
                "--genesis-render-trail",
                "--genesis-trail-decay",
                "245",
                "--genesis-trail-threshold",
                "64",
                "--genesis-gif-path",
                str(gif_path),
                "--genesis-gif-scale",
                "3",
                "--genesis-gif-fps",
                "15",
            ]
            if variant.include_control:
                cmd.append("--genesis-include-control")
            else:
                cmd.append("--genesis-no-control")

            rc, out = _run(cmd, cwd=REPO_ROOT)
            if rc != 0:
                raise SystemExit(f"genesis run failed for {variant.name} seed={seed}\n{out.strip()}")

            verify_cmd = [
                PYTHON,
                str((REPO_ROOT / "tools" / "verify_nusd_receipt.py").resolve()),
                str(receipt_path),
                "--skip-calibration",
            ]
            vrc, vout = _run(verify_cmd, cwd=REPO_ROOT)
            if vrc != 0 or "Receipt verification succeeded" not in vout:
                raise SystemExit(
                    f"genesis receipt verify failed for {variant.name} seed={seed}\n{vout.strip()}"
                )

            res = _extract_genesis_result(receipt_path) or {}
            rows.append(
                {
                    "variant": variant.name,
                    "seed": seed,
                    "include_control": variant.include_control,
                    "budget_bits": variant.budget_bits,
                    "pressure_stride": variant.pressure_stride,
                    "pdiscover_count": int(res.get("pdiscover_count", 0)),
                    "bits_first": int(res.get("bits_first", 0)),
                    "bits_last": int(res.get("bits_last", 0)),
                    "motion_mass_sum": int(res.get("motion_mass_sum", 0) or 0),
                    "motion_cc_max_max": int(res.get("motion_cc_max_max", 0) or 0),
                    "motion_centroid_l1_path_q": int(res.get("motion_centroid_l1_path_q", 0) or 0),
                    "trail_mass_sum": int(res.get("trail_mass_sum", 0) or 0),
                    "trail_cc_max_max": int(res.get("trail_cc_max_max", 0) or 0),
                    "trail_intensity_sum": int(res.get("trail_intensity_sum", 0) or 0),
                    "gif_sha256": str(res.get("video_sha256", "")),
                    "receipt_path": str(receipt_path),
                    "gif_path": str(gif_path),
                }
            )

    summary = {
        "batch_dir": str(batch_dir),
        "seeds": list(seeds),
        "variants": [variant.__dict__ for variant in variants],
        "rows": rows,
    }

    json_path = (batch_dir / "ablation_summary.json").resolve()
    json_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    csv_path = (batch_dir / "ablation_summary.csv").resolve()
    _write_csv(
        csv_path,
        rows,
        fieldnames=[
            "variant",
            "seed",
            "include_control",
            "budget_bits",
            "pressure_stride",
            "pdiscover_count",
            "bits_first",
            "bits_last",
            "motion_mass_sum",
            "motion_cc_max_max",
            "motion_centroid_l1_path_q",
            "trail_mass_sum",
            "trail_cc_max_max",
            "trail_intensity_sum",
            "gif_sha256",
            "receipt_path",
            "gif_path",
        ],
    )

    return json_path, csv_path


def main(argv: list[str] | None = None) -> None:
    out_root = (REPO_ROOT / "artifacts").resolve()
    seeds = (20251226, 20251227, 20251228)
    variants = (
        Variant(name="pressured", include_control=True, budget_bits=28000, pressure_stride=5),
        Variant(name="high_budget", include_control=True, budget_bits=52000, pressure_stride=5),
        Variant(name="rare_pressure", include_control=True, budget_bits=28000, pressure_stride=20),
    )

    json_path, csv_path = run_ablation(out_root=out_root, seeds=seeds, variants=variants)
    print(f"Genesis ablation OK: {json_path}")
    print(f"CSV: {csv_path}")


if __name__ == "__main__":
    main()
