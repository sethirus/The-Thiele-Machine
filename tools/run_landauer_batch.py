#!/usr/bin/env python3
"""Run and verify a Landauer batch without shortcuts.

This script:
- runs experiments/run_landauer.py for multiple protocols
- runs verifier/check_landauer.py on each output directory
- writes a consolidated JSON + CSV summary under artifacts/

Designed for "real execution" and archive-friendly outputs.
"""

from __future__ import annotations

import csv
import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Mapping


REPO_ROOT = Path(__file__).resolve().parent.parent
PYTHON = sys.executable


@dataclass(frozen=True)
class BatchSpec:
    protocols: tuple[str, ...]
    seeds: tuple[int, ...]
    temps: tuple[float, ...]
    trials_per_condition: int
    steps: int
    coupling: float
    bias_final: float
    epsilon: float


def _run(cmd: list[str], *, cwd: Path) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    return proc.returncode, (proc.stdout + "\n" + proc.stderr)


def _write_csv(path: Path, rows: Iterable[Mapping[str, object]], *, fieldnames: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({k: row.get(k, "") for k in fieldnames})


def run_batch(*, out_root: Path, spec: BatchSpec) -> tuple[Path, Path]:
    stamp = time.strftime("%Y%m%d_%H%M%S")
    out_root = out_root.resolve()
    batch_dir = (out_root / f"landauer_batch_{stamp}").resolve()
    batch_dir.mkdir(parents=True, exist_ok=True)

    results: List[dict[str, object]] = []

    for protocol in spec.protocols:
        run_dir = (batch_dir / protocol).resolve()
        run_dir.mkdir(parents=True, exist_ok=True)

        run_cmd = [
            PYTHON,
            "-m",
            "experiments.run_landauer",
            "--output-dir",
            str(run_dir),
            "--protocol",
            protocol,
            "--trials-per-condition",
            str(spec.trials_per_condition),
            "--steps",
            str(spec.steps),
            "--coupling",
            str(spec.coupling),
            "--bias-final",
            str(spec.bias_final),
            "--seeds",
            *[str(s) for s in spec.seeds],
            "--temps",
            *[str(t) for t in spec.temps],
        ]
        rc, out = _run(run_cmd, cwd=REPO_ROOT)
        if rc != 0:
            raise SystemExit(f"Landauer run failed for protocol={protocol}\n{out.strip()}")

        verify_cmd = [
            PYTHON,
            str((REPO_ROOT / "verifier" / "check_landauer.py").resolve()),
            str(run_dir),
            "--epsilon",
            str(spec.epsilon),
            "--out",
            str((run_dir / "landauer_verifier.json").resolve()),
        ]
        vrc, vout = _run(verify_cmd, cwd=REPO_ROOT)
        if vrc != 0:
            raise SystemExit(f"Landauer verifier failed for protocol={protocol}\n{vout.strip()}")

        verifier_path = (run_dir / "landauer_verifier.json").resolve()
        verifier = json.loads(verifier_path.read_text(encoding="utf-8"))

        results.append(
            {
                "protocol": protocol,
                "run_dir": str(run_dir),
                "status": bool(verifier.get("status")),
                "epsilon": float(verifier.get("epsilon", spec.epsilon)),
                "trial_count": int(verifier.get("trial_count", 0)),
                "metadata_digest_matches": bool(verifier.get("metadata_digest_matches")),
            }
        )

    summary = {
        "batch_dir": str(batch_dir),
        "spec": {
            "protocols": list(spec.protocols),
            "seeds": list(spec.seeds),
            "temps": list(spec.temps),
            "trials_per_condition": spec.trials_per_condition,
            "steps": spec.steps,
            "coupling": spec.coupling,
            "bias_final": spec.bias_final,
            "epsilon": spec.epsilon,
        },
        "results": results,
        "ok": all(bool(r["status"]) for r in results),
    }

    json_path = (batch_dir / "batch_summary.json").resolve()
    json_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    csv_path = (batch_dir / "batch_summary.csv").resolve()
    _write_csv(
        csv_path,
        results,
        fieldnames=[
            "protocol",
            "status",
            "epsilon",
            "trial_count",
            "metadata_digest_matches",
            "run_dir",
        ],
    )

    return json_path, csv_path


def main(argv: list[str] | None = None) -> None:
    argv = list(sys.argv[1:] if argv is None else argv)

    out_root = (REPO_ROOT / "artifacts").resolve()

    spec = BatchSpec(
        protocols=("sighted", "blind", "destroyed"),
        seeds=(0, 1, 2),
        temps=(0.5, 1.0, 2.0),
        trials_per_condition=30,
        steps=48,
        coupling=0.7,
        bias_final=0.6931471805599453,
        epsilon=0.05,
    )

    summary_json, summary_csv = run_batch(out_root=out_root, spec=spec)
    print(f"Landauer batch OK: {summary_json}")
    print(f"CSV: {summary_csv}")


if __name__ == "__main__":
    main()
