#!/usr/bin/env python3
"""Generate structured Thiele self-traces across canonical workloads."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, TextIO, Tuple

import os
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from thielecpu.assemble import parse
from thielecpu.state import State
from thielecpu.vm import TraceConfig, VM

TRACE_DIR = Path("artifacts/self_traces")
DEFAULT_INDEX = TRACE_DIR / "self_trace_index.json"
DEFAULT_SEED = 1337


class SelfTraceWriter:
    """Observer that records VM trace events as JSONL."""

    def __init__(self, path: Path) -> None:
        self._path = path
        self._handle: TextIO | None = None
        self._hasher = hashlib.sha256()
        self._step_count = 0
        self.digest: str | None = None

    def _write(self, payload: Mapping[str, object]) -> None:
        if self._handle is None:
            raise RuntimeError("trace writer not initialised")
        line = json.dumps(payload, sort_keys=True)
        self._handle.write(line + "\n")
        self._handle.flush()
        self._hasher.update((line + "\n").encode("utf-8"))

    def on_start(self, payload: Mapping[str, object]) -> None:  # pragma: no cover - exercised via CLI
        TRACE_DIR.mkdir(parents=True, exist_ok=True)
        self._path.parent.mkdir(parents=True, exist_ok=True)
        self._handle = self._path.open("w", encoding="utf-8")
        start_payload = dict(payload)
        start_payload.setdefault("event", "trace_start")
        self._write(start_payload)

    def on_step(self, payload: Mapping[str, object]) -> None:  # pragma: no cover - exercised via CLI
        if self._handle is None:
            return
        self._step_count += 1
        step_payload = dict(payload)
        step_payload.setdefault("event", "trace_step")
        self._write(step_payload)

    def on_finish(self, payload: Mapping[str, object]) -> None:  # pragma: no cover - exercised via CLI
        if self._handle is None:
            return
        finish_payload = dict(payload)
        finish_payload.setdefault("event", "trace_end")
        finish_payload.setdefault("steps", self._step_count)
        self._write(finish_payload)
        self._handle.close()
        self._handle = None
        self.digest = self._hasher.hexdigest()


@dataclass
class Workload:
    name: str
    builder: callable
    seed: int


def _render_program(lines: Iterable[str], base: Path) -> List[Tuple[str, str]]:
    program_lines = [line.rstrip() for line in lines]
    return parse(program_lines, base)


def _write_unsat_config(run_dir: Path) -> Path:
    cnf_path = run_dir / "unsat.cnf"
    cnf_path.write_text("p cnf 1 2\n1 0\n-1 0\n", encoding="utf-8")
    proof_path = run_dir / "unsat.lrat"
    proof_path.write_text("3 0 1 2 0\n", encoding="utf-8")
    config_path = run_dir / "unsat.json"
    config = {
        "cnf": str(cnf_path.resolve()),
        "proof_type": "LRAT",
        "proof": str(proof_path.resolve()),
    }
    config_path.write_text(json.dumps(config, indent=2), encoding="utf-8")
    return config_path.resolve()


def build_idle(run_dir: Path, seed: int) -> Tuple[List[str], Mapping[str, object]]:
    rng = random.Random(seed)
    steps = rng.randint(4, 6)
    lines: List[str] = ["PNEW {1,2,3,4}"]
    for idx in range(steps):
        lines.append("MDLACC")
        lines.append(f'EMIT "idle-pulse-{idx}"')
    lines.append("MDLACC")
    lines.append('EMIT "idle-complete"')
    return lines, {"pulses": steps}


def build_partition(run_dir: Path, seed: int) -> Tuple[List[str], Mapping[str, object]]:
    lines = [
        "PNEW {1,2,3,4,5,6}",
        "MDLACC 1",
        "PSPLIT 2",
        "MDLACC 1",
        "PMERGE 3 4",
        "MDLACC 1",
        'EMIT "partition-cycle"',
        "MDLACC 1",
    ]
    return lines, {"notes": "split and merge synthetic region"}


def build_proof(run_dir: Path, seed: int) -> Tuple[List[str], Mapping[str, object]]:
    config_path = _write_unsat_config(run_dir)
    lines = [
        "PNEW {1,2}",
        "MDLACC",
        'EMIT "proof-setup"',
        f'LASSERT "{config_path}"',
    ]
    return lines, {"config": str(config_path)}


def build_turbulence(run_dir: Path, seed: int) -> Tuple[List[str], Mapping[str, object]]:
    summary_name = "turbulence_stats.json"
    script_path = run_dir / "turbulence_workload.py"
    script = f"""
import json
import math
series = [math.log(1 + i * 0.5) for i in range(1, 33)]
mean = sum(series) / len(series)
variance = sum((value - mean) ** 2 for value in series) / len(series)
vm_write_text('{summary_name}', json.dumps({{'mean': mean, 'variance': variance}}, indent=2))
print('turbulence-mean', mean)
"""
    script_path.write_text(script, encoding="utf-8")
    lines = [
        "PNEW {1,2,3}",
        f'PYEXEC "{script_path.name}"',
        "MDLACC",
        'EMIT "turbulence-summary"',
        "MDLACC",
        'EMIT "turbulence-complete"',
    ]
    return lines, {"summary": summary_name}


WORKLOADS: List[Workload] = [
    Workload("idle", build_idle, DEFAULT_SEED + 1),
    Workload("partition", build_partition, DEFAULT_SEED + 2),
    Workload("proof", build_proof, DEFAULT_SEED + 3),
    Workload("turbulence", build_turbulence, DEFAULT_SEED + 4),
]


def generate_traces(index_path: Path) -> List[MutableMapping[str, object]]:
    results: List[MutableMapping[str, object]] = []
    for workload in WORKLOADS:
        run_dir = TRACE_DIR / f"{workload.name}_{workload.seed}"
        run_dir.mkdir(parents=True, exist_ok=True)
        program_lines, metadata = workload.builder(run_dir, workload.seed)
        program = _render_program(program_lines, run_dir)
        vm = VM(State())
        trace_file = TRACE_DIR / f"{workload.name}_{workload.seed}.jsonl"
        writer = SelfTraceWriter(trace_file)
        config = TraceConfig(
            workload_id=workload.name,
            observer=writer,
            metadata={"seed": workload.seed, **metadata},
        )
        vm.run(program, run_dir, trace_config=config)
        digest = writer.digest or hashlib.sha256(trace_file.read_bytes()).hexdigest()
        entry: MutableMapping[str, object] = {
            "workload": workload.name,
            "seed": workload.seed,
            "path": str(trace_file),
            "sha256": digest,
            "steps": writer._step_count,
            "metadata": metadata,
        }
        results.append(entry)
    index_path.parent.mkdir(parents=True, exist_ok=True)
    index_path.write_text(json.dumps({"traces": results}, indent=2), encoding="utf-8")
    return results


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--index",
        type=Path,
        default=DEFAULT_INDEX,
        help="output index file (JSON)",
    )
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    entries = generate_traces(args.index)
    print(f"Generated {len(entries)} self-traces -> {args.index}")
    for entry in entries:
        print(f"  - {entry['workload']}: {entry['steps']} steps (sha256={entry['sha256'][:16]}…)")


if __name__ == "__main__":
    main()


__all__ = ["generate_traces", "TRACE_DIR", "DEFAULT_INDEX"]
