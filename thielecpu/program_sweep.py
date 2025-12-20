"""Run small Thiele VM programs and compare μ accounting.

This module is intentionally lightweight and deterministic so it can serve as a
pytest gate and as a backend for demo scripts.

It runs real VM execution (the same VM used elsewhere in the repo), but can
suppress VM stdout for clean reporting.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Sequence, Tuple

import contextlib
import io
import json
import logging

from thielecpu.state import State
from thielecpu.vm import VM

Instruction = Tuple[str, str]


@dataclass(frozen=True)
class Workload:
    name: str
    program: Sequence[Instruction]
    metadata: Mapping[str, Any] = None  # type: ignore


def _sanitize_name(name: str) -> str:
    return "".join(ch if (ch.isalnum() or ch in "-_") else "_" for ch in name)


def run_workload(
    workload: Workload,
    *,
    outdir: Path,
    quiet: bool = True,
    auto_mdlacc: bool = True,
) -> Dict[str, Any]:
    """Run a single workload and return a summary dictionary.

    Returns a dict with:
      - name
      - outdir
      - summary (parsed summary.json)
      - ledger (parsed mu_ledger.json)
      - reasons (counts by reason)
    """

    outdir.mkdir(parents=True, exist_ok=True)
    vm = VM(State())

    # The VM is verbose by design; optionally suppress it so callers can present
    # cleaner progress output.
    if quiet:
        prior_disable = logging.root.manager.disable
        try:
            logging.disable(logging.CRITICAL)
            with contextlib.redirect_stdout(io.StringIO()):
                vm.run(list(workload.program), outdir, auto_mdlacc=auto_mdlacc)
        finally:
            logging.disable(prior_disable)
    else:
        vm.run(list(workload.program), outdir, auto_mdlacc=auto_mdlacc)

    summary_path = outdir / "summary.json"
    ledger_path = outdir / "mu_ledger.json"

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))

    reasons: Dict[str, int] = {}
    for entry in ledger:
        reason = str(entry.get("reason", ""))
        reasons[reason] = reasons.get(reason, 0) + 1

    return {
        "name": workload.name,
        "outdir": str(outdir),
        "metadata": dict(workload.metadata or {}),
        "summary": summary,
        "ledger": ledger,
        "reasons": reasons,
    }


def default_workloads(*, factoring_n: int = 15) -> List[Workload]:
    """Return a small suite of deterministic workloads.

    These are chosen to exercise distinct μ paths:
    - partition discovery/execution (PNEW/PSPLIT/PMERGE)
    - explicit information revelation (EMIT/REVEAL)
    - Python execution with factoring revelation detection (PYEXEC)
    - CHSH trial receipts (CHSH_TRIAL)
    """

    factoring_code = "\n".join(
        [
            "from thielecpu.factoring import recover_factors_partitioned",
            f"n = {int(factoring_n)}",
            "__result__ = recover_factors_partitioned(n, show_progress=False)",
        ]
    )

    return [
        Workload(
            name="noop_halt",
            program=[("HALT", "")],
            metadata={"category": "control"},
        ),
        Workload(
            name="emit_bits",
            program=[
                ("PNEW", "{1}"),
                ("EMIT", "0 8"),
                ("HALT", ""),
            ],
            metadata={"category": "information"},
        ),
        Workload(
            name="reveal_cert",
            program=[
                ("PNEW", "{1}"),
                ("REVEAL", "1 8 sweep_cert_payload"),
                ("HALT", ""),
            ],
            metadata={"category": "information"},
        ),
        Workload(
            name="partition_split_merge",
            program=[
                ("PNEW", "{1,2,3,4}"),
                # Split module 1 into odds/evens; new modules are deterministically 2 and 3.
                ("PSPLIT", "1 1"),
                ("PMERGE", "2 3"),
                ("HALT", ""),
            ],
            metadata={"category": "partition"},
        ),
        Workload(
            name="pyexec_factoring",
            program=[
                ("PNEW", "{1}"),
                ("PYEXEC", factoring_code),
                ("HALT", ""),
            ],
            metadata={"category": "pyexec", "n": int(factoring_n)},
        ),
        Workload(
            name="chsh_trials",
            program=[
                ("CHSH_TRIAL", "0 0 0 0"),
                ("CHSH_TRIAL", "0 1 0 0"),
                ("CHSH_TRIAL", "1 0 0 0"),
                ("CHSH_TRIAL", "1 1 0 1"),
                ("HALT", ""),
            ],
            metadata={"category": "chsh"},
        ),
    ]


def run_sweep(
    workloads: Sequence[Workload],
    *,
    base_outdir: Path,
    quiet: bool = True,
    auto_mdlacc: bool = True,
) -> Dict[str, Any]:
    """Run multiple workloads and write a combined report.json.

    The report schema is stable for tests:
      {"workloads": [...], "index": {name -> workload_summary}}
    """

    base_outdir.mkdir(parents=True, exist_ok=True)
    results: List[Dict[str, Any]] = []
    index: Dict[str, Dict[str, Any]] = {}

    for workload in workloads:
        work_outdir = base_outdir / _sanitize_name(workload.name)
        result = run_workload(
            workload,
            outdir=work_outdir,
            quiet=quiet,
            auto_mdlacc=auto_mdlacc,
        )
        results.append(result)
        index[workload.name] = result

    report = {
        "workloads": results,
        "index": index,
    }

    (base_outdir / "report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True), encoding="utf-8"
    )
    return report


__all__ = [
    "Instruction",
    "Workload",
    "default_workloads",
    "run_workload",
    "run_sweep",
]
