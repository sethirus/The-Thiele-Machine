#!/usr/bin/env python3
"""Assumption and dependency audit for key Coq theorems.

This is meant to support an intellectually honest "0 axioms" claim:
- It runs `Print Assumptions` on selected theorems.
- It records the raw `coqtop` output so reviewers can inspect it.

By default it audits the kernel TOE no-go theorem and the compositional-weight
non-uniqueness theorem.

Usage:
  /path/to/python tools/coq_assumption_audit.py --output artifacts/coq/assumptions.json
"""

from __future__ import annotations

import argparse
import json
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


@dataclass(frozen=True)
class TheoremTarget:
    require: str
    qualified_name: str


DEFAULT_TARGETS: Sequence[TheoremTarget] = (
    TheoremTarget(
        require="From KernelTOE Require Import NoGo.",
        qualified_name="KernelTOE.NoGo.KernelNoGoForTOE",
    ),
    TheoremTarget(
        require="From Kernel Require Import ProbabilityImpossibility.",
        qualified_name="Kernel.ProbabilityImpossibility.Born_Rule_Unique_Fails_Without_More_Structure",
    ),
)


def _loadpath_args_from_coqproject(repo_root: Path) -> List[str]:
    coqproject = repo_root / "coq" / "_CoqProject"
    lines = coqproject.read_text(encoding="utf-8").splitlines()
    args: List[str] = []
    for raw in lines:
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("-Q ") or line.startswith("-R "):
            parts = line.split()
            if len(parts) >= 3:
                flag, rel_path, logical = parts[0], parts[1], parts[2]
                args.extend([flag, str(repo_root / "coq" / rel_path), logical])
    return args


def _run_coqtop(repo_root: Path, commands: Sequence[str]) -> str:
    loadpath = _loadpath_args_from_coqproject(repo_root)
    proc = subprocess.run(
        ["coqtop", "-quiet", *loadpath],
        input="\n".join(commands) + "\n",
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        cwd=str(repo_root),
        check=False,
    )
    return proc.stdout


def audit_assumptions(repo_root: Path, targets: Sequence[TheoremTarget]) -> Dict[str, object]:
    payload: Dict[str, object] = {
        "repo_root": str(repo_root),
        "targets": [
            {"require": t.require, "qualified_name": t.qualified_name} for t in targets
        ],
        "results": [],
    }

    for target in targets:
        commands = [
            target.require,
            "Set Printing Width 120.",
            f"Print Assumptions {target.qualified_name}.",
        ]
        out = _run_coqtop(repo_root, commands)
        payload["results"].append(
            {
                "qualified_name": target.qualified_name,
                "require": target.require,
                "coqtop_output": out,
            }
        )

    return payload


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts") / "coq" / "assumption_audit.json",
        help="Where to write the captured coqtop output.",
    )
    return p.parse_args(list(argv) if argv is not None else None)


def main(argv: Iterable[str] | None = None) -> int:
    args = parse_args(argv)
    repo_root = Path(__file__).resolve().parents[1]

    payload = audit_assumptions(repo_root, list(DEFAULT_TARGETS))

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    print(f"Wrote Coq assumption audit: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
