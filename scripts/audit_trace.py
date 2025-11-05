#!/usr/bin/env python3
"""Audit blind solver traces against the formal separation model."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, List


def _bool(value) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        return value.lower() in {"1", "true", "t", "yes", "y"}
    raise AssertionError(f"cannot coerce {value!r} to bool")


def audit_trace_file(path: Path) -> Dict[str, int]:
    data = json.loads(path.read_text())
    trace: List[Dict[str, object]] = data.get("trace", [])
    variables: List[int] = data.get("variables", [])
    status = data.get("status")
    recorded_decisions = int(data.get("decisions", 0))
    recorded_conflicts = int(data.get("conflicts", 0))
    recorded_backtracks = int(data.get("backtracks", 0))

    if status not in {"sat", "unsat"}:
        raise AssertionError(f"{path}: unexpected status {status!r}")
    if not isinstance(trace, list):
        raise AssertionError(f"{path}: trace must be a list")
    if not isinstance(variables, list):
        raise AssertionError(f"{path}: variables must be a list")

    var_set = {int(v) for v in variables}
    assignments: Dict[int, bool] = {}
    stack: List[int] = []
    depth = 0
    decisions = conflicts = backtracks = 0

    for event in trace:
        if not isinstance(event, dict):
            raise AssertionError(f"{path}: malformed event {event!r}")
        etype = event.get("type")
        event_depth = int(event.get("depth", depth))
        if etype == "decide":
            var = int(event.get("var"))
            if var not in var_set:
                raise AssertionError(f"{path}: decision on unknown variable {var}")
            if var in assignments:
                raise AssertionError(f"{path}: variable {var} decided twice without backtrack")
            if event_depth != depth:
                raise AssertionError(f"{path}: decide depth mismatch (expected {depth}, got {event_depth})")
            value = _bool(event.get("value"))
            assignments[var] = value
            stack.append(var)
            depth += 1
            decisions += 1
        elif etype == "conflict":
            if event_depth != depth:
                raise AssertionError(f"{path}: conflict depth mismatch (expected {depth}, got {event_depth})")
            if not stack:
                raise AssertionError(f"{path}: conflict with empty stack")
            conflicts += 1
        elif etype == "backtrack":
            var = int(event.get("var"))
            if depth == 0 or not stack or stack[-1] != var:
                raise AssertionError(f"{path}: backtrack order mismatch at variable {var}")
            depth -= 1
            stack.pop()
            assignments.pop(var, None)
            backtracks += 1
        else:
            raise AssertionError(f"{path}: unknown event type {etype!r}")

    if stack and status == "unsat":
        raise AssertionError(f"{path}: unsat trace finished with assignments still on stack")

    if decisions != recorded_decisions or conflicts != recorded_conflicts or backtracks != recorded_backtracks:
        raise AssertionError(
            f"{path}: counter mismatch (decisions {decisions}/{recorded_decisions}, "
            f"conflicts {conflicts}/{recorded_conflicts}, backtracks {backtracks}/{recorded_backtracks})"
        )

    varcount = len(var_set)
    if status == "unsat" and varcount > 0:
        lower_bound = 2 ** max(0, varcount - 1)
        if decisions < lower_bound:
            raise AssertionError(
                f"{path}: decisions {decisions} below exponential lower bound {lower_bound} for {varcount} vars"
            )

    return {"decisions": decisions, "conflicts": conflicts, "backtracks": backtracks, "variables": varcount}


def main(argv: List[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit blind solver traces")
    parser.add_argument("trace", nargs="+", help="Trace files to audit")
    args = parser.parse_args(argv)

    ok = True
    for name in args.trace:
        path = Path(name)
        try:
            audit_trace_file(path)
            print(f"{path}: OK")
        except AssertionError as exc:  # pragma: no cover - CLI diagnostics
            ok = False
            print(str(exc), file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
