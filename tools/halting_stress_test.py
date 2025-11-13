"""Halting oracle stress test for the Thiele VM.

This script instantiates a handful of tiny register-machine programs, asks the
Thiele VM to classify whether each program halts when run on its own encoded
input, and compares that verdict to an ordinary step-bounded interpreter.  It
is designed to probe whether the Python implementation leaks any extra
information beyond what a straightforward simulation can derive.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

try:  # Allow running as a script without installing the package
    from thielecpu.assemble import Instruction
    from thielecpu.state import State
    from thielecpu.vm import VM
except ModuleNotFoundError:  # pragma: no cover - runtime convenience
    import os
    import sys

    REPO_ROOT = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(REPO_ROOT))
    from thielecpu.assemble import Instruction
    from thielecpu.state import State
    from thielecpu.vm import VM


@dataclass
class ToyProgram:
    """Minimal register-machine program used for halting experiments."""

    name: str
    instructions: List[Dict[str, int | str]]
    initial_state: Dict[str, int]
    description: str


def _program_specs() -> List[ToyProgram]:
    """Return the catalogue of tiny programs under test."""

    return [
        ToyProgram(
            name="halt_immediately",
            instructions=[{"op": "HALT"}],
            initial_state={"__input__": 0},
            description="Trivial program that halts without touching state.",
        ),
        ToyProgram(
            name="countdown_three",
            instructions=[
                {"op": "DECJNZ", "reg": "counter", "target": 0},
                {"op": "HALT"},
            ],
            initial_state={"counter": 3, "__input__": 1},
            description="Countdown loop that decrements a counter then halts.",
        ),
        ToyProgram(
            name="self_loop",
            instructions=[{"op": "GOTO", "target": 0}],
            initial_state={"__input__": 2},
            description="Immediate self-loop with no halting branch.",
        ),
        ToyProgram(
            name="branch_on_input",
            instructions=[
                {"op": "JZ", "reg": "flag", "target": 2},
                {"op": "HALT"},
                {"op": "GOTO", "target": 2},
            ],
            initial_state={"flag": 0, "__input__": 3},
            description="Halts iff the provided flag is zero; otherwise loops.",
        ),
        ToyProgram(
            name="diagonal_like",
            instructions=[
                {"op": "SET", "reg": "flag", "value": "__input__"},
                {"op": "JZ", "reg": "flag", "target": 3},
                {"op": "GOTO", "target": 1},
                {"op": "HALT"},
            ],
            initial_state={"__input__": 0},
            description=(
                "Toggles on its own index: loops when the encoded input is non-zero, "
                "halts otherwise.  This mimics a diagonal self-query in miniature."
            ),
        ),
    ]


def _normalise_state(state: Dict[str, int]) -> Tuple[Tuple[str, int], ...]:
    """Return a hashable representation of the current machine state."""

    return tuple(sorted(state.items()))


def _simulate_baseline(program: ToyProgram, max_steps: int) -> Dict[str, object]:
    """Run the toy program with a naive interpreter."""

    pc = 0
    steps = 0
    state = dict(program.initial_state)
    visited = set()

    while steps < max_steps:
        key = (pc, _normalise_state(state))
        if key in visited:
            return {
                "status": "LOOP",
                "steps": steps,
                "pc": pc,
                "final_state": state,
            }
        visited.add(key)

        if pc < 0 or pc >= len(program.instructions):
            return {
                "status": "CRASH",
                "steps": steps,
                "pc": pc,
                "final_state": state,
            }

        inst = program.instructions[pc]
        op = inst["op"]

        if op == "HALT":
            steps += 1
            return {
                "status": "HALTS",
                "steps": steps,
                "pc": pc,
                "final_state": state,
            }
        elif op == "GOTO":
            pc = int(inst["target"])
        elif op == "JZ":
            reg = str(inst["reg"])
            target = int(inst["target"])
            if state.get(reg, 0) == 0:
                pc = target
            else:
                pc += 1
        elif op == "DECJNZ":
            reg = str(inst["reg"])
            target = int(inst["target"])
            if state.get(reg, 0) > 0:
                state[reg] = state.get(reg, 0) - 1
                pc = target
            else:
                pc += 1
        elif op == "SET":
            reg = str(inst["reg"])
            value = inst.get("value", 0)
            if value == "__input__":
                state[reg] = state.get("__input__", 0)
            else:
                state[reg] = int(value)
            pc += 1
        else:
            return {
                "status": "ERROR",
                "steps": steps,
                "pc": pc,
                "final_state": state,
                "error": f"unknown op {op}",
            }

        steps += 1

    return {
        "status": "UNKNOWN",
        "steps": steps,
        "pc": pc,
        "final_state": state,
    }


def _pyexec_code(program: ToyProgram, max_steps: int) -> str:
    """Generate a PYEXEC payload mirroring the baseline interpreter."""

    # Inline the program as JSON for readability inside the sandbox.
    program_blob = json.dumps(program.instructions)
    state_blob = json.dumps(program.initial_state)

    return f"""
import json

program = json.loads('{program_blob}')
state = json.loads('{state_blob}')
max_steps = {max_steps}

pc = 0
steps = 0
visited = set()
status = "UNKNOWN"

while steps < max_steps:
    key = (pc, tuple(sorted(state.items())))
    if key in visited:
        status = "LOOP"
        break
    visited.add(key)

    if pc < 0 or pc >= len(program):
        status = "CRASH"
        break

    inst = program[pc]
    op = inst['op']

    if op == 'HALT':
        steps += 1
        status = 'HALTS'
        break
    elif op == 'GOTO':
        pc = int(inst['target'])
    elif op == 'JZ':
        reg = str(inst['reg'])
        target = int(inst['target'])
        if state.get(reg, 0) == 0:
            pc = target
        else:
            pc += 1
    elif op == 'DECJNZ':
        reg = str(inst['reg'])
        target = int(inst['target'])
        if state.get(reg, 0) > 0:
            state[reg] = state.get(reg, 0) - 1
            pc = target
        else:
            pc += 1
    elif op == 'SET':
        reg = str(inst['reg'])
        value = inst.get('value', 0)
        if value == '__input__':
            state[reg] = state.get('__input__', 0)
        else:
            state[reg] = int(value)
        pc += 1
    else:
        status = 'ERROR:' + op
        break

    steps += 1
else:
    status = 'UNKNOWN'

__result__ = {{
    'status': status,
    'steps': steps,
    'pc': pc,
    'final_state': state,
}}
"""


def _run_vm(program: ToyProgram, max_steps: int, outdir: Path) -> Dict[str, object]:
    """Execute the program on the Thiele VM and return the PYEXEC verdict."""

    state = State()
    vm = VM(state=state)
    payload = _pyexec_code(program, max_steps)
    instructions: List[Instruction] = [("PYEXEC", payload)]
    vm.run(instructions, outdir=outdir)
    result = vm.python_globals.get("_last_result")
    if isinstance(result, dict):
        return result
    return {"status": "NO_RESULT", "detail": result}


def _ensure_directory(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def run_analysis(max_steps: int, output: Path) -> Dict[str, object]:
    """Run the halting comparison and return a structured report."""

    specs = _program_specs()
    results: List[Dict[str, object]] = []
    vm_root = output.parent / "vm_runs"
    _ensure_directory(vm_root)

    for spec in specs:
        baseline = _simulate_baseline(spec, max_steps)
        vm_dir = vm_root / spec.name
        vm_result = _run_vm(spec, max_steps, vm_dir)
        results.append(
            {
                "program": spec.name,
                "description": spec.description,
                "initial_state": spec.initial_state,
                "baseline": baseline,
                "vm": vm_result,
                "agreement": baseline.get("status") == vm_result.get("status"),
            }
        )

    report = {"max_steps": max_steps, "programs": results}
    _ensure_directory(output.parent)
    output.write_text(json.dumps(report, indent=2))
    return report


def _print_report(report: Dict[str, object]) -> None:
    """Pretty-print a brief summary of the comparison table."""

    print(f"Max simulation steps: {report['max_steps']}")
    print("Program                           Baseline   VM verdict   Agree?")
    print("-" * 72)
    for item in report["programs"]:
        baseline_status = item["baseline"]["status"]
        vm_status = item["vm"]["status"]
        agree = "yes" if item["agreement"] else "NO"
        print(
            f"{item['program']:<32} {baseline_status:<10} {vm_status:<12} {agree}"
        )


def main(argv: Iterable[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-steps",
        type=int,
        default=32,
        help="Number of interpreter steps before declaring UNKNOWN.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/halting/results.json"),
        help="Where to write the JSON summary.",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    report = run_analysis(args.max_steps, args.output)
    _print_report(report)

    if any(not item["agreement"] for item in report["programs"]):
        print("Detected disagreement between baseline and VM runs.", file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
