"""Enumerate tiny Thiele programs and compare halting judgements.

This script explores a bounded search space of miniature register-machine
programs, runs each instance through the reference step-by-step interpreter,
and contrasts the verdict with the Thiele VM executing the mirrored PYEXEC
payload.  The goal is to spot any divergences where the VM appears to decide a
halting question that the bounded interpreter cannot settle within the
configured step budget.
"""

from __future__ import annotations

import argparse
import json
import sys
import random
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Sequence, Tuple

try:
    from tools import halting_stress_test
except ModuleNotFoundError:  # pragma: no cover - standalone execution
    import os
    import sys

    REPO_ROOT = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(REPO_ROOT))
    from tools import halting_stress_test

ToyProgram = halting_stress_test.ToyProgram


Instruction = Dict[str, int | str]
State = Dict[str, int]


def _instruction_templates(length: int) -> Sequence[Instruction]:
    """Return the palette of instructions allowed in the enumeration."""

    templates: List[Instruction] = [{"op": "HALT"}]
    for target in range(length):
        templates.extend(
            [
                {"op": "GOTO", "target": target},
                {"op": "DECJNZ", "reg": "flag", "target": target},
                {"op": "JZ", "reg": "flag", "target": target},
            ]
        )
    templates.extend(
        [
            {"op": "SET", "reg": "flag", "value": 0},
            {"op": "SET", "reg": "flag", "value": 1},
            {"op": "SET", "reg": "flag", "value": "__input__"},
        ]
    )
    return templates


def _enumerate_programs(max_length: int, limit: int) -> Iterator[ToyProgram]:
    """Generate candidate programs up to ``max_length`` instructions long."""

    counter = 0
    for length in range(1, max_length + 1):
        templates = _instruction_templates(length)
        choices = len(templates)
        for indices in range(choices ** length):
            if counter >= limit:
                return
            ops: List[Instruction] = []
            value = indices
            for _ in range(length):
                template = templates[value % choices]
                value //= choices
                ops.append(dict(template))
            for flag_init in (0, 1):
                for input_init in (0, 1):
                    if counter >= limit:
                        return
                    counter += 1
                    yield ToyProgram(
                        name=f"enumerated_{counter:03d}",
                        instructions=ops,
                        initial_state={"flag": flag_init, "__input__": input_init},
                        description=(
                            "Enumerated program with shared flag/input initial state "
                            "for diagonal halting survey"
                        ),
                    )


@dataclass
class SurveyResult:
    program: ToyProgram
    baseline: Dict[str, object]
    vm: Dict[str, object]

    @property
    def agrees(self) -> bool:
        return self.baseline.get("status") == self.vm.get("status")


def _run_program(program: ToyProgram, max_steps: int, workdir: Path) -> SurveyResult:
    baseline = halting_stress_test._simulate_baseline(program, max_steps)
    vm_dir = workdir / program.name
    vm = halting_stress_test._run_vm(program, max_steps, vm_dir)
    return SurveyResult(program=program, baseline=baseline, vm=vm)


def _summarise(results: Sequence[SurveyResult]) -> Dict[str, object]:
    anomalies = [
        {
            "program": res.program.name,
            "instructions": res.program.instructions,
            "initial_state": res.program.initial_state,
            "baseline": res.baseline,
            "vm": res.vm,
        }
        for res in results
        if not res.agrees
    ]
    return {
        "checked": len(results),
        "anomalies": anomalies,
    }


def run_survey(max_length: int, sample_size: int, max_steps: int, output: Path) -> Dict[str, object]:
    """Execute the enumeration survey and persist a compact JSON summary."""

    rng = random.Random(0xC0DE)
    programs = list(_enumerate_programs(max_length, sample_size * 4))
    rng.shuffle(programs)
    selected = programs[:sample_size]

    with tempfile.TemporaryDirectory(prefix="thiele_halting_survey_") as tmp:
        workdir = Path(tmp)
        results = [
            _run_program(program, max_steps, workdir)
            for program in selected
        ]

    summary = {
        "max_length": max_length,
        "sample_size": sample_size,
        "max_steps": max_steps,
        **_summarise(results),
    }

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True))
    return summary


def _print_summary(summary: Dict[str, object]) -> None:
    print(
        "Checked {sample_size} programs (length ≤ {max_length}, steps {max_steps}).".format(
            sample_size=summary["sample_size"],
            max_length=summary["max_length"],
            max_steps=summary["max_steps"],
        )
    )
    anomalies: List[Dict[str, object]] = summary.get("anomalies", [])
    if not anomalies:
        print("No VM/baseline disagreements detected.")
        return
    print(f"Detected {len(anomalies)} anomalies:")
    for item in anomalies:
        print(
            "- {program}: baseline={baseline} vm={vm}".format(
                program=item["program"],
                baseline=item["baseline"].get("status"),
                vm=item["vm"].get("status"),
            )
        )


def main(argv: Iterable[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-length",
        type=int,
        default=3,
        help="Maximum number of instructions per program.",
    )
    parser.add_argument(
        "--sample-size",
        type=int,
        default=40,
        help="Number of enumerated programs to evaluate.",
    )
    parser.add_argument(
        "--max-steps",
        type=int,
        default=64,
        help="Interpreter step budget before declaring UNKNOWN.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/halting/survey_summary.json"),
        help="Path for the JSON summary file.",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    summary = run_survey(args.max_length, args.sample_size, args.max_steps, args.output)
    _print_summary(summary)

    if summary.get("anomalies"):
        print("Halting survey detected disagreements; see summary for details.", file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
