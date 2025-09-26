"""Run live spike demonstrations for the Thiele Machine VM."""
from __future__ import annotations

import json
import math
import shutil
import textwrap
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional

from thielecpu.vm import VM
from thielecpu.state import State
from thielecpu.assemble import parse


OUTPUT_ROOT = Path("spike_demo_outputs")


@dataclass
class RunResult:
    name: str
    description: str
    output_dir: Path
    mu: float
    paradox: bool
    summary_path: Path
    ledger_path: Path
    trace_path: Path


# ---------------------------------------------------------------------------
# Helper utilities
# ---------------------------------------------------------------------------

def reset_output_root() -> None:
    if OUTPUT_ROOT.exists():
        shutil.rmtree(OUTPUT_ROOT)
    OUTPUT_ROOT.mkdir(parents=True, exist_ok=True)


def write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def format_json(data: Dict[str, float]) -> str:
    return json.dumps(data, indent=2, sort_keys=True)


def load_summary(output_dir: Path) -> Dict[str, object]:
    with (output_dir / "summary.json").open("r", encoding="utf-8") as fh:
        return json.load(fh)


def run_program(program_path: Path, output_dir: Path) -> RunResult:
    program_lines = program_path.read_text(encoding="utf-8").splitlines()
    program = parse(program_lines, program_path.parent)
    vm = VM(State())
    vm.run(program, output_dir)

    summary = load_summary(output_dir)
    ledger_path = output_dir / "mu_ledger.json"
    trace_path = output_dir / "trace.log"

    mu_value = summary.get("mu", float("nan"))
    if isinstance(mu_value, str):
        # Normalise legacy JSON infinities
        if mu_value.lower() in {"inf", "infinity", "+inf", "+infinity"}:
            mu_value = float("inf")
        elif mu_value.lower() in {"-inf", "-infinity"}:
            mu_value = float("-inf")
    paradox_flag = isinstance(mu_value, float) and math.isinf(mu_value)

    return RunResult(
        name=program_path.stem,
        description="",
        output_dir=output_dir,
        mu=mu_value,
        paradox=paradox_flag,
        summary_path=output_dir / "summary.json",
        ledger_path=ledger_path,
        trace_path=trace_path,
    )


def print_header(title: str) -> None:
    print("\n" + "=" * 80)
    print(title)
    print("=" * 80)


def print_divider(label: str) -> None:
    print("\n" + label)
    print("-" * len(label))


def mu_to_text(mu: float) -> str:
    if isinstance(mu, float) and math.isinf(mu):
        return "∞"
    if isinstance(mu, float):
        return f"{mu:.3f}" if not mu.is_integer() else f"{int(mu)}"
    return str(mu)


# ---------------------------------------------------------------------------
# Demonstration A: Glass Box AI Auditor
# ---------------------------------------------------------------------------


def build_ai_smt(data: Dict[str, float], smt_path: Path) -> None:
    lines = [
        "(set-logic QF_LRA)",
        "(declare-fun is_kitten () Real)",
        "(declare-fun is_dangerous () Real)",
        f"(assert (= is_kitten {data['is_kitten']}))",
        f"(assert (= is_dangerous {data['is_dangerous']}))",
        "(assert (=> (> is_kitten 0.9) (not (> is_dangerous 0.5))))",
    ]
    write_text(smt_path, "\n".join(lines) + "\n")


def create_pyexec_script(path: Path, lines: Iterable[str]) -> None:
    write_text(path, "\n".join(lines) + "\n")


def run_ai_case(case_dir: Path, ai_output: Dict[str, float], label: str) -> RunResult:
    print_divider(f"Case: {label}")
    print("AI model output:")
    print(textwrap.indent(format_json(ai_output), prefix="  "))

    py_path = case_dir / "emit_ai_output.py"
    create_pyexec_script(
        py_path,
        [
            "import json",
            f"data = {json.dumps(ai_output)}",
            "print(json.dumps(data, indent=2, sort_keys=True))",
        ],
    )

    smt_path = case_dir / "safety_policy.smt2"
    build_ai_smt(ai_output, smt_path)

    thm_path = case_dir / "program.thm"
    thm_content = textwrap.dedent(
        f""";
; Glass box AI audit — {label}
PNEW {{1,2,3}}
PYEXEC {py_path.name}
LASSERT {smt_path.name}
MDLACC
"""
    )
    write_text(thm_path, thm_content)

    output_dir = case_dir / "vm_output"
    result = run_program(thm_path, output_dir)

    summary = load_summary(output_dir)
    paradox_status = "True" if result.paradox else "False"
    print("Outcome:")
    print(f"  paradox_detected: {paradox_status}")
    print(f"  μ-bit cost: {mu_to_text(result.mu)}")
    print(f"  summary receipt: {result.summary_path}")
    print(f"  trace: {result.trace_path}")
    print(
        "Interpretation: "
        + (
            "The safety policy held — the Thiele Machine logged a clean audit."
            if not result.paradox
            else "Policy violation detected — the VM halted with a certified paradox."
        )
    )

    return result


def run_ai_auditor_demo() -> List[RunResult]:
    print_header("Demonstration A — Verifiable & Auditable AI (Glass Box)")
    print(
        "Goal: Use the Thiele VM to enforce a safety axiom on AI outputs and "
        "emit a paradox when the model violates policy."
    )

    demo_dir = OUTPUT_ROOT / "ai_auditor"
    demo_dir.mkdir(parents=True, exist_ok=True)

    safe_result = run_ai_case(
        demo_dir / "safe_case",
        {"id": "kitten_01", "is_kitten": 0.98, "is_dangerous": 0.01},
        "kitten_01 (expected to pass)",
    )

    unsafe_result = run_ai_case(
        demo_dir / "unsafe_case",
        {"id": "lion_cub_02", "is_kitten": 0.92, "is_dangerous": 0.85},
        "lion_cub_02 (expected paradox)",
    )

    print("\nSummary: The glass-box auditor accepts safe outputs and rejects paradoxical ones with a formal receipt.")
    return [safe_result, unsafe_result]


# ---------------------------------------------------------------------------
# Demonstration B: Universal Bug Finder
# ---------------------------------------------------------------------------


def build_bug_smt(x_value: int, smt_path: Path) -> None:
    lines = [
        "(set-logic QF_LIA)",
        "(declare-fun x () Int)",
        f"(assert (= x {x_value}))",
        "(assert (>= x 0))",
    ]
    write_text(smt_path, "\n".join(lines) + "\n")


def run_bug_case(case_dir: Path, x_value: int, label: str) -> RunResult:
    print_divider(f"Scenario: {label}")
    print(f"Caller prepares to invoke sqrt(x) with x = {x_value}.")

    py_path = case_dir / "caller_state.py"
    create_pyexec_script(
        py_path,
        [
            "x = {value}".format(value=x_value),
            "print(f'Preparing call: x = {x}')",
        ],
    )

    smt_path = case_dir / "safemath_axiom.smt2"
    build_bug_smt(x_value, smt_path)

    thm_path = case_dir / "program.thm"
    thm_content = textwrap.dedent(
        f""";
; Universal bug finder — {label}
PNEW {{10,11}}
PYEXEC {py_path.name}
LASSERT {smt_path.name}
MDLACC
"""
    )
    write_text(thm_path, thm_content)

    output_dir = case_dir / "vm_output"
    result = run_program(thm_path, output_dir)

    print("Outcome:")
    print(f"  paradox_detected: {'True' if result.paradox else 'False'}")
    print(f"  μ-bit cost: {mu_to_text(result.mu)}")
    print(f"  summary receipt: {result.summary_path}")
    print(f"  trace: {result.trace_path}")
    print(
        "Interpretation: "
        + (
            "Precondition satisfied — call permitted."
            if not result.paradox
            else "Precondition violated — the VM flags the bug before execution."
        )
    )

    return result


def run_bug_finder_demo() -> List[RunResult]:
    print_header("Demonstration B — Universal Bug Finder")
    print(
        "Goal: Treat a software bug as a logical paradox between caller state and library axioms,"
        " catching unsafe calls before they execute."
    )

    demo_dir = OUTPUT_ROOT / "bug_finder"
    demo_dir.mkdir(parents=True, exist_ok=True)

    safe_result = run_bug_case(demo_dir / "safe_call", 9, "Safe call (x = 9)")
    unsafe_result = run_bug_case(demo_dir / "buggy_call", -9, "Buggy call (x = -9)")

    print("\nSummary: The auditor lets safe calls proceed and halts paradoxical ones with an unsat certificate.")
    return [safe_result, unsafe_result]


# ---------------------------------------------------------------------------
# Demonstration C: Automated Scientist
# ---------------------------------------------------------------------------


def build_partition_smt(
    dataset: Dict[str, Dict[str, int]],
    group: Dict[str, object],
    smt_path: Path,
) -> None:
    label = group["label"]
    expected_color: Optional[int] = group.get("expected_color")  # type: ignore[assignment]
    point_names: List[str] = group["points"]  # type: ignore[assignment]

    lines: List[str] = ["(set-logic QF_LRA)"]
    idx = 0
    lines.extend(
        [
            f"; Linear model for {label}",
            f"(declare-fun a{idx} () Real)",
            f"(declare-fun b{idx} () Real)",
            f"(declare-fun c{idx} () Real)",
        ]
    )
    for name in point_names:
        pt = dataset[name]
        lines.append(
            f"(assert (= (+ (* {pt['K']} a{idx}) (* {pt['T']} b{idx}) c{idx}) {pt['W']}))"
        )
        if expected_color is not None:
            lines.append(f"(assert (= {pt['d']} {expected_color}))")
    write_text(smt_path, "\n".join(lines) + "\n")


def run_hypothesis(
    demo_dir: Path,
    dataset: Dict[str, Dict[str, int]],
    hypothesis: Dict[str, object],
    index: int,
) -> RunResult:
    name: str = hypothesis["name"]  # type: ignore[assignment]
    description: str = hypothesis["description"]  # type: ignore[assignment]
    groups: List[Dict[str, object]] = hypothesis["groups"]  # type: ignore[assignment]

    case_dir = demo_dir / f"{index:02d}_{name.lower().replace(' ', '_')}"
    case_dir.mkdir(parents=True, exist_ok=True)

    print_divider(f"Hypothesis {index}: {name}")
    print(description)

    py_lines = [
        "print('Testing partition:')",
    ]
    for group in groups:
        label = group["label"]  # type: ignore[assignment]
        pts = ", ".join(group["points"])  # type: ignore[assignment]
        expected_color = group.get("expected_color")
        if expected_color is None:
            py_lines.append(f"print('  - {label}: {{{pts}}}')")
        else:
            py_lines.append(
                f"print('  - {label}: {{{pts}}} (assume color d = {expected_color})')"
            )
    create_pyexec_script(case_dir / "describe_partition.py", py_lines)

    thm_lines = [
        "; Automated scientist hypothesis check",
        "PNEW {100,101,102,103}",
        "PYEXEC describe_partition.py",
    ]

    for group_index, group in enumerate(groups, start=1):
        smt_path = case_dir / f"group_{group_index}.smt2"
        build_partition_smt(dataset, group, smt_path)
        thm_lines.append(f"LASSERT {smt_path.name}")

    thm_lines.append("MDLACC")

    thm_path = case_dir / "program.thm"
    write_text(thm_path, "\n".join(thm_lines) + "\n")

    output_dir = case_dir / "vm_output"
    result = run_program(thm_path, output_dir)
    result.description = description

    status = "Validated" if not result.paradox else "Falsified"
    print(f"Result: {status}")
    print(f"  paradox_detected: {'True' if result.paradox else 'False'}")
    print(f"  μ-bit cost: {mu_to_text(result.mu)}")
    print(f"  summary receipt: {result.summary_path}")
    print(f"  trace: {result.trace_path}")

    return result


def run_auto_scientist_demo() -> List[RunResult]:
    print_header("Demonstration C — Automated Scientist")
    print(
        "Goal: Treat each scientific theory as a partition hypothesis, let the VM reject false theories via paradox, "
        "and measure the μ-bit cost of the surviving explanations."
    )

    dataset = {
        "A": {"K": 0, "d": 0, "T": 0, "W": 0},
        "B": {"K": 1, "d": 0, "T": 0, "W": 0},
        "C": {"K": 0, "d": 0, "T": 1, "W": 0},
        "D": {"K": 1, "d": 1, "T": 1, "W": 1},
    }

    print("Dataset (K, d, T -> W):")
    for name, pt in dataset.items():
        print(f"  Piece {name}: K={pt['K']}, color d={pt['d']}, T={pt['T']} -> W={pt['W']}")

    hypotheses: List[Dict[str, object]] = [
        {
            "name": "Null model",
            "description": "Assume one linear law fits all four data points.",
            "groups": [
                {"label": "All pieces", "points": ["A", "B", "C", "D"]},
            ],
        },
        {
            "name": "Mismatched partition",
            "description": "Guess the color split incorrectly: group 1 expects d=0, group 2 expects d=1 but includes point C.",
            "groups": [
                {"label": "Group 1", "points": ["A", "B"], "expected_color": 0},
                {"label": "Group 2", "points": ["C", "D"], "expected_color": 1},
            ],
        },
        {
            "name": "Sighted partition",
            "description": "Use the hidden color correctly: {A, B, C} with d=0 and {D} with d=1.",
            "groups": [
                {"label": "Color d=0", "points": ["A", "B", "C"], "expected_color": 0},
                {"label": "Color d=1", "points": ["D"], "expected_color": 1},
            ],
        },
    ]

    demo_dir = OUTPUT_ROOT / "auto_scientist"
    demo_dir.mkdir(parents=True, exist_ok=True)

    results: List[RunResult] = []
    for index, hypothesis in enumerate(hypotheses, start=1):
        result = run_hypothesis(demo_dir, dataset, hypothesis, index)
        results.append(result)

    print("\nFinal hypothesis summary:")
    header = f"{'Hypothesis':<24} | {'Status':<10} | {'μ-bit cost':<10} | Receipt"
    print(header)
    print("-" * len(header))
    for hypothesis, result in zip(hypotheses, results):
        status = "Validated" if not result.paradox else "Falsified"
        print(
            f"{hypothesis['name']:<24} | {status:<10} | {mu_to_text(result.mu):<10} | {result.summary_path}"
        )

    print(
        "\nObservation: Only the sighted partition survives without paradox, and its μ-bit ledger is finite."
        " The other hypotheses either contradict the data or mis-label the hidden color, producing UNSAT receipts."
    )

    return results


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------


def main() -> None:
    print("Thiele Machine Spike Demonstrations")
    print("This script generates fresh Thiele VM programs, executes them, and narrates the receipts.")
    reset_output_root()

    ai_results = run_ai_auditor_demo()
    bug_results = run_bug_finder_demo()
    scientist_results = run_auto_scientist_demo()

    print_header("All demonstrations complete")
    print("Artifacts saved under:", OUTPUT_ROOT.resolve())
    total_runs = len(ai_results) + len(bug_results) + len(scientist_results)
    paradoxes = sum(result.paradox for result in ai_results + bug_results + scientist_results)
    print(f"Executed {total_runs} VM runs; paradoxes detected: {paradoxes}.")
    print("Each summary.json and trace.log file provides the auditable receipt for its run.")


if __name__ == "__main__":
    main()
