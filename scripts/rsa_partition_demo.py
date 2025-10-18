# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Three-act RSA partition demonstration for the Thiele Machine VM.

The demo now stages the factoring transcript as a progression:

* **Act I – The Blind Worker.**  The VM is intentionally blinded and runs a
  sequential trial-division loop, mirroring a single-tape Turing machine.
* **Act II – The Blind Factory.**  The VM partitions the workload to emulate a
  modern multi-core CPU.  The tasks run in parallel, but the system still lacks
  any awareness of the global search space.
* **Act III – The Sighted Detective Agency.**  The VM first proves—via an SMT
  reasoning step—that its partition map covers the entire √n region.  Only after
  that μ-bit transaction succeeds does it execute the partition-native search
  and emit the silicon scaling analysis.

Each act produces receipts in its own sub-directory under ``rsa_demo_output``.
The script also compiles a consolidated ``analysis_report.json`` at the top
level for auditors who need a single artifact describing the witness, μ-ledger,
partition inventory, and hardware scaling deltas.
"""

from __future__ import annotations

import json
import math
import os
from pathlib import Path
import re
import textwrap
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from thielecpu.assemble import parse
from thielecpu.state import State
from thielecpu.vm import VM


ACT_I_SCRIPT = Path("temp_rsa_act_i.py")
SETUP_SCRIPT = Path("temp_rsa_setup.py")
ANALYSIS_SCRIPT = Path("temp_rsa_analysis.py")
COMPOSITION_SCRIPT = Path("temp_rsa_compose.py")
REASONING_SCRIPT = Path("temp_rsa_reasoning.py")


class RunArtifacts:
    """Structured summary extracted from a VM run."""

    def __init__(
        self,
        witness: Optional[Tuple[int, int]],
        mu_total: Optional[float],
        candidate_checks: int,
        highlight_lines: Sequence[str],
        reasoning_lines: Sequence[str],
        hardware_lines: Sequence[str],
    ) -> None:
        self.witness = witness
        self.mu_total = mu_total
        self.candidate_checks = candidate_checks
        self.highlight_lines = list(highlight_lines)
        self.reasoning_lines = list(reasoning_lines)
        self.hardware_lines = list(hardware_lines)


def _int_range_for_modulus(n: int) -> List[int]:
    sqrt_bound = int(math.isqrt(n))
    return list(range(2, max(2, sqrt_bound) + 1))


def _chunk(values: Sequence[int], chunk_size: int) -> List[List[int]]:
    bucket: List[List[int]] = []
    current: List[int] = []
    for value in values:
        current.append(value)
        if len(current) == chunk_size:
            bucket.append(current)
            current = []
    if current:
        bucket.append(current)
    return bucket


def _partition_search_space(n: int) -> Dict[str, List[int]]:
    """Return a labelled partition map covering the entire √n interval."""

    candidates = _int_range_for_modulus(n)
    if not candidates:
        return {"A": [2]}

    desired_partitions = min(8, max(2, len(candidates) // 10 or 1))
    chunk_size = max(1, math.ceil(len(candidates) / desired_partitions))
    chunks = _chunk(candidates, chunk_size)

    partitions: Dict[str, List[int]] = {}
    for index, chunk in enumerate(chunks):
        label = chr(ord("A") + index)
        partitions[label] = chunk

    if len(partitions) == 1:
        only_label = next(iter(partitions))
        values = partitions[only_label]
        midpoint = len(values) // 2 or 1
        partitions[only_label] = values[:midpoint]
        partitions[chr(ord(only_label) + 1)] = values[midpoint:] or values[:1]

    return partitions


def _analysis_summary(
    n: int, partitions: Dict[str, List[int]], analysis_bits: Iterable[int]
) -> Dict[str, object]:
    partition_labels = list(partitions.keys())
    partition_count = len(partition_labels)
    candidate_counts = {label: len(partitions[label]) for label in partition_labels}
    total_candidates = sum(candidate_counts.values())
    per_partition_max = max(candidate_counts.values()) if candidate_counts else 0
    sqrt_bound = int(math.isqrt(n))
    work_per_partition = (
        (total_candidates + max(1, partition_count) - 1) // max(1, partition_count)
        if partition_count
        else 0
    )

    analysis_rows = []
    for bits in analysis_bits:
        classical_log2 = bits / 2
        classical_log10 = classical_log2 * math.log10(2)
        classical_digits = max(1, int(math.floor(classical_log10)) + 1)

        if partition_count > 0:
            per_partition_log10 = classical_log10 - math.log10(partition_count)
        else:
            per_partition_log10 = classical_log10
        per_partition_digits = max(1, int(math.floor(per_partition_log10)) + 1)

        analysis_rows.append(
            {
                "bits": bits,
                "classical_checks_log2": classical_log2,
                "classical_checks_log10": classical_log10,
                "classical_checks_digits": classical_digits,
                "per_partition_checks_log10": per_partition_log10,
                "per_partition_checks_digits": per_partition_digits,
                "constant_depth_stages": 2,
                "orders_of_magnitude_reduced": classical_log10 - per_partition_log10,
            }
        )

    return {
        "modulus": n,
        "bit_length": n.bit_length(),
        "sqrt_bound": sqrt_bound,
        "partition_count": partition_count,
        "candidate_counts": candidate_counts,
        "total_candidates": total_candidates,
        "max_candidates_per_partition": per_partition_max,
        "work_per_partition": work_per_partition,
        "analysis_rows": analysis_rows,
    }


def _write_temp_script(path: Path, contents: str) -> None:
    path.write_text(contents + "\n", encoding="utf-8")


def _render_act_i_script(n: int) -> str:
    sqrt_bound = int(math.isqrt(n))
    return textwrap.dedent(
        f"""
        TARGET = {n}
        SQRT_BOUND = {sqrt_bound}
        print("Trial division range:", list(range(2, SQRT_BOUND + 1)))
        factor = None
        cofactor = None
        for candidate in range(2, SQRT_BOUND + 1):
            remainder = TARGET % candidate
            print("Testing", candidate, "→ remainder", remainder)
            if remainder == 0:
                factor = candidate
                cofactor = TARGET // candidate
                print("Witness located (sequential mode):", factor, "*", cofactor, "=", TARGET)
                break
        if factor is None:
            print("Sequential search failed to locate a witness")
            __result__ = None
        else:
            __result__ = (factor, cofactor)
        """
    ).strip()


def _render_partition_setup_script(
    n: int,
    partitions: Dict[str, List[int]],
    heading: str,
    descriptor: str,
) -> str:
    return textwrap.dedent(
        f"""
        TARGET = {n}
        PARTITIONS = {json.dumps(partitions)}
        PARTITION_RESULTS = dict((label, None) for label in PARTITIONS)
        print("{heading}")
        print("Target modulus:", TARGET)
        for label, numbers in PARTITIONS.items():
            print(f"Partition {{label}} {descriptor}: {{numbers}}")
        """
    ).strip()


def _render_partition_worker_script(label: str, descriptor: str) -> str:
    return textwrap.dedent(
        f"""
        numbers = PARTITIONS[{label!r}]
        print("Exploring Partition {label} {descriptor}:", numbers)
        found = None
        for candidate in numbers:
            remainder = TARGET % candidate
            print("Testing", candidate, "→ remainder", remainder)
            if remainder == 0:
                cofactor = TARGET // candidate
                found = {{"factor": candidate, "cofactor": cofactor}}
                print(
                    "Witness located in Partition {label}:",
                    candidate,
                    "*",
                    cofactor,
                    "=",
                    TARGET,
                )
                break
        if found is None:
            print("Partition {label} produced no witness.")
        PARTITION_RESULTS[{label!r}] = found
        __result__ = found
        """
    ).strip()


def _render_composition_script() -> str:
    return textwrap.dedent(
        """
        witness = None
        for value in PARTITION_RESULTS.values():
            if value:
                witness = value
                break
        if witness is not None:
            factor = witness["factor"]
            cofactor = witness["cofactor"]
            print("Composing final witness from partition search")
            print("Verification:", factor, "*", cofactor, "=", TARGET)
            __result__ = (factor, cofactor)
        else:
            print("No witness available; factoring failed.")
            __result__ = None
        """
    ).strip()


def _render_reasoning_script(
    partitions: Dict[str, List[int]], sqrt_bound: int
) -> str:
    coverage_values = sorted(
        {value for values in partitions.values() for value in values}
    )
    script = f"""
import z3

PARTITIONS = {json.dumps(partitions)}
COVERAGE_VALUES = {coverage_values}
SQRT_BOUND = {sqrt_bound}

solver = z3.Solver()
candidate = z3.Int("candidate")
solver.add(candidate >= 2)
solver.add(candidate <= SQRT_BOUND)
for value in COVERAGE_VALUES:
    solver.add(candidate != value)

print(
    "Reasoning step: attempting to witness any uncovered divisor in the",
    f"range [2, {{SQRT_BOUND}}]",
)
result = solver.check()
if result == z3.sat:
    model = solver.model()
    witness_cell = model[candidate]
    uncovered = witness_cell.as_long()
    print(
        "Reasoning failure: uncovered candidate survives the SMT search",
        uncovered,
    )
    __result__ = {{"status": "failure", "uncovered": uncovered}}
elif result == z3.unsat:
    print(
        "Reasoning success: the SMT solver certified the partition map",
        "covers all divisors in the √n search region. μ-bits were",
        "expended to lock this guarantee before executing the partitions.",
    )
    __result__ = {{"status": "success", "coverage": [2, SQRT_BOUND]}}
else:
    print("Reasoning inconclusive: solver returned", result)
    __result__ = {{"status": "unknown", "solver_result": str(result)}}
"""
    return textwrap.dedent(script).strip()


def _render_analysis_script(analysis_summary: Dict[str, object]) -> str:
    scaling_rows_literal = json.dumps(analysis_summary["analysis_rows"])
    return textwrap.dedent(
        f"""
        target = TARGET
        scaling_rows = {scaling_rows_literal}

        print("Hardware scaling assessment (inside VM):")
        print("  √n search bound:", {analysis_summary['sqrt_bound']})
        print("  Partition count:", {analysis_summary['partition_count']})
        print("  Total candidates tracked:", {analysis_summary['total_candidates']})
        print(
            "  Work per partition stage:",
            {analysis_summary['work_per_partition']},
        )

        for row in scaling_rows:
            bits = row["bits"]
            classical_digits = row["classical_checks_digits"] - 1
            per_partition_digits = row["per_partition_checks_digits"] - 1
            orders_str = "%.2f" % (row["orders_of_magnitude_reduced"],)
            template = (
                "  RSA-{{bits}}: classical √n search ≈ 10^{{classical}} checks; "
                "partition-native silicon load drops to ~10^{{per_partition}} candidates per module "
                "(Δ ≈ {{orders}} orders; constant-depth {{stages}}-stage composition)"
            )
            message = template.format(
                bits=bits,
                classical=classical_digits,
                per_partition=per_partition_digits,
                orders=orders_str,
                stages=row["constant_depth_stages"],
            )
            print(message)
        """
    ).strip()


def _run_vm_program(
    program_lines: Sequence[str],
    temp_scripts: Sequence[Path],
    output_dir: Path,
) -> RunArtifacts:
    output_dir.mkdir(parents=True, exist_ok=True)
    program_source = "\n".join(program_lines)
    program_path = output_dir.with_suffix(".thm")
    program_path.write_text(program_source, encoding="utf-8")

    try:
        program = parse(program_source.splitlines(), Path("."))
        vm = VM(State())
        vm.run(program, output_dir)
    finally:
        program_path.unlink(missing_ok=True)
        for script in temp_scripts:
            script.unlink(missing_ok=True)

    summary_path = output_dir / "summary.json"
    mu_total: Optional[float] = None
    if summary_path.exists():
        summary = json.loads(summary_path.read_text())
        mu_total = summary.get("mu_total")

    trace_path = output_dir / "trace.log"
    highlight_lines: List[str] = []
    reasoning_lines: List[str] = []
    hardware_lines: List[str] = []
    candidate_checks = 0
    witness: Optional[Tuple[int, int]] = None

    if trace_path.exists():
        trace_lines = trace_path.read_text().splitlines()
        for line in trace_lines:
            if "Testing" in line:
                candidate_checks += 1
            if "Reasoning" in line:
                reasoning_lines.append(line)
            if "Hardware scaling" in line or "RSA-" in line:
                hardware_lines.append(line)
            if "Witness located" in line or "Composing final witness" in line:
                highlight_lines.append(line)
                message = line.split("PYEXEC output:", 1)[-1]
                match = re.search(r":\s*(\d+)\s*\*\s*(\d+)\s*=\s*(\d+)", message)
                if match:
                    factor = int(match.group(1))
                    cofactor = int(match.group(2))
                    witness = (factor, cofactor)

    return RunArtifacts(
        witness=witness,
        mu_total=mu_total,
        candidate_checks=candidate_checks,
        highlight_lines=highlight_lines,
        reasoning_lines=reasoning_lines,
        hardware_lines=hardware_lines,
    )


def _act_i_program(n: int) -> Tuple[List[str], List[Path]]:
    script_source = _render_act_i_script(n)
    _write_temp_script(ACT_I_SCRIPT, script_source)
    program_lines = [
        "; Act I: Sequential trial division (blind worker)",
        "PNEW 0",
        f'PYEXEC "{ACT_I_SCRIPT.name}"',
        "MDLACC",
        'EMIT "Act I complete"',
    ]
    return program_lines, [ACT_I_SCRIPT]


def _act_ii_program(
    n: int, partitions: Dict[str, List[int]]
) -> Tuple[List[str], List[Path]]:
    temp_scripts: List[Path] = []
    setup_code = _render_partition_setup_script(
        n,
        partitions,
        heading="Configuring blind multi-core emulation (Act II)",
        descriptor="task queue",
    )
    _write_temp_script(SETUP_SCRIPT, setup_code)
    temp_scripts.append(SETUP_SCRIPT)

    for label in partitions:
        worker_script = _render_partition_worker_script(label, "task queue")
        path = Path(f"temp_rsa_partition_{label.lower()}.py")
        _write_temp_script(path, worker_script)
        temp_scripts.append(path)

    composition_script = _render_composition_script()
    _write_temp_script(COMPOSITION_SCRIPT, composition_script)
    temp_scripts.append(COMPOSITION_SCRIPT)

    program_lines = [
        "; Act II: Blind factory (partitioned tasks)",
        "PNEW 0",
        f'PYEXEC "{SETUP_SCRIPT.name}"',
    ]
    for label in partitions:
        program_lines.append(f'PYEXEC "temp_rsa_partition_{label.lower()}.py"')
    program_lines.extend(
        [
            f'PYEXEC "{COMPOSITION_SCRIPT.name}"',
            "MDLACC",
            'EMIT "Act II complete"',
        ]
    )
    return program_lines, temp_scripts


def _act_iii_program(
    n: int,
    partitions: Dict[str, List[int]],
    analysis_bits: Iterable[int],
) -> Tuple[List[str], List[Path], Dict[str, object]]:
    temp_scripts: List[Path] = []
    sqrt_bound = int(math.isqrt(n))

    setup_code = _render_partition_setup_script(
        n,
        partitions,
        heading="Configuring sighted Thiele partition map (Act III)",
        descriptor="search frontier",
    )
    _write_temp_script(SETUP_SCRIPT, setup_code)
    temp_scripts.append(SETUP_SCRIPT)

    reasoning_code = _render_reasoning_script(partitions, sqrt_bound)
    _write_temp_script(REASONING_SCRIPT, reasoning_code)
    temp_scripts.append(REASONING_SCRIPT)

    for label in partitions:
        worker_script = _render_partition_worker_script(label, "search frontier")
        path = Path(f"temp_rsa_partition_{label.lower()}.py")
        _write_temp_script(path, worker_script)
        temp_scripts.append(path)

    composition_script = _render_composition_script()
    _write_temp_script(COMPOSITION_SCRIPT, composition_script)
    temp_scripts.append(COMPOSITION_SCRIPT)

    analysis_summary = _analysis_summary(n, partitions, analysis_bits)
    analysis_code = _render_analysis_script(analysis_summary)
    _write_temp_script(ANALYSIS_SCRIPT, analysis_code)
    temp_scripts.append(ANALYSIS_SCRIPT)

    program_lines = [
        "; Act III: Sighted Thiele Machine",
        "PNEW 0",
        f'PYEXEC "{SETUP_SCRIPT.name}"',
        f'PYEXEC "{REASONING_SCRIPT.name}"',
    ]
    for label in partitions:
        program_lines.append(f'PYEXEC "temp_rsa_partition_{label.lower()}.py"')
    program_lines.extend(
        [
            f'PYEXEC "{COMPOSITION_SCRIPT.name}"',
            f'PYEXEC "{ANALYSIS_SCRIPT.name}"',
            "MDLACC",
            'EMIT "Act III complete"',
        ]
    )
    return program_lines, temp_scripts, analysis_summary


def run_partition_based_rsa_demo(n: int, analysis_bits: Iterable[int]) -> None:
    analysis_bits = list(analysis_bits)
    partitions = _partition_search_space(n)
    sqrt_bound = int(math.isqrt(n))

    print("Thiele Machine: Three-Act RSA Factorisation Demonstration")
    print("=" * 72)
    print(f"Target RSA modulus: {n}")
    print(f"Bit length: {n.bit_length()} bits")
    print(f"√n search bound: {sqrt_bound}")

    output_root = Path("rsa_demo_output")
    output_root.mkdir(exist_ok=True)

    # Act I – Sequential trial division
    print("\n--- ACT I: The Blind Worker (Turing Machine Emulation) ---")
    print(
        "The VM is intentionally blinded to a single instruction stream. It"
        " mirrors a Turing machine performing naive trial division.",
    )
    act_i_program, act_i_scripts = _act_i_program(n)
    act_i_dir = output_root / "act_i"
    act_i_result = _run_vm_program(act_i_program, act_i_scripts, act_i_dir)
    print(f"Candidate checks executed: {act_i_result.candidate_checks}")
    if act_i_result.witness:
        factor, cofactor = act_i_result.witness
        print(f"Witness recovered sequentially: {factor} × {cofactor} = {n}")
    if act_i_result.mu_total is not None:
        print(f"μ-total recorded by VM: {act_i_result.mu_total}")

    # Act II – Partitioned tasks without reasoning
    print("\n--- ACT II: The Blind Factory (Modern CPU Emulation) ---")
    print(
        "Partitions emulate a modern multi-core CPU. Each worker blindly"
        " handles a slice of the search without understanding the overall"
        " structure.",
    )
    act_ii_program, act_ii_scripts = _act_ii_program(n, partitions)
    act_ii_dir = output_root / "act_ii"
    act_ii_result = _run_vm_program(act_ii_program, act_ii_scripts, act_ii_dir)
    print(
        "Task-level parallelism executed candidate checks across",
        f"{len(partitions)} partitions (total checks: {act_ii_result.candidate_checks}).",
    )
    if act_ii_result.highlight_lines:
        print("Trace highlights:")
        for line in act_ii_result.highlight_lines:
            print("  " + line)
    if act_ii_result.mu_total is not None:
        print(f"μ-total recorded by VM: {act_ii_result.mu_total}")

    # Act III – Sighted reasoning followed by partition execution
    print("\n--- ACT III: The Sighted Detective Agency (Thiele Machine Unleashed) ---")
    print(
        "Before any partition executes, the VM spends μ-bits to prove—using",
        " an SMT solver—that the partition map covers the entire √n frontier.",
    )
    (
        act_iii_program,
        act_iii_scripts,
        analysis_summary,
    ) = _act_iii_program(n, partitions, analysis_bits)
    act_iii_dir = output_root / "act_iii"
    act_iii_result = _run_vm_program(act_iii_program, act_iii_scripts, act_iii_dir)

    if act_iii_result.reasoning_lines:
        print("Reasoning transcript:")
        for line in act_iii_result.reasoning_lines:
            print("  " + line)
    else:
        print("Reasoning transcript: (no lines captured; inspect trace.log)")

    if act_iii_result.highlight_lines:
        print("Partition search transcript:")
        for line in act_iii_result.highlight_lines:
            print("  " + line)
    if act_iii_result.mu_total is not None:
        print(f"μ-total recorded by VM: {act_iii_result.mu_total}")

    print("\nHardware scaling report (Act III conclusion):")
    for row in analysis_summary["analysis_rows"]:
        bits = row["bits"]
        classical_digits = row["classical_checks_digits"]
        per_partition_digits = row["per_partition_checks_digits"]
        orders = row["orders_of_magnitude_reduced"]
        print(
            f"  RSA-{bits}: classical √n search ≈ 10^{classical_digits - 1} checks;"
            f" Thiele partitions drop to ~10^{per_partition_digits - 1} per module"
            f" (Δ ≈ {orders:.2f} orders, constant-depth"
            f" {row['constant_depth_stages']} stages)",
        )

    if act_iii_result.hardware_lines:
        print("VM-recorded hardware narrative:")
        for line in act_iii_result.hardware_lines:
            print("  " + line)

    # Consolidated analysis report
    analysis_report = dict(analysis_summary)
    analysis_report["partitions"] = partitions
    if act_iii_result.witness:
        factor, cofactor = act_iii_result.witness
        analysis_report["witness"] = {
            "factor": factor,
            "cofactor": cofactor,
        }
    else:
        analysis_report["witness"] = None

    analysis_report["acts"] = {
        "act_i": {
            "candidate_checks": act_i_result.candidate_checks,
            "mu_total": act_i_result.mu_total,
            "witness": act_i_result.witness,
        },
        "act_ii": {
            "candidate_checks": act_ii_result.candidate_checks,
            "mu_total": act_ii_result.mu_total,
            "witness": act_ii_result.witness,
        },
        "act_iii": {
            "candidate_checks": act_iii_result.candidate_checks,
            "mu_total": act_iii_result.mu_total,
            "witness": act_iii_result.witness,
            "reasoning_success": any(
                "Reasoning success" in line for line in act_iii_result.reasoning_lines
            ),
        },
    }

    analysis_path = output_root / "analysis_report.json"
    analysis_path.write_text(json.dumps(analysis_report, indent=2), encoding="utf-8")
    print(f"\nAnalysis report written to {analysis_path}")

    if act_iii_result.witness:
        factor, cofactor = act_iii_result.witness
        print(f"\n[SUCCESS] Factored {n} = {factor} × {cofactor}")
    else:
        print(f"\n[FAIL] Act III failed to recover a witness for {n}")


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(
        description="Three-act RSA factorisation demo on the Thiele VM"
    )
    parser.add_argument(
        "--modulus",
        "--n",
        type=int,
        default=10403,
        help="RSA modulus to factor (should have tractable factors for the demo)",
    )
    parser.add_argument(
        "--analysis-bits",
        nargs="+",
        type=int,
        default=[256, 512, 1024, 2048, 4096],
        help=(
            "Bit lengths to include in the hardware scaling projection for Act III"
        ),
    )
    args = parser.parse_args()

    run_partition_based_rsa_demo(args.modulus, args.analysis_bits)


if __name__ == "__main__":
    main()
