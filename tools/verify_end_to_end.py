#!/usr/bin/env python3
"""Run the canonical Thiele Machine end-to-end verification workflow.

This harness is intended to be the single command reviewers execute to
validate the public tree.  By default it performs the following checks:

* Python unit test suite via ``pytest``
* Phase-three receipt/μ-ledger verification
* Core Coq build (``make -C coq core``)
* Halting boundary regression harness
* Bell/CHSH sandbox regeneration and validation
* Optional Yosys structural check and hardware simulation replay

Individual stages can be skipped with the dedicated ``--skip-*`` flags if a
reviewer needs a lighter pass, but a green run without skips is the baseline
signal that the repository is coherent."""
from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
from dataclasses import dataclass
import shutil
from typing import Iterable, List, Optional

RE_INSTR = re.compile(
    r"instr_memory\[(?P<idx>\d+)\] = \{8'h(?P<opc>[0-9a-fA-F]{2}),\s*8'h(?P<a>[0-9a-fA-F]{2}),\s*8'h(?P<b>[0-9a-fA-F]{2}),\s*8'h(?P<reserved>[0-9a-fA-F]{2})\};"
)

RE_LOG_METRIC = re.compile(
    r"\"partition_ops\":\s*(?P<partition>\d+),\s*\"mdl_ops\":\s*(?P<mdl>\d+),\s*\"info_gain\":\s*(?P<info>\d+)(?:,\s*\"mu(?:_total)?\":\s*(?P<mu>\d+))?"
)

RE_FIELD = re.compile(r"^(?P<label>Final PC|Status|Error):\s*(?P<value>[0-9a-fA-Fx]+)")

PROJECT_ROOT = pathlib.Path(__file__).resolve().parents[1]
HARDWARE_DIR = PROJECT_ROOT / "thielecpu" / "hardware"
TB_PATH = HARDWARE_DIR / "thiele_cpu_tb.v"
LOG_PATH = HARDWARE_DIR / "simulation_output.log"

OPCODE_PNEW = 0x00
OPCODE_PSPLIT = 0x01
OPCODE_PMERGE = 0x02
OPCODE_MDLACC = 0x05
OPCODE_XOR_ADD = 0x0B
OPCODE_XOR_SWAP = 0x0C
OPCODE_EMIT = 0x0E
OPCODE_HALT = 0xFF


@dataclass
class InstructionWord:
    index: int
    opcode: int
    operand_a: int
    operand_b: int


@dataclass
class Metrics:
    partition_ops: int
    mdl_ops: int
    info_gain: int
    mu_total: int


@dataclass
class ExecutionSummary:
    metrics: Metrics
    final_pc: int
    final_status: int
    final_error: int


def run_command(cmd: List[str], cwd: Optional[pathlib.Path] = None) -> None:
    subprocess.run(cmd, cwd=cwd, check=True)


def parse_instructions(path: pathlib.Path) -> List[InstructionWord]:
    entries: List[InstructionWord] = []
    seen: set[int] = set()
    for line in path.read_text().splitlines():
        match = RE_INSTR.search(line)
        if not match:
            continue
        idx = int(match.group("idx"))
        if idx in seen:
            raise RuntimeError(f"duplicate assignment for instr_memory[{idx}] in {path}")
        seen.add(idx)
        entries.append(
            InstructionWord(
                index=idx,
                opcode=int(match.group("opc"), 16),
                operand_a=int(match.group("a"), 16),
                operand_b=int(match.group("b"), 16),
            )
        )
    if not entries:
        raise RuntimeError(f"no instructions parsed from {path}")
    entries.sort(key=lambda inst: inst.index)
    return entries


def metrics_from_instructions(instrs: Iterable[InstructionWord]) -> Metrics:
    partition_ops = 0
    mdl_ops = 0
    info_gain = 0
    mu_total = 0
    for instr in instrs:
        opc = instr.opcode
        if opc in {OPCODE_PNEW, OPCODE_PSPLIT, OPCODE_PMERGE}:  # partition-mutating ops
            partition_ops += 1
        if opc == OPCODE_EMIT:
            info_gain += instr.operand_b
            # Note: mu_total comes from operand_cost (reserved byte), not operand_b
        if opc == OPCODE_MDLACC:
            mdl_ops += 1
    return Metrics(partition_ops=partition_ops, mdl_ops=mdl_ops, info_gain=info_gain, mu_total=mu_total)


def summary_from_log(path: pathlib.Path) -> ExecutionSummary:
    text = path.read_text()
    metrics_match = RE_LOG_METRIC.search(text)
    if metrics_match is None:
        raise RuntimeError(f"unable to find metrics in {path}")
    lines = text.splitlines()
    mu_total_value = int(metrics_match.group("mu")) if metrics_match.group("mu") else int(metrics_match.group("info"))
    metrics = Metrics(
        partition_ops=int(metrics_match.group("partition")),
        mdl_ops=int(metrics_match.group("mdl")),
        info_gain=int(metrics_match.group("info")),
        mu_total=mu_total_value,
    )

    final_pc = _parse_last_hex_field(lines, "Final PC")
    final_status = _parse_last_hex_field(lines, "Status")
    final_error = _parse_last_hex_field(lines, "Error")

    if final_pc is None or final_status is None or final_error is None:
        raise RuntimeError(f"unable to extract final state summary from {path}")

    return ExecutionSummary(metrics=metrics, final_pc=final_pc, final_status=final_status, final_error=final_error)


def _parse_last_hex_field(lines: List[str], label: str) -> int | None:
    for line in reversed(lines):
        match = RE_FIELD.match(line.strip())
        if match and match.group("label") == label:
            value = match.group("value")
            value = value.lower().removeprefix("0x")
            return int(value, 16)
    return None


def expected_final_pc(instrs: List[InstructionWord]) -> int:
    if not instrs:
        return 0
    for instr in instrs:
        if instr.opcode == OPCODE_HALT:
            # RTL testbench captures PC when HALT is being executed (before increment).
            # So final PC points AT the HALT instruction, not after it.
            return instr.index * 4
    # Default: assume the program runs through the highest-indexed instruction we saw.
    return instrs[-1].index * 4


def verify_metrics(expected: Metrics, observed: Metrics) -> None:
    mismatches = []
    if expected.partition_ops != observed.partition_ops:
        mismatches.append(f"partition_ops expected {expected.partition_ops} != {observed.partition_ops}")
    if expected.mdl_ops != observed.mdl_ops:
        mismatches.append(f"mdl_ops expected {expected.mdl_ops} != {observed.mdl_ops}")
    if expected.info_gain != observed.info_gain:
        mismatches.append(f"info_gain expected {expected.info_gain} != {observed.info_gain}")
    if expected.mu_total != observed.mu_total:
        mismatches.append(f"mu_total expected {expected.mu_total} != {observed.mu_total}")
    if mismatches:
        raise RuntimeError("Metric mismatch:\n" + "\n".join(mismatches))


def verify_final_state(instrs: List[InstructionWord], summary: ExecutionSummary) -> None:
    expected_pc = expected_final_pc(instrs)
    if summary.final_pc != expected_pc:
        raise RuntimeError(
            "Final PC mismatch: expected 0x{expected:08x} from HALT index, observed 0x{observed:08x}".format(
                expected=expected_pc, observed=summary.final_pc
            )
        )
    if summary.final_error not in {0, 1}:
        raise RuntimeError(f"Unexpected final error flag {summary.final_error:#x}; expected 0x0 or 0x1")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--skip-pytests",
        action="store_true",
        help="Skip running the Python unit test suite (pytest).",
    )
    parser.add_argument(
        "--skip-receipts",
        action="store_true",
        help="Skip the phase-three proofpack / receipt verification.",
    )
    parser.add_argument("--skip-build", action="store_true", help="Skip the Coq core build step.")
    parser.add_argument("--skip-hardware", action="store_true", help="Skip running the hardware simulation test suite.")
    parser.add_argument(
        "--skip-yosys", action="store_true", help="Skip the structural Yosys elaboration check."
    )
    parser.add_argument(
        "--skip-halting",
        action="store_true",
        help="Skip the halting baseline vs VM regression checks.",
    )
    parser.add_argument(
        "--skip-bell",
        action="store_true",
        help="Skip the Bell / CHSH workflow regeneration.",
    )
    args = parser.parse_args()

    if not args.skip_pytests:
        run_command(["pytest", "-q"], cwd=PROJECT_ROOT)

    if not args.skip_receipts:
        proofpack_tar = PROJECT_ROOT / "artifacts" / "phase_three" / "phase_three_proofpack.tar.gz"
        proofpack_dir = PROJECT_ROOT / "artifacts" / "phase_three" / "phase_three_bundle"
        proofpack_arg: Optional[pathlib.Path] = None

        if proofpack_tar.exists():
            proofpack_arg = proofpack_tar
        elif proofpack_dir.exists():
            proofpack_arg = proofpack_dir
        else:
            print(
                "Phase-three proofpack artifacts not found; skipping receipt verification."
            )

        if proofpack_arg is not None:
            run_command(
                [
                    "python3",
                    str(PROJECT_ROOT / "tools" / "verify_phase_three_proofpack.py"),
                    str(proofpack_arg),
                ]
            )

    if not args.skip_build:
        run_command(["make", "-C", str(PROJECT_ROOT / "coq"), "core"])

    if not args.skip_halting:
        run_command(["python3", str(PROJECT_ROOT / "tools" / "verify_halting_boundary.py")])

    if not args.skip_bell:
        run_command(["python3", str(PROJECT_ROOT / "tools" / "verify_bell_workflow.py")])

    if not args.skip_yosys:
        run_yosys_check()

    if not args.skip_hardware:
        run_command(["python3", str(HARDWARE_DIR / "test_hardware.py")])

        instrs = parse_instructions(TB_PATH)
        expected = metrics_from_instructions(instrs)
        summary = summary_from_log(LOG_PATH)
        verify_metrics(expected, summary.metrics)
        verify_final_state(instrs, summary)

        print("All components agree:")
        print(f"  Partition ops : {summary.metrics.partition_ops}")
        print(f"  MDL ops       : {summary.metrics.mdl_ops}")
        print(f"  Info gain     : {summary.metrics.info_gain}")
        print(f"  μ-total       : {summary.metrics.mu_total}")
        print(f"  Final PC      : 0x{summary.final_pc:08x}")
        print(f"  Final status  : 0x{summary.final_status:08x}")
        print(f"  Final error   : 0x{summary.final_error:08x}")
    else:
        print("Hardware simulation skipped; instruction and log checks suppressed.")


def run_yosys_check() -> None:
    if shutil.which("yosys") is None:
        raise RuntimeError(
            "yosys executable not found in PATH; install yosys or rerun with --skip-yosys"
        )

    script = " ; ".join(
        [
            "read_verilog -sv -DYOSYS_LITE thiele_cpu.v",
            "hierarchy -check -top thiele_cpu",
        ]
    )

    run_command(["yosys", "-q", "-p", script], cwd=HARDWARE_DIR)


if __name__ == "__main__":
    main()
