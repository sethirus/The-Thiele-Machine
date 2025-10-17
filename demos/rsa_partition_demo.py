# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Partition-native RSA factorisation demonstration for the Thiele Machine."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
from typing import Dict, List, Optional, Tuple

import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from thielecpu.assemble import parse
from thielecpu.state import State
from thielecpu.vm import VM


SETUP_SCRIPT = Path("temp_rsa_setup.py")
PARTITION_A_SCRIPT = Path("temp_rsa_partition_a.py")
PARTITION_B_SCRIPT = Path("temp_rsa_partition_b.py")
COMPOSITION_SCRIPT = Path("temp_rsa_compose.py")


def _write_partition_scripts(n: int) -> List[Path]:
    setup_code = f"""
TARGET = {n}
PARTITIONS = {{
    "A": [2, 3, 5, 7],
    "B": [11, 13]
}}
PARTITION_RESULTS = {{"A": None, "B": None}}
print("Partitioning search space for n =", TARGET)
print("Partition A:", PARTITIONS["A"])
print("Partition B:", PARTITIONS["B"])
""".strip()

    partition_a_code = """
numbers = PARTITIONS["A"]
print("Exploring Partition A:", numbers)
found = None
for candidate in numbers:
    remainder = TARGET % candidate
    print("Testing", candidate, "→ remainder", remainder)
    if remainder == 0:
        cofactor = TARGET // candidate
        found = {"factor": candidate, "cofactor": cofactor}
        print("Witness located in Partition A:", candidate, "*", cofactor, "=", TARGET)
        break
if found is None:
    print("Partition A produced no witness.")
PARTITION_RESULTS["A"] = found
__result__ = found
""".strip()

    partition_b_code = """
numbers = PARTITIONS["B"]
print("Exploring Partition B:", numbers)
found = None
for candidate in numbers:
    remainder = TARGET % candidate
    print("Testing", candidate, "→ remainder", remainder)
    if remainder == 0:
        cofactor = TARGET // candidate
        found = {"factor": candidate, "cofactor": cofactor}
        print("Unexpected witness located in Partition B:", candidate, "*", cofactor, "=", TARGET)
        break
if found is None:
    print("Partition B produced no witness; search exhausted.")
PARTITION_RESULTS["B"] = found
__result__ = found
""".strip()

    composition_code = """
witness = PARTITION_RESULTS["A"]
if witness is not None:
    factor = witness["factor"]
    cofactor = witness["cofactor"]
    print("Composing final witness from Partition A")
    print("Verification:", factor, "*", cofactor, "=", TARGET)
    __result__ = (factor, cofactor)
else:
    print("No witness available; factoring failed.")
    __result__ = None
""".strip()

    scripts = [
        (SETUP_SCRIPT, setup_code),
        (PARTITION_A_SCRIPT, partition_a_code),
        (PARTITION_B_SCRIPT, partition_b_code),
        (COMPOSITION_SCRIPT, composition_code),
    ]

    written = []
    for path, contents in scripts:
        path.write_text(contents + "\n", encoding="utf-8")
        written.append(path)
    return written


def create_partition_based_factoring_program(n: int) -> Tuple[str, List[Path]]:
    """Create the Thiele program and supporting PYEXEC scripts."""

    scripts = _write_partition_scripts(n)
    program_lines = [
        "; Partition-Based RSA Factorisation",
        f"; Target modulus: {n}",
        "PNEW 0",
        f'PYEXEC "{SETUP_SCRIPT.name}"',
        f'PYEXEC "{PARTITION_A_SCRIPT.name}"',
        f'PYEXEC "{PARTITION_B_SCRIPT.name}"',
        f'PYEXEC "{COMPOSITION_SCRIPT.name}"',
        "MDLACC",
        'EMIT "RSA factorisation completed via partition-native computation"',
    ]
    return "\n".join(program_lines), scripts


def run_partition_based_rsa_demo(n: int) -> None:
    """Execute the partition-based RSA factorisation demo."""

    print("Thiele Machine: Partition-Based RSA Factorisation Demonstration")
    print("=" * 60)
    print(f"Target RSA modulus: {n}")
    print(f"Bit length: {n.bit_length()} bits")
    print()

    program_source, temp_scripts = create_partition_based_factoring_program(n)
    program_path = Path("temp_rsa_partition.thm")
    program_path.write_text(program_source, encoding="utf-8")

    try:
        program = parse(program_source.splitlines(), Path("."))
        vm = VM(State())
        output_dir = Path("rsa_demo_output")
        vm.run(program, output_dir)

        summary_path = output_dir / "summary.json"
        if summary_path.exists():
            summary = json.loads(summary_path.read_text())
            print("\nMu-bit accounting:")
            print(json.dumps(summary, indent=2))

        trace_path = output_dir / "trace.log"
        found_witness: Optional[Tuple[int, int]] = None
        if trace_path.exists():
            trace_lines = trace_path.read_text().splitlines()
            print("\nExecution trace highlights:")
            for line in trace_lines:
                if "Witness located in Partition A" in line:
                    print("  " + line)
                    message = line.split("PYEXEC output:", 1)[-1]
                    match = re.search(r":\s*(\d+)\s*\*\s*(\d+)\s*=\s*(\d+)", message)
                    if match:
                        factor = int(match.group(1))
                        cofactor = int(match.group(2))
                        found_witness = (factor, cofactor)
                elif "Partition B produced no witness" in line:
                    print("  " + line)
                elif "Composing final witness" in line:
                    print("  " + line)
                elif "Verification:" in line:
                    print("  " + line)

        if found_witness:
            factor, cofactor = found_witness
            print("\n[SUCCESS] Factored", n, "=", factor, "x", cofactor)
        else:
            print("\n[FAIL] No witness recovered from partition search")

    finally:
        for path in temp_scripts:
            path.unlink(missing_ok=True)
        program_path.unlink(missing_ok=True)


def main() -> None:
    run_partition_based_rsa_demo(91)


if __name__ == "__main__":
    main()

