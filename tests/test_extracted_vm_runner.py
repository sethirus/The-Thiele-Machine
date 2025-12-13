# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Executable check: Coq-extracted VM semantics runner.

This test compiles and executes an OCaml runner against the Coq-extracted
semantics in build/thiele_core.ml, then compares a small trace against the
Python canonical State implementation.

Goal: Make the Coq extraction an executable "ground truth" leg in CI.
"""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent
EXTRACTED_IR = REPO_ROOT / "build" / "thiele_core.ml"
EXTRACTED_MLI = REPO_ROOT / "build" / "thiele_core.mli"
RUNNER_SRC = REPO_ROOT / "tools" / "extracted_vm_runner.ml"
RUNNER_BIN = REPO_ROOT / "build" / "extracted_vm_runner"


def _compile_runner() -> None:
    if not EXTRACTED_IR.exists():
        pytest.skip("missing build/thiele_core.ml (run `make -C coq Extraction.vo`) ")
    if not EXTRACTED_MLI.exists():
        pytest.skip("missing build/thiele_core.mli (run `make -C coq Extraction.vo`)")
    if not RUNNER_SRC.exists():
        pytest.skip("missing tools/extracted_vm_runner.ml")
    if shutil.which("ocamlc") is None:
        pytest.skip("ocamlc not available")

    def _mtime(path: Path) -> float:
        try:
            return path.stat().st_mtime
        except FileNotFoundError:
            return 0.0

    # Rebuild if missing or stale.
    if RUNNER_BIN.exists():
        bin_time = _mtime(RUNNER_BIN)
        if bin_time >= max(_mtime(EXTRACTED_IR), _mtime(EXTRACTED_MLI), _mtime(RUNNER_SRC)):
            return

    subprocess.run(
        [
            "ocamlc",
            "-I",
            str(REPO_ROOT / "build"),
            "-o",
            str(RUNNER_BIN),
            str(EXTRACTED_MLI),
            str(EXTRACTED_IR),
            str(RUNNER_SRC),
        ],
        check=True,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )


def _parse_regions_from_python_state(state) -> list[tuple[int, ...]]:
    modules = getattr(state.regions, "modules", {})
    regions = [tuple(sorted(region)) for region in modules.values()]
    return sorted(regions)


def _parse_regions_from_extracted(output: dict) -> list[tuple[int, ...]]:
    modules = output["graph"]["modules"]
    regions = [tuple(module["region"]) for module in modules]
    return sorted(regions)


def test_extracted_pnew_pmerge_matches_python_state(tmp_path: Path) -> None:
    _compile_runner()

    from thielecpu.state import State

    py_state = State()
    m1 = py_state.pnew({0, 1})
    m2 = py_state.pnew({2, 3})
    py_state.pmerge(m1, m2)

    python_regions = _parse_regions_from_python_state(py_state)
    python_mu = py_state.mu_ledger.total

    # In the extracted semantics, module IDs start at 0.
    # Costs are passed explicitly in the trace; choose costs so totals match
    # the Python μ-ledger for these operations.
    trace = "\n".join(
        [
            "FUEL 32",
            "PNEW {0,1} 2",
            "PNEW {2,3} 2",
            "PMERGE 0 1 4",
        ]
    )
    trace_path = tmp_path / "trace.txt"
    trace_path.write_text(trace, encoding="utf-8")

    proc = subprocess.run(
        [str(RUNNER_BIN), str(trace_path)],
        check=True,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )

    extracted = json.loads(proc.stdout)
    extracted_regions = _parse_regions_from_extracted(extracted)

    assert extracted["err"] is False
    assert extracted_regions == python_regions
    assert extracted["mu"] == python_mu


def test_extracted_xor_xfer_matches_python_vm(tmp_path: Path) -> None:
    _compile_runner()

    from thielecpu.state import State
    from thielecpu.vm import VM

    state = State()
    vm = VM(state)

    # Deterministic preload
    vm.data_memory[5] = 0x12345678
    vm.register_file[7] = 0x0F0F0F0F
    vm.register_file[9] = 0xF0F0F0F0

    program = [
        ("XOR_LOAD", "0 5"),
        ("XOR_RANK", "1 0"),
        ("XOR_ADD", "7 9"),
        ("XOR_SWAP", "0 1"),
        ("XFER", "2 0"),
        ("HALT", "0"),
    ]

    outdir = tmp_path / "vm_out"
    outdir.mkdir(parents=True, exist_ok=True)
    vm.run(program, outdir)

    trace = "\n".join(
        [
            "FUEL 64",
            "INIT_MEM 5 305419896",  # 0x12345678
            "INIT_REG 7 252645135",  # 0x0F0F0F0F
            "INIT_REG 9 4042322160",  # 0xF0F0F0F0
            "XOR_LOAD 0 5 0",
            "XOR_RANK 1 0 0",
            "XOR_ADD 7 9 0",
            "XOR_SWAP 0 1 0",
            "XFER 2 0 0",
            "HALT 0",
        ]
    )
    trace_path = tmp_path / "trace_compute.txt"
    trace_path.write_text(trace, encoding="utf-8")

    proc = subprocess.run(
        [str(RUNNER_BIN), str(trace_path)],
        check=True,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    extracted = json.loads(proc.stdout)

    assert extracted["err"] is False

    # Full compute-state equivalence (regs + memory)
    assert extracted["regs"] == [int(x) & 0xFFFFFFFF for x in vm.register_file]
    assert extracted["mem"] == [int(x) & 0xFFFFFFFF for x in vm.data_memory]
