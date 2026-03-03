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
import os
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent
EXTRACTED_IR = REPO_ROOT / "build" / "thiele_core.ml"
EXTRACTED_MLI = REPO_ROOT / "build" / "thiele_core.mli"
RUNNER_SRC = REPO_ROOT / "tools" / "extracted_vm_runner.ml"
RUNNER_BIN = REPO_ROOT / "build" / "extracted_vm_runner"


def _ocaml_env() -> dict:
    """Return environment with increased OCaml stack size."""
    env = os.environ.copy()
    env.setdefault("OCAMLRUNPARAM", "l=64M")
    return env


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
            "ocamlfind", "ocamlc",
            "-package", "str",
            "-linkpkg",
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

    # In the extracted semantics, module IDs start at 1 (matching Python/RTL).
    # Costs are passed explicitly in the trace; choose costs so totals match
    # the Python μ-ledger for these operations.
    trace = "\n".join(
        [
            "FUEL 32",
            "PNEW {0,1} 2",
            "PNEW {2,3} 2",
            "PMERGE 1 2 4",
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
        env=_ocaml_env(),
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
        env=_ocaml_env(),
    )
    extracted = json.loads(proc.stdout)

    assert extracted["err"] is False

    # Full compute-state equivalence (regs + memory)
    assert extracted["regs"] == [int(x) & 0xFFFFFFFF for x in vm.register_file]
    assert extracted["mem"] == [int(x) & 0xFFFFFFFF for x in vm.data_memory]


def test_checkpoint_creates_json_file(tmp_path: Path) -> None:
    """CHECKPOINT directive saves state to a JSON file."""
    _compile_runner()

    trace = "\n".join([
        "FUEL 32",
        "PNEW {0,1} 3",
        "CHECKPOINT mid_state",
        "HALT 1",
    ])
    trace_path = tmp_path / "trace_ckpt.txt"
    trace_path.write_text(trace, encoding="utf-8")

    proc = subprocess.run(
        [str(RUNNER_BIN), str(trace_path)],
        check=True,
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        env=_ocaml_env(),
    )
    final = json.loads(proc.stdout)

    # Checkpoint file should exist in cwd (tmp_path)
    ckpt_file = tmp_path / "mid_state.json"
    assert ckpt_file.exists(), "Checkpoint file was not created"

    ckpt = json.loads(ckpt_file.read_text())
    # Checkpoint is taken AFTER PNEW (pc=1), before HALT
    assert ckpt["pc"] == 1
    assert ckpt["mu"] == 3
    assert ckpt["err"] is False

    # Final state should be after HALT (pc=3 because checkpoint occupies slot 1)
    assert final["pc"] == 3
    assert final["mu"] == 4


def test_resume_from_checkpoint(tmp_path: Path) -> None:
    """--resume restores state from a checkpoint JSON and continues execution."""
    _compile_runner()

    # Phase 1: Run up to checkpoint
    trace = "\n".join([
        "FUEL 32",
        "LOAD_IMM 0 42 1",
        "LOAD_IMM 1 99 1",
        "CHECKPOINT snap",
        "HALT 1",
    ])
    trace_path = tmp_path / "trace.txt"
    trace_path.write_text(trace, encoding="utf-8")

    subprocess.run(
        [str(RUNNER_BIN), str(trace_path)],
        check=True,
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        env=_ocaml_env(),
    )

    snap_file = tmp_path / "snap.json"
    assert snap_file.exists()
    snap = json.loads(snap_file.read_text())
    assert snap["pc"] == 2
    assert snap["mu"] == 2
    assert snap["regs"][0] == 42
    assert snap["regs"][1] == 99

    # Phase 2: Resume from checkpoint — PC=2 means we hit CHECKPOINT again then HALT
    proc2 = subprocess.run(
        [str(RUNNER_BIN), "--resume", str(snap_file), str(trace_path)],
        check=True,
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        env=_ocaml_env(),
    )
    resumed = json.loads(proc2.stdout)
    assert resumed["pc"] == 4
    assert resumed["mu"] == 3  # 2 from checkpoint + 1 for HALT
    assert resumed["regs"][0] == 42
    assert resumed["regs"][1] == 99


def test_mem_size_directive(tmp_path: Path) -> None:
    """MEM_SIZE directive controls memory array size."""
    _compile_runner()

    trace = "\n".join([
        "FUEL 10",
        "MEM_SIZE 512",
        "HALT 1",
    ])
    trace_path = tmp_path / "trace_mem.txt"
    trace_path.write_text(trace, encoding="utf-8")

    proc = subprocess.run(
        [str(RUNNER_BIN), str(trace_path)],
        check=True,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        env=_ocaml_env(),
    )
    result = json.loads(proc.stdout)
    assert len(result["mem"]) == 512


def test_write_port_outputs_register_values(tmp_path: Path) -> None:
    """WRITE_PORT writes register values to a file channel."""
    _compile_runner()

    out_file = tmp_path / "port_output.txt"
    trace = "\n".join([
        "FUEL 32",
        "LOAD_IMM 0 42 1",
        "LOAD_IMM 1 99 1",
        f"WRITE_PORT {out_file} 0",
        f"WRITE_PORT {out_file} 1",
        "HALT 1",
    ])
    trace_path = tmp_path / "trace_wp.txt"
    trace_path.write_text(trace, encoding="utf-8")

    proc = subprocess.run(
        [str(RUNNER_BIN), str(trace_path)],
        check=True,
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        env=_ocaml_env(),
    )
    result = json.loads(proc.stdout)
    assert result["err"] is False

    # Check output file contains the register values
    lines = out_file.read_text().strip().split("\n")
    assert lines == ["42", "99"]


def test_read_port_loads_values_into_registers(tmp_path: Path) -> None:
    """READ_PORT reads integers from a file channel into registers.

    NOTE: Programs using READ_PORT are NOT covered by the three-layer
    isomorphism (Philosophy B). The Coq proofs do not see these values.
    """
    _compile_runner()

    input_file = tmp_path / "port_input.txt"
    input_file.write_text("100\n200\n", encoding="utf-8")

    trace = "\n".join([
        "FUEL 32",
        f"READ_PORT 0 {input_file}",
        f"READ_PORT 1 {input_file}",
        "HALT 1",
    ])
    trace_path = tmp_path / "trace_rp.txt"
    trace_path.write_text(trace, encoding="utf-8")

    proc = subprocess.run(
        [str(RUNNER_BIN), str(trace_path)],
        check=True,
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        env=_ocaml_env(),
    )
    result = json.loads(proc.stdout)
    assert result["err"] is False
    assert result["regs"][0] == 100
    assert result["regs"][1] == 200


def test_read_write_port_roundtrip(tmp_path: Path) -> None:
    """WRITE_PORT output can be consumed by READ_PORT in a subsequent run."""
    _compile_runner()

    port_file = tmp_path / "pipe.txt"

    # Phase 1: Write values
    trace1 = "\n".join([
        "FUEL 32",
        "LOAD_IMM 5 12345 1",
        f"WRITE_PORT {port_file} 5",
        "HALT 1",
    ])
    t1_path = tmp_path / "trace1.txt"
    t1_path.write_text(trace1, encoding="utf-8")

    subprocess.run(
        [str(RUNNER_BIN), str(t1_path)],
        check=True,
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        env=_ocaml_env(),
    )

    # Phase 2: Read values back
    trace2 = "\n".join([
        "FUEL 32",
        f"READ_PORT 10 {port_file}",
        "HALT 1",
    ])
    t2_path = tmp_path / "trace2.txt"
    t2_path.write_text(trace2, encoding="utf-8")

    proc2 = subprocess.run(
        [str(RUNNER_BIN), str(t2_path)],
        check=True,
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        env=_ocaml_env(),
    )
    result = json.loads(proc2.stdout)
    assert result["regs"][10] == 12345
