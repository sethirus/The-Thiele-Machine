"""
thielecpu/hardware/cosim.py — Canonical cross-layer Verilog co-simulation surface.

This module is the authoritative entry point for RTL co-simulation of the Thiele CPU.
It delegates to rtl_harness/cosim.py which implements the full simulation engine,
and enforces that the canonical Kami RTL path (thiele_cpu_kami.v + thiele_cpu_kami_tb.v)
is used as the ground-truth hardware reference.

Cross-layer isomorphism chain:
  Coq kernel (VMStep.v) → OCaml extraction → Python VM → [this file] → Verilog RTL

Environment variable THIELE_RTL_SIM selects the simulation backend:
  - "iverilog"   : Icarus Verilog (default, no install required beyond iverilog)
  - "verilator"  : Verilator (faster, requires verilator installed)

Required RTL artifacts:
  - thielecpu/hardware/rtl/thiele_cpu_kami.v      (generated from Kami spec via bsc)
  - rtl_harness/testbench/thiele_cpu_kami_tb.v    (co-simulation testbench)
"""

from __future__ import annotations

import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

# Ensure the repo root is on the path so rtl_harness can be imported.
_REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

# Canonical RTL paths — these MUST point to the Kami-generated artifacts.
_RTL_DIR = _REPO_ROOT / "thielecpu" / "hardware" / "rtl"
CANONICAL_RTL = _RTL_DIR / "thiele_cpu_kami.v"
CANONICAL_TB  = _REPO_ROOT / "rtl_harness" / "testbench" / "thiele_cpu_kami_tb.v"

# Import the full simulation engine from the rtl_harness layer.
from rtl_harness.cosim import (  # noqa: E402
    OPCODES,
    run_verilog,
    run_verilog_batch,
    compile_testbench_iverilog,
    program_to_hex,
)

__all__ = [
    "OPCODES",
    "CANONICAL_RTL",
    "CANONICAL_TB",
    "run_verilog",
    "run_verilog_batch",
    "compile_testbench_iverilog",
    "program_to_hex",
]


def assert_rtl_artifacts_present() -> None:
    """Raise FileNotFoundError if canonical RTL artifacts are missing."""
    for p in (CANONICAL_RTL,):
        if not p.exists():
            raise FileNotFoundError(
                f"Canonical Kami RTL artifact missing: {p}\n"
                "Rebuild with: scripts/kami_extract.sh"
            )
