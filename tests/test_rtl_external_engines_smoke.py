from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

from tools.verify_end_to_end import HARDWARE_DIR


@pytest.mark.integration
def test_rtl_external_engines_smoke():
    if shutil.which("iverilog") is None or shutil.which("vvp") is None:
        pytest.skip("iverilog/vvp not available in PATH")

    compile_cmd = [
        "iverilog",
        "-g2012",
        "-I",
        str(HARDWARE_DIR),
        "-o",
        "thiele_cpu_engines_tb.out",
        "thiele_cpu.v",
        "thiele_cpu_engines_tb.v",
        "lei.v",
        "pee.v",
        "mu_alu.v",
        "mu_core.v",
    ]

    with tempfile.TemporaryDirectory() as td:
        out = str((Path(td) / "thiele_cpu_engines_tb.out").resolve())
        compile_cmd_with_out = list(compile_cmd)
        compile_cmd_with_out[compile_cmd_with_out.index("thiele_cpu_engines_tb.out")] = out
        subprocess.run(compile_cmd_with_out, cwd=HARDWARE_DIR, check=True, capture_output=True, text=True)

        run = subprocess.run(
            ["vvp", out],
            cwd=HARDWARE_DIR,
            check=True,
            capture_output=True,
            text=True,
            timeout=30,
        )

    assert "ENGINES_SMOKE_OK" in run.stdout
