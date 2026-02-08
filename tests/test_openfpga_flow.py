from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest


def _tool_available(name: str) -> bool:
    return shutil.which(name) is not None


@pytest.mark.skipif(
    not all(_tool_available(tool) for tool in ("yosys", "nextpnr-ecp5", "ecppack")),
    reason="open-source FPGA tools not available",
)
def test_openfpga_ecp5_bitstream_generation() -> None:
    repo_root = Path(__file__).resolve().parents[1]
    rtl_dir = repo_root / "thielecpu" / "hardware" / "rtl"
    top_verilog = rtl_dir / "thiele_cpu_unified.v"

    with tempfile.TemporaryDirectory() as tmpdir:
        workdir = Path(tmpdir)
        json_out = workdir / "thiele_cpu.json"
        cfg_out = workdir / "thiele_cpu.cfg"
        bit_out = workdir / "thiele_cpu.bit"

        subprocess.run(
            [
                "yosys",
                "-p",
                "read_verilog -sv -nomem2reg -DSYNTHESIS -DYOSYS_LITE "
                f"-I {rtl_dir} {top_verilog}; "
                f"synth_ecp5 -top thiele_cpu -json {json_out}",
            ],
            check=True,
            capture_output=True,
            text=True,
            cwd=str(repo_root),
            timeout=900,
        )
        subprocess.run(
            [
                "nextpnr-ecp5",
                "--json",
                str(json_out),
                "--textcfg",
                str(cfg_out),
                "--85k",
                "--package",
                "CABGA381",
                "--speed",
                "6",
                "--threads",
                "4",
                "--placer",
                "heap",
                "--router",
                "router1",
                "--placer-heap-cell-placement-timeout",
                "4",
                "--no-tmdriv",
                "--timing-allow-fail",
            ],
            check=True,
            capture_output=True,
            text=True,
            timeout=1200,
        )
        subprocess.run(
            ["ecppack", str(cfg_out), str(bit_out)],
            check=True,
            capture_output=True,
            text=True,
            timeout=300,
        )

        assert bit_out.exists()
