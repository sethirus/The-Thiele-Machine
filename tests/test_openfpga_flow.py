from __future__ import annotations

import os
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

        cpu_count = os.cpu_count() or 2
        threads = max(1, (cpu_count + 1) // 2)

        # Use simple synthesis script similar to CI
        ys_script = workdir / "synth.ys"
        ys_script.write_text(
            f"read_verilog -sv -DSYNTHESIS -DYOSYS_LITE {top_verilog}\n"
            f"prep -top thiele_cpu\n"
            f"check\n"
            f"stat\n"
            f"write_json {json_out}\n"
        )

        # Save the generated synth.ys script to a persistent location for debugging
        persistent_ys_path = repo_root / "debug_synth.ys"
        with open(persistent_ys_path, "w") as persistent_ys_file:
            persistent_ys_file.write(ys_script.read_text())

        # Log the location of the saved script
        print(f"Generated synth.ys script saved to: {persistent_ys_path}")

        # Use yosys explicitly
        subprocess.run(
            ["yosys", "-s", str(ys_script)],
            check=True,
            capture_output=True,
            text=True,
            cwd=str(repo_root),
            timeout=300,  # Reduced timeout for simpler synthesis
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
                str(threads),
                "--placer",
                "heap",
                "--router",
                "router1",
                "--placer-heap-cell-placement-timeout",
                "4",
                "--ignore-loops",
                "--ignore-rel-clk",
                "--no-tmdriv",
                "--timing-allow-fail",
            ],
            check=True,
            capture_output=True,
            text=True,
            timeout=600,  # Keep for P&R which can be slow
        )
        subprocess.run(
            ["ecppack", str(cfg_out), str(bit_out)],
            check=True,
            capture_output=True,
            text=True,
            timeout=60,
        )

        assert bit_out.exists()
