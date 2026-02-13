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

        # Write a yosys script that skips the 'share' pass.
        # The share pass explodes combinatorially on the region_table
        # $memrd cells (SAT activation patterns double per cell).
        ys_script = workdir / "synth.ys"
        ys_script.write_text(
            f"read_verilog -sv -nomem2reg -DSYNTHESIS -DYOSYS_LITE "
            f"-I {rtl_dir} {top_verilog}\n"
            # begin label (hierarchy):
            f"synth_ecp5 -top thiele_cpu -run begin:coarse\n"
            # coarse sub-passes WITHOUT share:
            "proc\n"
            "flatten\n"
            "tribuf -logic\n"
            "deminout\n"
            "opt_expr\n"
            "opt_clean\n"
            "check\n"
            "opt -nodffe -nosdff\n"
            "fsm\n"
            "opt\n"
            "wreduce\n"
            "peepopt\n"
            "opt_clean\n"
            # skip: share  (causes exponential blowup on region_table)
            "techmap -map +/cmp2lut.v -D LUT_WIDTH=4\n"
            "opt_expr\n"
            "opt_clean\n"
            "techmap -map +/mul2dsp.v -map +/ecp5/dsp_map.v "
            "-D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18 "
            "-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 "
            "-D DSP_NAME=$__MUL18X18\n"
            "chtype -set $mul t:$__soft_mul\n"
            "alumacc\n"
            "opt\n"
            "memory -nomap\n"
            "opt_clean\n"
            # resume from map_ram through end:
            f"synth_ecp5 -top thiele_cpu -run map_ram: -json {json_out}\n"
        )
        subprocess.run(
            ["yosys", "-s", str(ys_script)],
            check=True,
            capture_output=True,
            text=True,
            cwd=str(repo_root),
            timeout=1200,
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
            timeout=1200,  # align with automated_verification.sh default
        )
        subprocess.run(
            ["ecppack", str(cfg_out), str(bit_out)],
            check=True,
            capture_output=True,
            text=True,
            timeout=300,
        )

        assert bit_out.exists()
