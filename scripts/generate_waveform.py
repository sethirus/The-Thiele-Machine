"""Generate a VCD waveform for the Thiele CPU testbench."""
from __future__ import annotations

import tempfile
import shutil
import subprocess
from pathlib import Path
from typing import List

REPO_ROOT = Path(__file__).resolve().parent.parent
HW_DIR = REPO_ROOT / "thielecpu" / "hardware"
RESULTS_DIR = REPO_ROOT / "results"


def _collect_sources() -> List[Path]:
    """Return the minimal source set needed to build the testbench."""

    core_sources = [
        "mu_alu.v",
        "mu_core.v",
        "thiele_cpu.v",
        "thiele_cpu_tb.v",
    ]
    missing = [name for name in core_sources if not (HW_DIR / name).exists()]
    if missing:
        raise RuntimeError(f"missing expected sources: {missing}")
    return [HW_DIR / name for name in core_sources]


def generate_waveform(out_prefix: str = "thiele_cpu_tb", output_dir: Path = RESULTS_DIR) -> Path:
    """Compile and run the RTL testbench, returning the VCD path.

    The compiled simulator binary is placed in a temporary directory to avoid
    polluting the repository with build outputs.
    """

    if shutil.which("iverilog") is None:
        raise RuntimeError("iverilog is not installed; install it to generate waveforms")

    sources = _collect_sources()
    if not sources:
        raise RuntimeError("no Verilog sources found in thielecpu/hardware")

    output_dir.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        sim_bin = td_path / f"{out_prefix}.out"
        # The testbench hardcodes the dumpfile name.
        produced_vcd = td_path / "thiele_cpu_tb.vcd"
        final_vcd = output_dir / f"{out_prefix}.vcd"

        compile_cmd = [
            "iverilog",
            "-g2012",
            "-s",
            "thiele_cpu_tb",
            "-I",
            str(HW_DIR),
            "-o",
            str(sim_bin),
        ] + [str(src) for src in sources]

        subprocess.run(compile_cmd, check=True, cwd=HW_DIR)

        # Run the simulation inside the temp directory so any auxiliary files stay ephemeral.
        subprocess.run(["vvp", str(sim_bin.resolve())], check=True, cwd=td_path)

        if not produced_vcd.exists():
            raise RuntimeError(f"Expected VCD at {produced_vcd} was not produced")
        final_vcd.write_bytes(produced_vcd.read_bytes())

    return final_vcd


if __name__ == "__main__":
    path = generate_waveform()
    print(f"Waveform captured at {path}")
