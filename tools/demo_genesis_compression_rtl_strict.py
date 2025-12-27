#!/usr/bin/env python3
"""Genesis Compression (RTL-backed, strict digest) demo.

Runs a stricter RTL co-sim that asserts (in Verilog) that a 32-bit digest derived
from the produced receipt remains stable across the host-side verifier.

This is still host-compute for the heavy work, but RTL now checks an invariant
beyond just rc=0.
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

RESET = "\033[0m"
BOLD = "\033[1m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
BLUE = "\033[34m"
CYAN = "\033[36m"
MAGENTA = "\033[35m"

REPO_ROOT = Path(__file__).resolve().parent.parent
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"
TB = HARDWARE_DIR / "thiele_cpu_genesis_compression_strict_tb.v"
CPU = HARDWARE_DIR / "thiele_cpu.v"
MU_ALU = HARDWARE_DIR / "mu_alu.v"
MU_CORE = HARDWARE_DIR / "mu_core.v"
RECEIPT_INTEGRITY = HARDWARE_DIR / "receipt_integrity_checker.v"
VPI_SRC = HARDWARE_DIR / "pyexec_vpi.c"
VPI_MOD = HARDWARE_DIR / "pyexec_vpi.vpi"

GIF_PATH = (REPO_ROOT / "artifacts" / "genesis_compression.gif").resolve()
RECEIPT_PATH = (REPO_ROOT / "artifacts" / "genesis_compression_nusd_receipt.jsonl").resolve()


def print_phase(name: str) -> None:
    print(f"{BOLD}{YELLOW}>>> PHASE: {name}{RESET}")


def progress_bar(label: str, progress: float, status: str) -> None:
    bar_len = 30
    filled = max(0, min(bar_len, int(bar_len * progress)))
    bar = "█" * filled + "░" * (bar_len - filled)
    print(f"  [{MAGENTA}{label:^14}{RESET}] {bar} {int(progress * 100):>3}% {status}", end="\r")


def _run(cmd: list[str], *, cwd: Path) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    return proc.returncode, (proc.stdout + "\n" + proc.stderr)


def main() -> None:
    print(f"{BOLD}{CYAN}╔════════════════════════════════════════════════════════════════╗{RESET}")
    print(f"{BOLD}{CYAN}║  GENESIS COMPRESSION (RTL STRICT) - DIGEST ASSERTION          ║{RESET}")
    print(f"{BOLD}{CYAN}║  RTL asserts receipt-derived digest stability                  ║{RESET}")
    print(f"{BOLD}{CYAN}╚════════════════════════════════════════════════════════════════╝{RESET}\n")

    print_phase("INIT")
    if not TB.exists():
        raise SystemExit(f"Missing strict testbench: {TB}")

    print_phase("EXECUTE")
    for i in range(10):
        progress_bar("IVERILOG", (i + 1) / 10.0, "compiling...")
        time.sleep(0.02)
    print("")

    out_exe = HARDWARE_DIR / "thiele_cpu_genesis_compression_strict_tb"
    compile_cmd = [
        "iverilog",
        "-g2012",
        "-o",
        str(out_exe),
        str(CPU),
        str(TB),
        str(MU_ALU),
        str(MU_CORE),
        str(RECEIPT_INTEGRITY),
    ]
    rc, out = _run(compile_cmd, cwd=HARDWARE_DIR)
    if rc != 0:
        print(out.strip())
        raise SystemExit(rc)

    vpi_cmd = ["iverilog-vpi", "-o", str(VPI_MOD), str(VPI_SRC)]
    rc, out = _run(vpi_cmd, cwd=HARDWARE_DIR)
    if rc != 0:
        print(out.strip())
        raise SystemExit(rc)

    try:
        for i in range(20):
            progress_bar("RTL RUN", (i + 1) / 20.0, "executing...")
            time.sleep(0.02)
        print("")

        run_cmd = [
            "vvp",
            "-M",
            str(HARDWARE_DIR),
            "-m",
            "pyexec_vpi",
            str(out_exe),
            f"+REPO_ROOT={REPO_ROOT}",
        ]
        started = time.time()
        rc, sim_out = _run(run_cmd, cwd=HARDWARE_DIR)
        duration = time.time() - started

        lines = [ln for ln in sim_out.splitlines() if ln.strip()]
        keep = [ln for ln in lines if ln.startswith("[RTL]")]
        for ln in keep[-40:]:
            print("  " + ln)

        print_phase("RESULT")
        print(f"  • rc: {rc}")
        print(f"  • Wall time: {duration:.3f}s")
        print(f"  • GIF: {GIF_PATH}")
        print(f"  • Receipt: {RECEIPT_PATH}")

        if rc != 0:
            raise SystemExit(rc)

        print(f"{GREEN}✓ RTL digest assertion succeeded{RESET}")

    finally:
        pass


if __name__ == "__main__":
    main()
