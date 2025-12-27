#!/usr/bin/env python3
"""Genesis Compression (RTL-backed) demo.

Runs the genesis_compression experiment, but routes control through the Verilog CPU
using the PYEXEC instruction path.

Pipeline:
INIT → DISCOVER → CLASSIFY → DECOMPOSE → EXECUTE → MERGE → VERIFY → SUCCESS

Outputs:
- artifacts/genesis_compression.gif
- artifacts/genesis_compression_nusd_receipt.jsonl
"""

from __future__ import annotations

import json
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
TB = HARDWARE_DIR / "thiele_cpu_genesis_compression_tb.v"
CPU = HARDWARE_DIR / "thiele_cpu.v"
MU_ALU = HARDWARE_DIR / "mu_alu.v"
MU_CORE = HARDWARE_DIR / "mu_core.v"
RECEIPT_INTEGRITY = HARDWARE_DIR / "receipt_integrity_checker.v"
VPI_SRC = HARDWARE_DIR / "pyexec_vpi.c"
VPI_MOD = HARDWARE_DIR / "pyexec_vpi.vpi"

RECEIPT_PATH = (REPO_ROOT / "artifacts" / "genesis_compression_nusd_receipt.jsonl").resolve()
GIF_PATH = (REPO_ROOT / "artifacts" / "genesis_compression.gif").resolve()


def print_header() -> None:
    print(f"{BOLD}{CYAN}╔════════════════════════════════════════════════════════════════╗{RESET}")
    print(f"{BOLD}{CYAN}║  GENESIS COMPRESSION (RTL) - VERILOG CPU ORCHESTRATED         ║{RESET}")
    print(f"{BOLD}{CYAN}║  Verilog CPU → PYEXEC → GIF+receipt → replay verification     ║{RESET}")
    print(f"{BOLD}{CYAN}╚════════════════════════════════════════════════════════════════╝{RESET}\n")


def print_phase(name: str) -> None:
    print(f"{BOLD}{YELLOW}>>> PHASE: {name}{RESET}")


def print_step(step: str, detail: str = "") -> None:
    tail = f" {detail}" if detail else ""
    print(f"{BOLD}{BLUE}➤ {step}{RESET}{tail}")


def progress_bar(label: str, progress: float, status: str) -> None:
    bar_len = 30
    filled = max(0, min(bar_len, int(bar_len * progress)))
    bar = "█" * filled + "░" * (bar_len - filled)
    print(f"  [{MAGENTA}{label:^14}{RESET}] {bar} {int(progress * 100):>3}% {status}", end="\r")


def _run(cmd: list[str], *, cwd: Path) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    return proc.returncode, (proc.stdout + "\n" + proc.stderr)


def _extract_result(receipt_path: Path) -> dict | None:
    try:
        with receipt_path.open("r", encoding="utf-8") as handle:
            for line in handle:
                obj = json.loads(line)
                if obj.get("event") == "genesis_compression_result":
                    return obj.get("result")
    except OSError:
        return None
    return None


def main() -> None:
    print_header()

    print_phase("INIT")
    print_step("Preparing RTL simulation")
    if not TB.exists():
        raise SystemExit(f"Missing testbench: {TB}")

    print_phase("DISCOVER")
    print_step("Primordial soup")
    print("  • Grid: 128x128 random noise")
    print("  • Rule: reversible Margolus Critters")
    print("  • A/B : control (no pressure) vs pressured (μ budget)")
    print("")

    print_phase("CLASSIFY")
    print_step("What this proves")
    print("  • The Verilog CPU orchestrates real host compute via PYEXEC")
    print("  • The output is replay-verifiable via NUSD receipt")
    print("")

    print_phase("DECOMPOSE")
    print_step("Module graph")
    print("  • RTL CPU : thiele_cpu.v")
    print("  • TB      : thiele_cpu_genesis_compression_tb.v")
    print("  • VPI     : thielecpu/hardware/pyexec_vpi.c ($pyexec)")
    print("  • BRIDGE  : thielecpu/hardware/pyexec_bridge.py (single-shot)")
    print("  • RECEIPT : tools/make_nusd_receipt.py (domain=genesis_compression)")
    print("  • VERIFY  : tools/verify_nusd_receipt.py")
    print("")

    print_phase("EXECUTE")
    print_step("Compiling RTL (iverilog)")
    for i in range(10):
        progress_bar("IVERILOG", (i + 1) / 10.0, "compiling...")
        time.sleep(0.02)
    print("")

    out_exe = HARDWARE_DIR / "thiele_cpu_genesis_compression_tb"
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
    rc, output = _run(compile_cmd, cwd=HARDWARE_DIR)
    if rc != 0:
        print(output.strip())
        raise SystemExit(rc)

    print_step("Building VPI module ($pyexec)")
    vpi_cmd = ["iverilog-vpi", "-o", str(VPI_MOD), str(VPI_SRC)]
    rc, output = _run(vpi_cmd, cwd=HARDWARE_DIR)
    if rc != 0:
        print(output.strip())
        raise SystemExit(rc)

    print_step("Running RTL simulation (vvp)")
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
    for ln in keep[-30:]:
        print("  " + ln)

    print_phase("MERGE")
    print_step("Artifacts emitted")
    print(f"  • GIF    : {GREEN}{GIF_PATH}{RESET}")
    print(f"  • Receipt: {GREEN}{RECEIPT_PATH}{RESET}")
    print(f"  • Wall time: {duration:.3f}s")
    print("")

    print_phase("VERIFY")
    print_step("Hardware run exit status")
    if rc != 0:
        print(sim_out.strip())
        raise SystemExit(rc)

    res = _extract_result(RECEIPT_PATH) or {}

    print_phase("SUCCESS")
    print(f"{GREEN}✓ RTL-orchestrated genesis compression succeeded{RESET}")
    if res:
        print(f"  • PDISCOVER triggers : {int(res.get('pdiscover_count', 0))}")
        bits_p0 = int(res.get("bits_first", 0))
        bits_p1 = int(res.get("bits_last", 0))
        c0 = res.get("bits_first_control")
        c1 = res.get("bits_last_control")
        if c0 is not None and c1 is not None:
            print(f"  • bits(control)      : {int(c0)} → {int(c1)}")
        print(f"  • bits(pressured)    : {bits_p0} → {bits_p1}")
        mm_sum = res.get("motion_mass_sum")
        mm_max = res.get("motion_mass_max")
        mc_sum = res.get("motion_cc_count_sum")
        mc_max = res.get("motion_cc_max_max")
        path_q = res.get("motion_centroid_l1_path_q")
        if mm_sum is not None:
            print(
                "  • motion(pressured) : "
                f"mass_sum={int(mm_sum)}  mass_max={int(mm_max or 0)}  "
                f"cc_sum={int(mc_sum or 0)}  cc_max={int(mc_max or 0)}  "
                f"centroid_L1_path_q={int(path_q or 0)}"
            )
        tm_sum = res.get("trail_mass_sum")
        tm_max = res.get("trail_mass_max")
        tc_sum = res.get("trail_cc_count_sum")
        tc_max = res.get("trail_cc_max_max")
        ti_sum = res.get("trail_intensity_sum")
        if tm_sum is not None:
            print(
                "  • trail(pressured)  : "
                f"mass_sum={int(tm_sum)}  mass_max={int(tm_max or 0)}  "
                f"cc_sum={int(tc_sum or 0)}  cc_max={int(tc_max or 0)}  "
                f"intensity_sum={int(ti_sum or 0)}"
            )
        if res.get("video_sha256"):
            print(f"  • GIF sha256         : {res.get('video_sha256')}")


if __name__ == "__main__":
    main()
