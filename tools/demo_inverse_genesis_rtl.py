#!/usr/bin/env python3
"""Inverse Genesis (RTL-backed) demo.

This runs the exact same NUSD receipt generation + replay verification as the
Python-VM demo, but it *routes control through the Verilog CPU* using the RTL
PYEXEC interface.

Pipeline:
INIT → DISCOVER → CLASSIFY → DECOMPOSE → EXECUTE → MERGE → VERIFY → SUCCESS

Mechanics:
- Icarus Verilog runs `thiele_cpu` with a tiny program of PYEXEC instructions.
- The testbench services `py_req` by calling $pyexec (an Icarus VPI system task).
- The VPI task runs a real Python bridge in single-shot mode to perform work.

So the Verilog CPU is the orchestrator; Python does the heavy host compute.
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
TB = HARDWARE_DIR / "thiele_cpu_inverse_genesis_tb.v"
CPU = HARDWARE_DIR / "thiele_cpu.v"
MU_ALU = HARDWARE_DIR / "mu_alu.v"
MU_CORE = HARDWARE_DIR / "mu_core.v"
RECEIPT_INTEGRITY = HARDWARE_DIR / "receipt_integrity_checker.v"
VPI_SRC = HARDWARE_DIR / "pyexec_vpi.c"
VPI_MOD = HARDWARE_DIR / "pyexec_vpi.vpi"

RECEIPT_PATH = (REPO_ROOT / "artifacts" / "inverse_genesis_nusd_receipt.jsonl").resolve()


def print_header() -> None:
    print(f"{BOLD}{CYAN}╔════════════════════════════════════════════════════════════════╗{RESET}")
    print(f"{BOLD}{CYAN}║  INVERSE GENESIS (RTL) - VERILOG CPU ORCHESTRATED DISCOVERY   ║{RESET}")
    print(f"{BOLD}{CYAN}║  Verilog CPU → PYEXEC → receipt → replay verification         ║{RESET}")
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


def _extract_candidate(receipt_path: Path) -> dict | None:
    try:
        with receipt_path.open("r", encoding="utf-8") as handle:
            for line in handle:
                obj = json.loads(line)
                if obj.get("event") == "inverse_genesis_invariant":
                    return obj.get("candidate")
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
    print_step("Setting up discovery run (chaotic double pendulum)")
    print("  • Control: Verilog CPU executes PYEXEC")
    print("  • Compute: host Python bridge performs receipt generation")
    print("")

    print_phase("CLASSIFY")
    print_step("Classifying workload")
    print("  • Type: RTL-orchestrated host compute")
    print("  • Output: equation + receipt + replay verifier")
    print("")

    print_phase("DECOMPOSE")
    print_step("Module graph")
    print("  • RTL CPU : thiele_cpu.v")
    print("  • TB      : thiele_cpu_inverse_genesis_tb.v")
    print("  • VPI     : thielecpu/hardware/pyexec_vpi.c ($pyexec)")
    print("  • BRIDGE  : thielecpu/hardware/pyexec_bridge.py (single-shot)")
    print("  • RECEIPT : tools/make_nusd_receipt.py")
    print("  • VERIFY  : tools/verify_nusd_receipt.py")
    print("")

    print_phase("EXECUTE")
    print_step("Compiling RTL (iverilog)")
    for i in range(10):
        progress_bar("IVERILOG", (i + 1) / 10.0, "compiling...")
        time.sleep(0.02)
    print("")

    out_exe = HARDWARE_DIR / "thiele_cpu_inverse_genesis_tb"
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

    # Keep terminal output clean: show only the PYEXEC lines + completion summary.
    lines = [ln for ln in sim_out.splitlines() if ln.strip()]
    keep = [ln for ln in lines if ln.startswith("[RTL]")]
    for ln in keep[-20:]:
        print("  " + ln)

    print_phase("MERGE")
    print_step("Receipt emitted", f"{GREEN}{RECEIPT_PATH}{RESET}")
    print(f"  • Wall time: {duration:.3f}s")
    print("")

    print_phase("VERIFY")
    print_step("Hardware run exit status")
    if rc != 0:
        print(sim_out.strip())
        raise SystemExit(rc)

    cand = _extract_candidate(RECEIPT_PATH)

    print_phase("SUCCESS")
    print(f"{GREEN}✓ RTL-orchestrated receipt generation + replay verification succeeded{RESET}")
    if cand and cand.get("expression"):
        print(f"{BOLD}{CYAN}Discovered invariant:{RESET}")
        print(f"  {cand.get('expression')}")
        print(f"  • compression_ratio: {float(cand.get('compression_ratio', 0.0)):.2f}x")
        print(f"  • relative_std      : {float(cand.get('relative_std', 0.0)):.4f}")
        terms = cand.get("terms")
        if isinstance(terms, list):
            print(f"  • terms             : {len(terms)}")
            print(f"{BOLD}{CYAN}Candidate (copy/paste):{RESET}")
            print("  terms=" + json.dumps(terms, separators=(",", ":")))
            print("  intercept=" + json.dumps(cand.get("intercept"), separators=(",", ":")))
            print("  coefficients=" + json.dumps(cand.get("coefficients"), separators=(",", ":")))


if __name__ == "__main__":
    main()
