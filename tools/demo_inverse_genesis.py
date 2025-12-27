#!/usr/bin/env python3
"""Inverse Genesis demo: discover conservation of energy from chaotic data.

This is an end-to-end, falsifiable run:
- Generates raw noisy double-pendulum data
- Runs an MDL-guided invariant discovery search ("find H that stays constant")
- Emits a NUSD receipt via the standard receipt pipeline
- Re-verifies the receipt by replaying the domain computation

Output is intentionally styled like other repo demos and uses the canonical
Thiele phases:
INIT → DISCOVER → CLASSIFY → DECOMPOSE → EXECUTE → MERGE → VERIFY → SUCCESS
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

# Add project root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.state import State
from thielecpu.vm import VM


RESET = "\033[0m"
BOLD = "\033[1m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
BLUE = "\033[34m"
CYAN = "\033[36m"
MAGENTA = "\033[35m"


def print_header() -> None:
    print(f"{BOLD}{CYAN}╔════════════════════════════════════════════════════════════════╗{RESET}")
    print(f"{BOLD}{CYAN}║  INVERSE GENESIS - AUTOMATED DISCOVERY OF PHYSICS              ║{RESET}")
    print(f"{BOLD}{CYAN}║  Chaotic data → conserved quantity → receipt → verification    ║{RESET}")
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


def main() -> None:
    print_header()

    receipt_path = (REPO_ROOT / "artifacts" / "inverse_genesis_nusd_receipt.jsonl").resolve()

    print_phase("INIT")
    print_step("Initializing Thiele VM")
    vm = VM(State())
    time.sleep(0.15)

    print_phase("DISCOVER")
    print_step("Setting up discovery run (chaotic double pendulum)")
    print("  • System: double pendulum (chaotic)")
    print("  • Goal: discover invariant H(theta1, theta2, omega1, omega2) ≈ constant")
    print("  • Input: noisy raw trajectory samples")
    print("")

    print_phase("CLASSIFY")
    print_step("Classifying discovery workload")
    print("  • Type: invariant discovery (MDL / Occam)")
    print("  • Output: explicit equation + receipt + replay verifier")
    print("")

    print_phase("DECOMPOSE")
    print_step("Module graph")
    print("  • DATA  : synthesize noisy trajectory")
    print("  • SEARCH: greedy MDL feature selection")
    print("  • RECEIPT: hash-chained NUSD log")
    print("  • VERIFY: replay domain + recompute NUSD")
    print("")

    print_phase("EXECUTE")
    print_step("Running receipt generator inside VM")

    # Animate a little while the VM runs the script.
    for i in range(10):
        progress_bar("DATA+SEARCH", (i + 1) / 10.0, "preparing...")
        time.sleep(0.03)
    print("")

    vm.python_globals["_vm_argv0"] = str((REPO_ROOT / "tools" / "make_nusd_receipt.py").resolve())
    vm.python_globals["_vm_script_args"] = [
        "--domain",
        "inverse_genesis",
        "--output",
        str(receipt_path),
        "--no-calibration",
        "--inverse-seed",
        "20251226",
        "--inverse-steps",
        "1024",
        "--inverse-dt",
        "0.01",
        "--inverse-noise-std",
        "0.002",
        "--inverse-max-terms",
        "6",
        "--inverse-min-gain-bits",
        "0.1",
        "--inverse-bits-per-sample",
        "64.0",
    ]

    started = time.time()
    _, out = vm.execute_python(str((REPO_ROOT / "tools" / "make_nusd_receipt.py").resolve()))
    duration = time.time() - started

    if out.strip():
        # Keep output tidy: show only the last few lines.
        lines = [line for line in out.splitlines() if line.strip()]
        for line in lines[-4:]:
            print(f"  {line}")

    print_phase("MERGE")
    print_step("Receipt emitted", f"{GREEN}{receipt_path}{RESET}")
    print(f"  • Wall time: {duration:.3f}s")
    print("")

    print_phase("VERIFY")
    print_step("Replaying domain computation and verifying hash chain")

    # Show a short verifier animation.
    for i in range(20):
        progress_bar("VERIFIER", (i + 1) / 20.0, "recomputing...")
        time.sleep(0.02)
    print("")

    vm.python_globals["_vm_argv0"] = str((REPO_ROOT / "tools" / "verify_nusd_receipt.py").resolve())
    vm.python_globals["_vm_script_args"] = [str(receipt_path), "--skip-calibration"]

    _, verify_out = vm.execute_python(str((REPO_ROOT / "tools" / "verify_nusd_receipt.py").resolve()))
    ok = "Receipt verification succeeded" in verify_out

    print_phase("SUCCESS")
    if ok:
        print(f"{GREEN}✓ Receipt replay verified (hash chain + recomputed MDL/NUSD){RESET}")

        # Extract and display the discovered invariant directly from the receipt.
        expression = None
        compression_ratio = None
        relative_std = None
        terms = None
        intercept = None
        coefficients = None
        try:
            with receipt_path.open("r", encoding="utf-8") as handle:
                for line in handle:
                    obj = json.loads(line)
                    if obj.get("event") == "inverse_genesis_invariant":
                        candidate = obj.get("candidate", {})
                        expression = candidate.get("expression")
                        compression_ratio = candidate.get("compression_ratio")
                        relative_std = candidate.get("relative_std")
                        terms = candidate.get("terms")
                        intercept = candidate.get("intercept")
                        coefficients = candidate.get("coefficients")
                        break
        except OSError:
            pass

        if expression:
            print(f"{BOLD}{CYAN}Discovered invariant:{RESET}")
            print(f"  {expression}")
            if compression_ratio is not None or relative_std is not None:
                cr_text = f"{float(compression_ratio):.2f}x" if compression_ratio is not None else "(n/a)"
                rs_text = f"{float(relative_std):.4f}" if relative_std is not None else "(n/a)"
                terms_text = str(len(terms)) if isinstance(terms, list) else "(n/a)"
                print(f"  • compression_ratio: {cr_text}")
                print(f"  • relative_std      : {rs_text}")
                print(f"  • terms             : {terms_text}")

            # Copy/paste-friendly block (kept intentionally compact).
            if isinstance(terms, list) and intercept is not None and coefficients is not None:
                print(f"{BOLD}{CYAN}Candidate (copy/paste):{RESET}")
                print("  terms=" + json.dumps(terms, separators=(",", ":")))
                print("  intercept=" + json.dumps(intercept, separators=(",", ":")))
                print("  coefficients=" + json.dumps(coefficients, separators=(",", ":")))
    else:
        print(verify_out.strip() or "Verification failed")
        raise SystemExit(1)

    print("")
    print_step("Next", "Inspect the discovered invariant in the receipt summary entry")
    print(f"  • Receipt: {receipt_path}")


if __name__ == "__main__":
    main()
