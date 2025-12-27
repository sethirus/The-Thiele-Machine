#!/usr/bin/env python3
"""Genesis Compression demo.

Creates a 2D "primordial soup" from pure noise and evolves it under:
- a reversible 2D CA rule (Margolus HPP lattice gas)
- a fixed "μ-like" budget that triggers deterministic lossy compression pressure

Deliverables:
- Animated GIF (artifacts/genesis_compression.gif)
- Replay-verifiable NUSD receipt (artifacts/genesis_compression_nusd_receipt.jsonl)

Pipeline phases:
INIT → DISCOVER → CLASSIFY → DECOMPOSE → EXECUTE → MERGE → VERIFY → SUCCESS

Note:
This demonstrates how a compressibility constraint biases emergent structure.
It is not, by itself, a proof that biological life or intelligence is inevitable.
"""

from __future__ import annotations

import json
import time
from pathlib import Path

from thielecpu.vm import State, VM

RESET = "\033[0m"
BOLD = "\033[1m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
BLUE = "\033[34m"
CYAN = "\033[36m"
MAGENTA = "\033[35m"

REPO_ROOT = Path(__file__).resolve().parent.parent
RECEIPT_PATH = (REPO_ROOT / "artifacts" / "genesis_compression_nusd_receipt.jsonl").resolve()
GIF_PATH = (REPO_ROOT / "artifacts" / "genesis_compression.gif").resolve()


def print_header() -> None:
    print(f"{BOLD}{CYAN}╔════════════════════════════════════════════════════════════════╗{RESET}")
    print(f"{BOLD}{CYAN}║  GENESIS COMPRESSION - STRUCTURE UNDER A μ BUDGET             ║{RESET}")
    print(f"{BOLD}{CYAN}║  Noise → reversible CA → budget pressure → GIF + receipt      ║{RESET}")
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
    print_step("Preparing paths")
    print(f"  • GIF    : {GIF_PATH}")
    print(f"  • Receipt: {RECEIPT_PATH}\n")

    print_phase("DISCOVER")
    print_step("Primordial soup")
    print("  • Grid: 128x128 (random noise)")
    print("  • Update rule: reversible Margolus Critters")
    print("  • A/B: control (no pressure) vs pressured (μ budget)")
    print("  • Output : side-by-side animated GIF + replay-verifiable receipt")
    print("")

    print_phase("CLASSIFY")
    print_step("What this is")
    print("  • A falsifiable compression-pressure demo")
    print("  • Not a proof of inevitable biology\n")

    print_phase("DECOMPOSE")
    print_step("Module graph")
    print("  • Simulator: tools/genesis_compression.py")
    print("  • Receipt  : tools/make_nusd_receipt.py")
    print("  • Verifier : tools/verify_nusd_receipt.py\n")

    print_phase("EXECUTE")
    print_step("Running receipt generator inside VM")

    vm = VM(State())
    vm.python_globals["_vm_argv0"] = str((REPO_ROOT / "tools" / "make_nusd_receipt.py").resolve())
    vm.python_globals["_vm_script_args"] = [
        "--domain",
        "genesis_compression",
        "--output",
        str(RECEIPT_PATH),
        "--no-calibration",
        "--genesis-rule",
        "critters",
        "--genesis-include-control",
        "--genesis-display-phase-invert",
        "--genesis-init-density",
        "0.50",
        "--genesis-init-patch-frac",
        "1.0",
        "--genesis-render-hud",
        "--genesis-no-render-delta",
        "--genesis-render-motion",
        "--genesis-render-trail",
        "--genesis-trail-decay",
        "245",
        "--genesis-width",
        "128",
        "--genesis-height",
        "128",
        "--genesis-steps",
        "6000",
        "--genesis-seed",
        "20251226",
        "--genesis-budget-bits",
        "28000",
        "--genesis-dictionary-size",
        "8",
        "--genesis-pressure-stride",
        "5",
        "--genesis-sample-every",
        "120",
        "--genesis-sample-steps",
        "0",
        "1000",
        "2000",
        "3000",
        "4000",
        "5000",
        "6000",
        "--genesis-gif-path",
        str(GIF_PATH),
        "--genesis-gif-scale",
        "4",
        "--genesis-gif-fps",
        "20",
    ]

    for i in range(40):
        progress_bar("GENESIS", (i + 1) / 40.0, "evolving...")
        time.sleep(0.01)
    print("")

    _, out = vm.execute_python(str((REPO_ROOT / "tools" / "make_nusd_receipt.py").resolve()))
    if "NUSD receipt written" not in out:
        print(out.strip())
        raise SystemExit(2)

    print_phase("MERGE")
    print_step("Artifacts emitted")
    print(f"  • GIF    : {GREEN}{GIF_PATH}{RESET}")
    print(f"  • Receipt: {GREEN}{RECEIPT_PATH}{RESET}\n")

    print_phase("VERIFY")
    print_step("Replaying receipt")
    vm.python_globals["_vm_argv0"] = str((REPO_ROOT / "tools" / "verify_nusd_receipt.py").resolve())
    vm.python_globals["_vm_script_args"] = [str(RECEIPT_PATH), "--skip-calibration"]
    _, verify_out = vm.execute_python(str((REPO_ROOT / "tools" / "verify_nusd_receipt.py").resolve()))
    ok = "Receipt verification succeeded" in verify_out
    if not ok:
        print(verify_out.strip())
        raise SystemExit(3)

    res = _extract_result(RECEIPT_PATH) or {}

    print_phase("SUCCESS")
    print(f"{GREEN}✓ Receipt replay verified (hash chain + recomputed domain){RESET}")
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
