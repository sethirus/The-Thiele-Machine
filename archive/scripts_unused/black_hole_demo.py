#!/usr/bin/env python3

from __future__ import annotations

import json
import os

from thielecpu.hardware.cosim import run_verilog
from thielecpu.state import BianchiViolationError, MuLedger


def python_black_hole_demo() -> dict:
    ledger = MuLedger(mu_discovery=0, mu_execution=1)
    ledger.mu_tensor[0][0] = 2

    try:
        ledger.check_bianchi_consistency()
    except BianchiViolationError as exc:
        return {
            "layer": "python",
            "behavior": "fail-fast-exception",
            "exception": str(exc),
        }

    return {
        "layer": "python",
        "behavior": "no-violation",
        "exception": None,
    }


def rtl_probe_demo(backend: str) -> dict:
    program = "\n".join([
        "REVEAL 0 0 4",
        "REVEAL 0 1 4",
        "REVEAL 1 0 4",
        "HALT 0",
    ])
    state = run_verilog(program, timeout=30, backend=backend)

    if state is None:
        return {
            "layer": "rtl",
            "backend": backend,
            "available": False,
        }

    return {
        "layer": "rtl",
        "backend": backend,
        "available": True,
        "status": int(state.get("status", 0)),
        "mu": int(state.get("mu", 0)),
        "cycles": int(state.get("cycles", 0)),
    }


def main() -> int:
    backend = os.getenv("THIELE_RTL_SIM", "iverilog").strip().lower() or "iverilog"
    if backend not in {"iverilog", "verilator"}:
        raise ValueError(f"Unsupported THIELE_RTL_SIM backend: {backend}")

    report = {
        "summary": {
            "model_note": "mu-metric curvature is a machine-checked computational law of this architecture; it is not a claim about general-relativistic spacetime.",
            "proof_note": "Coq proofs guarantee the law in the formal model, and Python/RTL isomorphism tests show the implementation realizes the same law operationally.",
            "singularity_note": "python raises; rtl freezes when bianchi_alarm is asserted.",
        },
        "python_black_hole": python_black_hole_demo(),
        "rtl_probe": rtl_probe_demo(backend),
    }

    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
