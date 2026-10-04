#!/usr/bin/env python3
"""Prove the board/loader against the actual FPGA netlist, at a CPU interface.

This is conditional component equivalence, NOT a proof of CPU/RAM equivalence.
The report names the shared CPU responses and every compared external output.
The reset base and arbitrary inductive step are both mandatory. Auxiliary FSM
invariants are proved with the comparison, never assumed for an execution.
See formal/loader-equivalence.txt for the contract and structural checks.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
TOP = "thiele_cpu_top_genesys2"


def board_cell_params(netlist_json: Path) -> dict:
    top = json.loads(netlist_json.read_text(encoding="utf-8"))["modules"][TOP]
    return {name: {"type": c["type"], "parameters": c.get("parameters", {})}
            for name, c in top["cells"].items() if c["type"] in ("IBUFDS", "MMCME2_BASE", "BUFGCE")}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--netlist-json", type=Path, default=ROOT / "build/thiele_xc7k325t.json")
    parser.add_argument("--report", type=Path, default=ROOT / "build/equiv_report.json")
    parser.add_argument("--yosys", default="yosys")
    parser.add_argument("--yosys-share", type=Path, help="optional Yosys data directory for a standalone installation")
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--seq", type=int, choices=[2], default=2,
                        help="two SAT frames describe one arbitrary transition, not an execution bound")
    parser.add_argument("--min-proven", type=int, default=0,
                        help="optional lower bound on compared component bits")
    parser.add_argument("--require", action="append", default=None,
                        help="compatibility option: system.m2_; all component outputs are always mandatory")
    args = parser.parse_args()
    if args.timeout < 1 or args.min_proven < 0:
        parser.error("timeout must be positive and min-proven nonnegative")
    if args.require is not None and args.require != ["system.m2_"]:
        parser.error("this component proof supports system.m2_; CPU equivalence remains unproved")

    sys.path.insert(0, str(ROOT / "scripts"))
    from board_gls import mmcm_ratio, wrapper_mmcm_params
    from loader_netlist_prove import prove

    cells = board_cell_params(args.netlist_json)
    types = sorted(c["type"] for c in cells.values())
    if types != ["BUFGCE", "IBUFDS", "MMCME2_BASE"]:
        raise SystemExit(f"board cells in the netlist: {types}")
    mmcm = next(c for c in cells.values() if c["type"] == "MMCME2_BASE")
    if mmcm_ratio(mmcm["parameters"]) != mmcm_ratio(wrapper_mmcm_params()):
        raise SystemExit("netlist MMCM divides differently from the wrapper source")
    ok = prove(args.netlist_json.resolve(), args.report.resolve(), yosys=args.yosys,
               yosys_share=args.yosys_share, timeout=args.timeout)
    report = json.loads(args.report.read_text(encoding="utf-8"))
    if report.get("compared_bits", 0) < args.min_proven:
        report["status"] = "FAIL"
        report["component_equivalent"] = False
        report["error"] = "fewer compared bits than the requested minimum"
        args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        ok = False
    print(f"[equiv] {report['status']}: reset and induction; "
          f"{report.get('compared_bits', 0)} component bits compared")
    print("[equiv] Conditional on equal CPU responses; CPU/RAM and physical timing are NOT proved here.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
