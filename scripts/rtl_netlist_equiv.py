#!/usr/bin/env python3
"""Formal equivalence of the RTL and the netlist the bitstream is built from.

Gold: the RTL exactly as synth_xc7.ys reads it (RegFile.v, thiele_cpu_kami.v,
thiele_system.v, thiele_cpu_top_genesys2.v with -DSYNTHESIS), elaborated and
flattened (hierarchy, proc, flatten, memory -nomap).
Gate: the JSON netlist from synth_xc7.ys (the file nextpnr places and
routes), with yosys's xilinx cells_sim.v as the functional model of every
cell, flattened the same way.

In both, the three board cells (IBUFDS, MMCME2_BASE, BUFGCE) are deleted and
the CPU clock net cpu_clk becomes a primary input, so the comparison is of
everything those cells feed. The script checks separately that the netlist's
board cells carry the wrapper's parameters.

yosys equiv_make pairs every net that has the same name in both designs
(register outputs survive synthesis under their RTL names); equiv_simple
proves each pair equal from the pairs feeding it (combinational cones, then
up to SEQ register stages); equiv_induct proves what is left by induction
over the pairs. The result is a set of $equiv cells, each proven or not.

How to read the result. If every $equiv cell is proven, the gate netlist and
the RTL are sequentially equivalent from equal register states (equal after
reset). If some are unproven, the proven ones hold under the assumption that
the unproven pairs are equal; that is a conditional statement, not
equivalence, and the report says so and lists the unproven nets. Known
reasons a pair stays unproven: a net downstream of a LUT-RAM read (the RAM is
a different structure in the two designs: a yosys $mem against LUT-RAM cells
and their bank logic), and a state register the `fsm` pass re-encoded. Those
parts are covered by the gate-level simulation (scripts/board_gls.py), not by
this proof.

Exit status: non-zero if yosys fails, if the report cannot be parsed, or if
the number of proven cells falls below --min-proven (pin it to the measured
value so a regression fails), or if any net named in --require is unproven.

  python3 scripts/rtl_netlist_equiv.py --netlist-json build/thiele_xc7k325t.json
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RTL = ROOT / "thielecpu" / "hardware" / "rtl"
TOP = "thiele_cpu_top_genesys2"
BOARD_CELLS = ["ibufds_sysclk", "mmcm_cpu", "bufg_cpu"]
RTL_FILES = ["RegFile.v", "thiele_cpu_kami.v", "thiele_system.v", "thiele_cpu_top_genesys2.v"]

# Register groups that must come out proven for the run to pass when given
# with --require (prefix match on the net name).
DEFAULT_REQUIRE = ["system.m2_"]   # loader, report and LED logic


def yosys_script(netlist_json: Path, seq: int, unproven_out: Path) -> str:
    rtl = " ".join(str(RTL / f) for f in RTL_FILES)
    delete = " ".join(f"{TOP}/{c}" for c in BOARD_CELLS)
    return f"""
# ---- gold: the RTL ----
read_verilog -lib +/xilinx/cells_xtra.v
read_verilog -sv -DSYNTHESIS {rtl}
hierarchy -top {TOP}
proc
flatten
delete {delete}
setundef -undriven -expose
opt_clean
memory -nomap
opt_clean
design -stash gold

# ---- gate: the netlist nextpnr places ----
read_json {netlist_json}
read_verilog -overwrite +/xilinx/cells_sim.v
hierarchy -top {TOP}
delete {delete}
flatten
proc
setundef -undriven -expose
opt_clean
memory -nomap
opt_clean
design -stash gate

# ---- pair and prove ----
design -copy-from gold -as gold {TOP}
design -copy-from gate -as gate {TOP}
equiv_make gold gate equiv
hierarchy -top equiv
async2sync
equiv_simple -seq {seq}
equiv_induct -seq {seq}
tee -o {unproven_out} equiv_status
"""


def parse_status(text: str) -> dict:
    m = re.search(r"Found (\d+) \$equiv cells in \S+:\s*\n\s*Of those cells (\d+) are proven and (\d+) are unproven", text)
    if not m:
        raise SystemExit("could not parse equiv_status output")
    total, proven, unproven = map(int, m.groups())
    nets = re.findall(r"Unproven \$equiv \S+: (\S+) (\S+)", text)
    return {"total": total, "proven": proven, "unproven": unproven,
            "unproven_nets": sorted({g.lstrip("\\") for g, _ in nets})}


def board_cell_params(netlist_json: Path) -> dict:
    top = json.loads(netlist_json.read_text(encoding="utf-8"))["modules"][TOP]
    return {name: {"type": c["type"], "parameters": c.get("parameters", {})}
            for name, c in top["cells"].items() if c["type"] in ("IBUFDS", "MMCME2_BASE", "BUFGCE")}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--netlist-json", type=Path, default=ROOT / "build" / "thiele_xc7k325t.json")
    ap.add_argument("--seq", type=int, default=2, help="register stages for equiv_simple/equiv_induct")
    ap.add_argument("--min-proven", type=int, default=0)
    ap.add_argument("--require", action="append", default=None,
                    help="net-name prefix that must have no unproven pair (default: system.m2_)")
    ap.add_argument("--report", type=Path, default=ROOT / "build" / "equiv_report.json")
    args = ap.parse_args()

    sys.path.insert(0, str(ROOT / "scripts"))
    from board_gls import mmcm_ratio, wrapper_mmcm_params
    cells = board_cell_params(args.netlist_json)
    types = sorted(c["type"] for c in cells.values())
    if types != ["BUFGCE", "IBUFDS", "MMCME2_BASE"]:
        raise SystemExit(f"board cells in the netlist: {types}")
    mmcm = next(c for c in cells.values() if c["type"] == "MMCME2_BASE")
    if mmcm_ratio(mmcm["parameters"]) != mmcm_ratio(wrapper_mmcm_params()):
        raise SystemExit("netlist MMCM divides differently from the wrapper source")

    work = args.report.parent
    work.mkdir(parents=True, exist_ok=True)
    status_file = work / "equiv_status.txt"
    script = work / "equiv.ys"
    script.write_text(yosys_script(args.netlist_json.resolve(), args.seq, status_file), encoding="utf-8")
    log = work / "equiv.log"
    proc = subprocess.run(["yosys", "-l", str(log), "-q", "-s", str(script)],
                          capture_output=True, text=True)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr[-4000:])
        raise SystemExit("yosys failed; see " + str(log))
    res = parse_status(status_file.read_text(encoding="utf-8"))
    require = args.require if args.require is not None else DEFAULT_REQUIRE
    bad = sorted(n for n in res["unproven_nets"] if any(n.startswith(p) for p in require))
    res["required_prefixes"] = require
    res["required_unproven"] = bad
    res["equivalent"] = res["unproven"] == 0
    args.report.write_text(json.dumps(res, indent=2) + "\n", encoding="utf-8")
    groups: dict[str, int] = {}
    for n in res["unproven_nets"]:
        key = re.sub(r"\[\d+\]$", "", n).split(".")[-1] if n.startswith("system.") else n
        groups[key] = groups.get(key, 0) + 1
    print(f"[equiv] {res['proven']} of {res['total']} paired nets proven equal; "
          f"{res['unproven']} unproven")
    if res["unproven"]:
        print("[equiv] NOT an equivalence proof: the proven pairs hold assuming the unproven ones do.")
        for k, v in sorted(groups.items(), key=lambda kv: -kv[1])[:40]:
            print(f"    unproven: {k} ({v})")
    failed = False
    if res["proven"] < args.min_proven:
        print(f"[equiv] FAIL: {res['proven']} proven, fewer than the pinned {args.min_proven}")
        failed = True
    if bad:
        print(f"[equiv] FAIL: unproven nets under required prefixes: {bad[:20]}")
        failed = True
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
