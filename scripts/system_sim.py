#!/usr/bin/env python3
"""Load programs into the extracted system over its serial pin and compare.

For each program the script runs three things and requires them to agree on
the halted flag, the error flag, the program counter, the mu ledger, and the
error code:

1. the CPU alone, through the co-simulation testbench (the reference);
2. the extracted system (thiele_cpu_kami.v + thiele_system.v), loaded over
   its serial pin by rtl_harness/testbench/system_tb.v;
3. with --gates, the same testbench on a gate netlist yosys synthesizes from
   that Verilog, simulated with Verilator.

The system's report also carries its sync and end markers, which are
checked.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RTL = ROOT / "thielecpu" / "hardware" / "rtl"
TB = ROOT / "rtl_harness" / "testbench" / "system_tb.v"
SOURCES = [RTL / "RegFile.v", RTL / "thiele_cpu_kami.v", RTL / "thiele_system.v"]

PROGRAMS = {
    "arith_halt": "LOAD_IMM 1 5 0\nLOAD_IMM 2 7 1\nADD 3 1 2 3\nHALT 0",
    "jump_loop": "LOAD_IMM 1 3 0\nLOAD_IMM 2 1 0\nSUB 1 1 2 1\nJNEZ 1 2 0\nHALT 0",
}


def program_stream(program: str) -> list[int]:
    sys.path.insert(0, str(ROOT))
    from thielecpu.hardware.cosim import program_to_hex
    words, _data, init = program_to_hex(program)
    if init:
        raise ValueError("the serial loader writes instructions only; no INIT_* lines")
    words = [w for w in words if int(w, 16) != 0]
    if not 0 < len(words) <= 128:
        raise ValueError(f"a program has 1 to 128 instructions, not {len(words)}")
    out = [len(words) & 0xFF, len(words) >> 8]
    for w in words:
        out.extend(int(w, 16).to_bytes(16, "little"))
    return out


def reference(program: str) -> dict:
    sys.path.insert(0, str(ROOT))
    from thielecpu.hardware.cosim import run_verilog
    r = run_verilog(program, timeout=120)
    if r is None:
        raise RuntimeError("reference simulation produced no result")
    return {"halted": bool(r.get("status") == 2 or r.get("halted")), "err": bool(r["err"]),
            "pc": int(r["pc"]), "mu": int(r["mu"]), "error_code": int(r.get("error_code", 0))}


def parse_report(stdout: str) -> dict:
    lines = [ln for ln in stdout.splitlines() if ln.startswith("{")]
    if not lines:
        raise RuntimeError(f"no report in simulator output:\n{stdout[-2000:]}")
    rep = json.loads(lines[-1])
    if rep.get("timeout") or rep.get("error"):
        raise RuntimeError(f"system simulation failed: {rep}")
    if rep["sync"] != 0xDE or rep["end"] != 0xAD:
        raise RuntimeError(f"report framing wrong: {rep}")
    return {"halted": bool(rep["status"] & 1), "err": bool(rep["status"] & 2),
            "pc": rep["pc"], "mu": rep["mu"], "error_code": rep["error_code"]}


def run_iverilog(sources: list[Path], stream: list[int], work: Path) -> dict:
    hexfile = work / "stream.hex"
    hexfile.write_text("".join(f"{b:02x}\n" for b in stream))
    out = work / "system_tb.vvp"
    subprocess.run(["iverilog", "-g2012", "-o", str(out), str(TB), *map(str, sources)],
                   check=True, capture_output=True, text=True)
    res = subprocess.run(["vvp", str(out), f"+BYTES={hexfile}", f"+N_BYTES={len(stream)}"],
                         check=True, capture_output=True, text=True, timeout=3600)
    return parse_report(res.stdout)


def gate_netlist(work: Path) -> Path:
    net = work / "system_gates.v"
    script = ("read_verilog -sv -DSYNTHESIS " + " ".join(map(str, SOURCES)) + "; "
              "synth -top mkThieleSystem -flatten; opt_clean; "
              f"write_verilog -noattr {net}")
    subprocess.run(["yosys", "-q", "-p", script], check=True)
    return net


def run_verilator(netlist: Path, stream: list[int], work: Path) -> dict:
    hexfile = work / "stream.hex"
    hexfile.write_text("".join(f"{b:02x}\n" for b in stream))
    obj = work / "vgates"
    subprocess.run(["verilator", "--binary", "--timing", "-Wno-fatal", "-O2",
                    "--top-module", "system_tb", "-Mdir", str(obj), str(TB), str(netlist)],
                   check=True, capture_output=True, text=True)
    res = subprocess.run([str(obj / "Vsystem_tb"), f"+BYTES={hexfile}",
                          f"+N_BYTES={len(stream)}"],
                         check=True, capture_output=True, text=True, timeout=3600)
    return parse_report(res.stdout)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--gates", action="store_true", help="also simulate a synthesized gate netlist")
    ap.add_argument("--program", choices=sorted(PROGRAMS), action="append")
    args = ap.parse_args()
    names = args.program or sorted(PROGRAMS)
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        netlist = gate_netlist(work) if args.gates else None
        for name in names:
            prog = PROGRAMS[name]
            stream = program_stream(prog)
            ref = reference(prog)
            rtl = run_iverilog(SOURCES, stream, work)
            results = {"reference": ref, "rtl": rtl}
            if netlist is not None:
                results["gates"] = run_verilator(netlist, stream, work)
            same = all(r == ref for r in results.values())
            print(f"[system-sim] {name}: {'agree' if same else 'DISAGREE'} {json.dumps(results)}")
            failures += 0 if same else 1
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
