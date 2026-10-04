#!/usr/bin/env python3
"""Gate-level simulation of the exact Genesys 2 board top, against the RTL and the VM.

For each test program the script runs three things and compares their final
state field by field:

1. gates: the netlist synthesized for the bitstream (thielecpu/hardware/rtl/
   synth_xc7.ys: synth_xilinx -flatten -abc9 -nodsp, top
   thiele_cpu_top_genesys2), read from its JSON, written back to Verilog and
   simulated with yosys's xilinx cells_sim.v;
2. rtl: the same board top as RTL (thiele_cpu_top_genesys2.v,
   thiele_system.v, thiele_cpu_kami.v, RegFile.v);
3. vm: the Coq-extracted VM (build/thiele_vm.run_vm, backed by the OCaml
   extracted runner, the backend the repo's parity tests use).

Both simulations use one testbench (rtl_harness/testbench/genesys2_top_tb.v)
that drives only the board pins: the 200 MHz differential clock, the reset
button and the UART receive line. The program goes in as serial frames, the
fifteen-byte status report comes back on the UART transmit pin, and then the
testbench reads the architectural state. IBUFDS, MMCME2_BASE and BUFGCE are
behavioural models (rtl_harness/gls/xilinx_board_cells.v); every other cell
is yosys's cells_sim.v model, except block RAM, which uses the pinned
SDP72 functional model checked against Xilinx UNISIM (the Yosys declaration
has no behavior).

What is compared:
- gates against rtl: the report bytes, the LEDs, and every probed state
  field, exactly. A field the RTL has and the netlist does not is listed; if
  it is a required field the run fails.
- each simulation against itself: report pc, mu, error code and status bits
  against the probed registers.
- rtl against itself: the memories reconstructed from their write ports
  against the RegFile arrays read directly (this validates the write-port
  reconstruction the gate run depends on).
- mapped LUT RAM uses physical write-address pins and bank enables. The
  Yosys 0.33 memory_libmap replica ordering is checked across every read
  replica; logical address aliases can contain undriven high bits after
  synthesis. Simultaneous writes to distinct banks are rejected, and the
  program set writes distinct values at addresses 63, 64 and 127.
- rtl against vm: pc, mu, err, the sixteen registers, the 128 data words,
  certified, the module table (live slots against the VM's modules),
  pt_next_id, the morphism table, the witness counters and logic_acc.
- with --power-on, the same comparisons for runs that never press the reset
  button: the gates start from their INIT values and the RTL from every
  register and memory word at 0, so the board wrapper's power-on reset alone
  must bring the system to its reset state.

What is not covered: timing (zero-delay simulation of the pre-place-and-
route netlist; the routed design is not simulated, and nextpnr's timing
report is not sign-off), the real behaviour of the three modelled Xilinx
cells, analogue/timing behavior of the functional RAM model, and anything about a physical board. No board has run this design.

Usage:
  python3 scripts/board_gls.py --netlist-json build/thiele_xc7k325t.json
  python3 scripts/board_gls.py --synthesize          # runs synth_xc7.ys first
  options: --program NAME (repeatable), --long, --no-gates, --no-vm,
           --power-on (also run the board top without pressing reset: the
           gates from their INIT values, and the RTL with every register and
           memory word at 0, as configuration leaves them), --sim iverilog,
           --props (the RTL run also carries formal/cpu_props.vh and
           formal/system_props.vh as simulation checks; any assertion failure
           fails the run, and every cover in REACHABLE_COVERS must be hit by
           at least one program)
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RTL = ROOT / "thielecpu" / "hardware" / "rtl"
TB = ROOT / "rtl_harness" / "testbench" / "genesys2_top_tb.v"
BOARD_CELLS = ROOT / "rtl_harness" / "gls" / "xilinx_board_cells.v"
XILINX_MODELS = BOARD_CELLS.parent / "xilinx"
FORMAL_DIR = ROOT / "formal"
WRAPPER = RTL / "thiele_cpu_top_genesys2.v"
RTL_SOURCES = [RTL / "RegFile.v", RTL / "thiele_cpu_kami.v", RTL / "thiele_system.v", WRAPPER]
TOP = "thiele_cpu_top_genesys2"
CPU = "system.m1."          # flattened name prefix of the CPU inside the top

# ---------------------------------------------------------------------------
# Programs. Each has the cosim dialect the serial loader encodes ("cpu") and
# the VM's text dialect ("vm"); they differ only in the _EXT spellings. The
# serial loader writes instructions only, so no INIT_* lines.
# ---------------------------------------------------------------------------
PROGRAMS: dict[str, dict] = {
    "arith_halt": {  # scripts/system_sim.py
        "cpu": ["LOAD_IMM 1 5 0", "LOAD_IMM 2 7 1", "ADD 3 1 2 3", "HALT 0"],
    },
    "jump_loop": {  # scripts/system_sim.py
        "cpu": ["LOAD_IMM 1 3 0", "LOAD_IMM 2 1 0", "SUB 1 1 2 1", "JNEZ 1 2 0", "HALT 0"],
    },
    "store_load": {  # a data-memory write read back, inside module 1's range
        "cpu": ["PNEW {0,1,2,3,4,5,6,7} 1", "LOAD_IMM 1 42 0", "STORE 5 1 0",
                "LOAD 2 5 0", "HALT 0"],
    },
    "store_load_banks": {  # distinct values across the 64-word LUT-RAM boundary
        "cpu": ["PNEW {" + ",".join(map(str, range(128))) + "} 1",
                "LOAD_IMM 1 42 0", "LOAD_IMM 5 63 0", "STORE 5 1 0", "LOAD 2 5 0",
                "LOAD_IMM 1 43 0", "LOAD_IMM 5 64 0", "STORE 5 1 0", "LOAD 3 5 0",
                "LOAD_IMM 1 44 0", "LOAD_IMM 5 127 0", "STORE 5 1 0", "LOAD 4 5 0",
                "HALT 0"],
    },
    "pnew_overlap_trap": {  # tests/test_pnew_topology_change.py
        "cpu": ["PNEW {0,1,2} 10", "PNEW {1,2,3} 10", "HALT 1"],
    },
    "pnew_past_memory_trap": {  # tests/test_partition_capacity.py
        "cpu": ["PNEW {127,128} 1", "HALT 0"],
    },
    "psplit_pmerge": {
        "cpu": ["PNEW {0,1,2,3} 1", "PSPLIT 1 {0,1} {2,3} 1", "PMERGE 2 3 1", "HALT 0"],
    },
    "compose_two_identities": {  # tests/test_rtl_morph_opcodes.py
        "cpu": ["PNEW {1} 0", "MORPH_ID 0 1 0", "MORPH_ID 0 1 0", "COMPOSE_EXT 0 1 2 0", "HALT 0"],
        "vm": ["PNEW {1} 0", "MORPH_ID 0 1 0", "MORPH_ID 0 1 0", "COMPOSE 0 1 2 0", "HALT 0"],
    },
    "partition_capacity_trap": {  # tests/test_partition_capacity.py, 65 instructions
        "cpu": [f"PNEW {{{i}}} 1" for i in range(63)] + ["PNEW {63} 1", "HALT 0"],
        "long": True,
        "fuel": 200,
    },
}


def random_program(rng) -> list[str]:
    """A serially loadable random program in the opcode set that
    tests/test_cross_layer_adversarial_fuzz.py already compares between the
    VM and the RTL, plus PNEW of random ranges (some overlap and trap) and
    MORPH_ID. Module 1 owns [0, 16) so STORE/LOAD stay inside it."""
    body = ["PNEW {" + ",".join(str(i) for i in range(16)) + "} 1"]
    for _ in range(10):
        op = rng.choice(["LOAD_IMM", "ADD", "SUB", "XFER", "STORE", "LOAD", "XOR_LOAD",
                         "XOR_ADD", "XOR_SWAP", "XOR_RANK", "PNEW", "MORPH_ID"])
        r = lambda: rng.randint(0, 7)
        if op == "LOAD_IMM":
            body.append(f"LOAD_IMM {r()} {rng.randint(0, 255)} {r()}")
        elif op in ("ADD", "SUB"):
            body.append(f"{op} {r()} {r()} {r()} {r()}")
        elif op in ("XFER", "XOR_ADD", "XOR_RANK"):
            body.append(f"{op} {r()} {r()} {r()}")
        elif op == "STORE":
            body.append(f"STORE {rng.randint(0, 15)} {r()} {r()}")
        elif op == "LOAD":
            body.append(f"LOAD {r()} {rng.randint(0, 15)} {r()}")
        elif op == "XOR_LOAD":
            body.append(f"XOR_LOAD {r()} {rng.randint(0, 3)} {r()}")
        elif op == "XOR_SWAP":
            a = r()
            b = rng.choice([x for x in range(8) if x != a])
            body.append(f"XOR_SWAP {a} {b} {r()}")
        elif op == "PNEW":
            base = rng.randint(16, 120)
            n = rng.randint(1, 8)
            body.append("PNEW {" + ",".join(str(base + i) for i in range(n)) + "} " + str(r()))
        else:
            body.append(f"MORPH_ID {r()} 1 {r()}")
    return body + ["HALT 0"]


# ---------------------------------------------------------------------------
# State fields. name -> (width, required). Names are mkModule1 registers.
# ---------------------------------------------------------------------------
REG_FIELDS: dict[str, tuple[int, bool]] = {
    "pc": (32, True), "mu": (32, True), "err": (1, True), "halted": (1, True),
    "error_code": (32, True), "certified": (1, True), "regs": (512, True),
    "ptTable": (2048, True), "ptBases": (2048, True), "pt_next_id": (7, True),
    "active_module": (6, False), "trap_vector": (32, False),
    "morph_next_id": (5, True), "morph_valid_table": (16, True),
    "morph_src_table": (96, True), "morph_dst_table": (96, True),
    "morph_identity_table": (16, True), "morph_coupling_desc_table": (64, False),
    "coupling_desc_next_id": (5, False), "coupling_desc_valid_table": (16, False),
    "coupling_desc_count_table": (80, False), "coupling_desc_base_table": (64, False),
    "coupling_pair_next_id": (5, False), "coupling_pair_valid_table": (16, False),
    "wc_same_00": (32, False), "wc_diff_00": (32, False), "wc_same_01": (32, False),
    "wc_diff_01": (32, False), "wc_same_10": (32, False), "wc_diff_10": (32, False),
    "wc_same_11": (32, False), "wc_diff_11": (32, False),
    "logic_acc": (32, False), "partition_ops": (32, False), "mdl_ops": (32, False),
    "info_gain": (32, False), "csr_status": (32, False), "csr_heap_base": (32, False),
    "mstatus": (32, False), "cert_addr": (32, False),
}
# Memories: name -> (address bits, data bits, depth, required)
MEMORIES: dict[str, tuple[int, int, int, bool]] = {
    "mem": (7, 32, 128, True),
    "imem": (7, 128, 128, True),
    "module_tensors": (8, 32, 256, False),
}
# Covers the program set reaches from reset through the board pins (--props).
# C6 (err rewritten while already set) needs an FSM to write err after an
# earlier error; no program here does that, so it is shown by formal only.
REACHABLE_COVERS = {"C1_pnew_allocates", "C2_psplit_allocates_two", "C3_pmerge_allocates",
                    "C4_partition_overlap_trap", "C5_partition_capacity_trap",
                    "C7_halted_cleared_by_start", "C8_morph_allocates", "C9_mu_charged",
                    "C10_err_rises", "C12_two_live_slots",
                    "D1_load", "D2_start", "D3_report_begins", "D4_report_done"}
LONG_COVERS = {"C11_partition_table_full"}
WITNESS_ORDER = ["wc_same_00", "wc_diff_00", "wc_same_01", "wc_diff_01",
                 "wc_same_10", "wc_diff_10", "wc_same_11", "wc_diff_11"]
BOARD_CELL_TYPES = {"IBUFDS", "MMCME2_BASE", "BUFGCE"}


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(cmd, check=True, capture_output=True, text=True, **kw)
    except subprocess.CalledProcessError as exc:
        # A simulator abort otherwise hides the actual convergence/model error.
        sys.stderr.write((exc.stdout or "")[-12000:])
        sys.stderr.write((exc.stderr or "")[-12000:])
        raise


def yosys_datdir() -> Path:
    try:
        return Path(run(["yosys-config", "--datdir"]).stdout.strip())
    except (OSError, subprocess.CalledProcessError):
        exe = shutil.which("yosys")
        if exe is None:
            raise SystemExit("yosys not found")
        return Path(exe).resolve().parents[1] / "share" / "yosys"


def cells_sim_modules(cells_sim: Path) -> set[str]:
    text = cells_sim.read_text(encoding="utf-8", errors="replace")
    return {m.lstrip("\\") for m in re.findall(r"^\s*module\s+(\\?\S+?)\s*[#(]", text, re.M)}


def gate_cell_sources(work: Path) -> list[Path]:
    """Replace Yosys's empty block-RAM declaration with the tested SDP72 model."""
    original = yosys_datdir() / "xilinx" / "cells_sim.v"
    text = original.read_text(encoding="utf-8")
    text, count = re.subn(r"(?ms)^module RAMB36E1\b.*?^endmodule\b",
                          "// RAMB36E1 behavior is supplied by ramb36_sdp72.v.", text)
    if count != 1:
        raise RuntimeError("expected exactly one Yosys RAMB36E1 declaration")
    filtered = work / "xilinx_cells_sim.v"
    filtered.write_text(text, encoding="utf-8")
    return [BOARD_CELLS, filtered, BOARD_CELLS.parent / "ramb36_sdp72.v", XILINX_MODELS / "glbl.v"]


# ---------------------------------------------------------------------------
# MMCM ratio: the CPU clock is the board clock divided by this integer.
# ---------------------------------------------------------------------------
def _num(value) -> float:
    if isinstance(value, (int, float)):
        return float(value)
    s = str(value).strip().strip('"')
    if re.fullmatch(r"[01]{8,}", s):          # yosys JSON binary-string parameter
        return float(int(s, 2))
    return float(s)


def mmcm_ratio(params: dict) -> int:
    mult = _num(params["CLKFBOUT_MULT_F"])
    div = _num(params.get("DIVCLK_DIVIDE", 1))
    out = _num(params["CLKOUT0_DIVIDE_F"])
    ratio = div * out / mult
    if abs(ratio - round(ratio)) > 1e-9 or round(ratio) % 2:
        raise SystemExit(f"MMCM ratio {ratio} is not an even integer; the clock model needs one")
    return int(round(ratio))


def wrapper_mmcm_params() -> dict:
    text = WRAPPER.read_text(encoding="utf-8")
    out = {}
    for name in ("CLKFBOUT_MULT_F", "DIVCLK_DIVIDE", "CLKOUT0_DIVIDE_F", "CLKIN1_PERIOD"):
        m = re.search(r"\." + name + r"\s*\(\s*([0-9.]+)\s*\)", text)
        if not m:
            raise SystemExit(f"{name} not found in {WRAPPER}")
        out[name] = m.group(1)
    return out


# ---------------------------------------------------------------------------
# Programs to serial byte streams (same framing as scripts/system_sim.py).
# ---------------------------------------------------------------------------
def program_stream(program: list[str]) -> list[int]:
    sys.path.insert(0, str(ROOT))
    from thielecpu.hardware.cosim import program_to_hex
    words, _data, init = program_to_hex(program)
    if init:
        raise ValueError("the serial loader writes instructions only; no INIT_* lines")
    while words and int(words[-1], 16) == 0:
        words.pop()
    if not 0 < len(words) <= 128:
        raise ValueError(f"a program has 1 to 128 instructions, not {len(words)}")
    if len(words) != len(program):
        raise ValueError(f"{len(program)} lines encoded to {len(words)} words")
    out = [len(words) & 0xFF, len(words) >> 8]
    for w in words:
        out.extend(int(w, 16).to_bytes(16, "little"))
    return out


# ---------------------------------------------------------------------------
# Gate netlist and probes.
# ---------------------------------------------------------------------------
class Netlist:
    """The top module of a flattened yosys JSON netlist."""

    def __init__(self, path: Path):
        data = json.loads(path.read_text(encoding="utf-8"))
        if TOP not in data["modules"]:
            raise SystemExit(f"{path}: no module {TOP}")
        self.top = data["modules"][TOP]
        self.nets = {n: v for n, v in self.top["netnames"].items() if not v.get("hide_name", 0)}
        self.bit_name: dict[int, tuple[str, int]] = {}
        for name, v in self.nets.items():
            for i, b in enumerate(v["bits"]):
                if isinstance(b, int):
                    self.bit_name.setdefault(b, (name, i))

    def cell_types(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for c in self.top["cells"].values():
            counts[c["type"]] = counts.get(c["type"], 0) + 1
        return counts

    def find(self, *names: str) -> str | None:
        for n in names:
            if n in self.nets:
                return n
        return None

    def near(self, suffix: str) -> list[str]:
        return sorted(n for n in self.nets if n.endswith(suffix))[:8]

    def bits_expr(self, bits: list) -> str:
        """A Verilog concatenation naming each bit through a public net."""
        parts = []
        for b in reversed(bits):
            if isinstance(b, str):
                parts.append({"0": "1'b0", "1": "1'b1"}.get(b, "1'bx"))
                continue
            if b not in self.bit_name:
                raise KeyError(b)
            name, i = self.bit_name[b]
            width = len(self.nets[name]["bits"])
            off = self.nets[name].get("offset", 0)
            ref = esc(name)
            parts.append(ref if width == 1 else f"{ref}[{i + off}]")
        return "{" + ", ".join(parts) + "}"

    def ram_write_port(self, memory: str, abits: int) -> dict | None:
        """Observe the physical write pins of this memory's mapped banks.

        Synthesis can remove the logical WE/address names, split a LUT RAM
        into independently enabled banks, or map instruction RAM to block
        RAM. Read the primitive inputs directly; do not infer a shared WE
        from data bits that may be shared with another memory.
        """
        cells = [(name, cell) for name, cell in self.top["cells"].items()
                 if name.startswith(CPU + memory + ".arr.")]
        if not cells or any(c.get("hide_name", 0) for _, c in cells):
            return None
        enables, addresses = {}, {}
        lut_banks = {}
        cpu_clock = self.nets["cpu_clk"]["bits"]
        for name, cell in cells:
            conn = cell["connections"]
            ref = esc(name)
            if cell["type"] == "RAM64M":
                suffix = name.removeprefix(CPU + memory + ".arr.")
                if (conn.get("WCLK") != cpu_clock or len(conn.get("WE", [])) != 1
                        or len(conn.get("ADDRD", [])) != 6
                        or not re.fullmatch(r"\d+\.\d+", suffix)):
                    return None
                enables.setdefault(tuple(conn["WE"]), f"{ref}.WE")
                replica, index = map(int, suffix.split("."))
                lut_banks.setdefault(replica, []).append((index, tuple(conn["WE"])))
                addresses.setdefault(tuple(conn["ADDRD"]), f"{ref}.ADDRD")
            elif cell["type"] == "RAMB36E1":
                params = cell["parameters"]
                if (params.get("RAM_MODE") != "SDP"
                        or int(params.get("WRITE_WIDTH_B", "0"), 2) != 72
                        or int(params.get("WRITE_WIDTH_A", "0"), 2) != 0
                        or conn.get("CLKBWRCLK") != cpu_clock
                        or conn.get("ENBWREN") != ["1"]):
                    return None
                # SDP72 uses address bits 6..14. Unused high address bits
                # must be zero; all active byte enables must agree.
                addr = conn.get("ADDRBWRADDR", [])
                we = conn.get("WEBWE", [])
                active = set(we) - {"0"}
                if (len(addr) != 16 or abits > 9
                        or any(b != "0" for b in addr[:6] + addr[6 + abits:])
                        or len(active) != 1 or "x" in active or "z" in active):
                    return None
                enables.setdefault(tuple(sorted(active, key=str)), f"(|{ref}.WEBWE)")
                addresses.setdefault(tuple(addr[6:6 + abits]),
                                     f"{ref}.ADDRBWRADDR[{5 + abits}:6]")
            else:
                return None
        if len(addresses) > 1:
            return None
        conflict = None
        if lut_banks:
            if any(c["type"] != "RAM64M" for _, c in cells) or not 6 <= abits <= 8:
                return None
            # Yosys 0.33 memory_libmap emit(): arr.<read-replica>.<data-replica>.
            # gen_swizzle orders data replicas by increasing high address,
            # then by data column. All read replicas must agree on that order.
            # The old logical ADDR_IN high bits can survive as UNDRIVEN wires;
            # the bank enables, rather than those names, locate the actual write.
            orders = []
            for replica in sorted(lut_banks):
                order = []
                for _, we_bits in sorted(lut_banks[replica]):
                    if not order or we_bits != order[-1]:
                        order.append(we_bits)
                orders.append(order)
            banks = orders[0]
            if (len(banks) != 1 << (abits - 6) or len(set(banks)) != len(banks)
                    or any(order != banks for order in orders)):
                return None
            bank_we = [enables[bits] for bits in banks]
            low = next(iter(addresses.values()))
            high = ["(" + " | ".join(we for n, we in enumerate(bank_we) if n & (1 << bit)) + ")"
                    for bit in reversed(range(abits - 6))]
            addr_expr = "{" + ", ".join([*high, low]) + "}" if high else low
            addresses = {(): addr_expr}
            conflict = " | ".join(f"({a} && {b})" for i, a in enumerate(bank_we)
                                  for b in bank_we[i + 1:]) or None
        return {"WE": "(" + " | ".join(enables.values()) + ")",
                "ADDR": next(iter(addresses.values()), None), "CONFLICT": conflict}


def esc(name: str) -> str:
    return name if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", name) else f"\\{name} "


def gate_probes(net: Netlist) -> tuple[list[str], dict, list[str]]:
    """Wires to add inside the netlist's top module, the probe map, and absences."""
    wires, probes, missing = [], {}, []
    clk = net.find("cpu_clk")
    if clk is None:
        raise SystemExit("netlist has no net cpu_clk")
    wires.append(f"wire gls_cpu_clk = {esc(clk)};")
    probes["clk"] = "dut.gls_cpu_clk"
    for field, (width, required) in REG_FIELDS.items():
        name = net.find(CPU + field)
        if name is None:
            missing.append(field + (" (required)" if required else ""))
            continue
        w = len(net.nets[name]["bits"])
        wires.append(f"wire [{w - 1}:0] gls_{field} = {esc(name)};")
        probes[field] = (f"dut.gls_{field}", w)
    for mem, (abits, dbits, depth, required) in MEMORIES.items():
        we = net.find(f"{CPU}{mem}$WE", f"{CPU}{mem}.WE")
        addr = net.find(f"{CPU}{mem}$ADDR_IN", f"{CPU}{mem}.ADDR_IN")
        din = net.find(f"{CPU}{mem}$D_IN", f"{CPU}{mem}.D_IN")
        we_expr = esc(we) if we else None
        addr_expr = esc(addr) if addr else None
        port = net.ram_write_port(mem, abits)
        if port is not None:
            we_expr = port["WE"]
            addr_expr = port["ADDR"] or addr_expr
            if port["CONFLICT"]:
                wires.append(f'always @(posedge gls_cpu_clk) if ({port["CONFLICT"]}) '
                             f'$fatal(1, "{mem}: multiple physical write banks enabled");')
        if we_expr is None or addr_expr is None or din is None:
            missing.append(f"{mem} write port" + (" (required)" if required else ""))
            continue
        wires.append(f"wire gls_{mem}_we = {we_expr};")
        wires.append(f"wire [{abits - 1}:0] gls_{mem}_addr = {addr_expr};")
        wires.append(f"wire [{dbits - 1}:0] gls_{mem}_din = {esc(din)};")
        probes[mem] = {"we": f"dut.gls_{mem}_we", "addr": f"dut.gls_{mem}_addr",
                       "din": f"dut.gls_{mem}_din", "depth": depth, "dbits": dbits}
    return wires, probes, missing


def rtl_probes() -> dict:
    probes: dict = {"clk": "dut.cpu_clk"}
    for field, (width, _req) in REG_FIELDS.items():
        probes[field] = (f"dut.system.m1.{field}", width)
    for mem, (_a, dbits, depth, _req) in MEMORIES.items():
        probes[mem] = {"we": f"dut.system.m1.{mem}$WE", "addr": f"dut.system.m1.{mem}$ADDR_IN",
                       "din": f"dut.system.m1.{mem}$D_IN", "depth": depth, "dbits": dbits,
                       "direct": f"dut.system.m1.{mem}.arr"}
    return probes


def probes_include(probes: dict) -> str:
    """gls_probes.vh: clock macro, write-port shadows, and task dump_state."""
    out = [f"`define GLS_CPU_CLK {probes['clk']}"]
    dump = ["task dump_state;", "  integer k;", "  begin", '    $write("{");']
    first = True
    for key, p in probes.items():
        if key == "clk" or isinstance(p, dict):
            continue
        ref, _w = p
        sep = "" if first else ", "
        dump.append(f'    $write("{sep}\\"{key}\\": \\"%h\\"", {ref});')
        first = False
    for mem, p in probes.items():
        if not isinstance(p, dict):
            continue
        depth, dbits = p["depth"], p["dbits"]
        out += [f"reg [{dbits - 1}:0] gls_sh_{mem} [0:{depth - 1}];",
                f"reg gls_wr_{mem} [0:{depth - 1}];",
                "integer gls_i_" + mem + ";",
                f"initial for (gls_i_{mem} = 0; gls_i_{mem} < {depth}; gls_i_{mem} = gls_i_{mem} + 1) gls_wr_{mem}[gls_i_{mem}] = 1'b0;",
                f"always @(posedge `GLS_CPU_CLK) if ({p['we']} === 1'b1) begin",
                f"  gls_sh_{mem}[{p['addr']}] <= {p['din']};",
                f"  gls_wr_{mem}[{p['addr']}] <= 1'b1;",
                "end"]
        for kind, arr in (("shadow", f"gls_sh_{mem}"), ("direct", p.get("direct"))):
            if arr is None:
                continue
            label = f"{mem}" if kind == "shadow" else f"{mem}_direct"
            sep = "" if first else ", "
            dump.append(f'    $write("{sep}\\"{label}\\": [");')
            dump.append(f"    for (k = 0; k < {depth}; k = k + 1) begin")
            if kind == "shadow":
                dump.append(f'      if (!gls_wr_{mem}[k]) $write("%s\\"unwritten\\"", k ? ", " : "");')
                dump.append(f'      else $write("%s\\"%h\\"", k ? ", " : "", {arr}[k]);')
            else:
                dump.append(f'      $write("%s\\"%h\\"", k ? ", " : "", {arr}[k]);')
            dump.append("    end")
            dump.append('    $write("]");')
            first = False
    dump += ['    $write("}");', "  end", "endtask"]
    return "\n".join(out + dump) + "\n"


def write_gate_verilog(json_path: Path, work: Path) -> tuple[Path, Netlist, dict, list[str]]:
    net = Netlist(json_path)
    gv = work / "gls_netlist.v"
    run(["yosys", "-q", "-p", f"read_json {json_path}; write_verilog -noattr {gv}"])
    wires, probes, missing = gate_probes(net)
    text = gv.read_text(encoding="utf-8")
    m = re.search(r"^module\s+" + TOP + r"\b.*?^endmodule", text, re.S | re.M)
    if not m:
        raise SystemExit("top module not found in the written netlist")
    block = "\n  // Added by scripts/board_gls.py: probe wires that only read existing nets.\n  " \
            + "\n  ".join(wires) + "\n"
    end = m.end() - len("endmodule")
    gv.write_text(text[:end] + block + text[end:], encoding="utf-8")
    return gv, net, probes, missing


# ---------------------------------------------------------------------------
# Simulation.
# ---------------------------------------------------------------------------
_INIT_REGION = re.compile(r"`ifdef BSV_NO_INITIAL_BLOCKS.*?`endif // BSV_NO_INITIAL_BLOCKS", re.S)


def configuration_state_copy(src: Path, dst: Path) -> None:
    """Copy an extracted Verilog file with its initial blocks set to 0.

    Bluespec's simulation initial blocks fill registers and RegFile arrays with
    the 'hAAAA pattern. Configuration leaves every flip-flop and LUT-RAM bit
    of the chip at 0, so the power-on run starts from 0 instead.
    """
    text = src.read_text(encoding="utf-8")
    regions = _INIT_REGION.findall(text)
    if not regions:
        raise ValueError(f"{src.name}: no Bluespec initial block")

    def zero(m: re.Match) -> str:
        body = re.sub(r"(\d+)'h[0-9A-Fa-f]+", r"\1'h0", m.group(0))
        return body.replace("{((data_width + 1)/2){2'b10}}", "{data_width{1'b0}}")

    out = _INIT_REGION.sub(zero, text)
    if "'hA" in "".join(_INIT_REGION.findall(out)) or "2'b10" in "".join(_INIT_REGION.findall(out)):
        raise ValueError(f"{src.name}: an initial value was not set to 0")
    dst.write_text(out, encoding="utf-8")


def build_sim(kind: str, sources: list[Path], defines: dict, work: Path, sim: str) -> list[str]:
    inc = work / kind
    inc.mkdir(exist_ok=True)
    dflags = [f"-D{k}={v}" for k, v in defines.items()]
    if sim == "verilator":
        obj = work / f"obj_{kind}"
        run(["verilator", "--binary", "-j", "0", "--timing", "-Wno-fatal", "-O2", "--x-assign", "0",
             "--x-initial", "0", "--top-module", "genesys2_top_tb", "-Mdir", str(obj),
             f"-I{inc}", *dflags, str(TB), *map(str, sources)], timeout=7200)
        return [str(obj / "Vgenesys2_top_tb")]
    out = work / f"{kind}.vvp"
    run(["iverilog", "-g2012", "-o", str(out), "-I", str(inc), *dflags, str(TB),
         *map(str, sources)], timeout=3600)
    return ["vvp", str(out)]


def simulate(binary: list[str], stream: list[int], work: Path, extra: list[str]) -> dict:
    hexfile = work / "stream.hex"
    hexfile.write_text("".join(f"{b:02x}\n" for b in stream), encoding="utf-8")
    res = run([*binary, f"+BYTES={hexfile}", f"+N_BYTES={len(stream)}", *extra], timeout=7200)
    lines = [ln for ln in res.stdout.splitlines() if ln.startswith("{")]
    if not lines:
        raise RuntimeError(f"no result line:\n{res.stdout[-2000:]}")
    out = json.loads(lines[-1])
    if out.get("timeout") or out.get("error"):
        raise RuntimeError(f"simulation failed: {out}")
    events = [json.loads(ln) for ln in lines[:-1]]
    out["covers"] = sorted({e["cover"] for e in events if "cover" in e})
    out["assert_fail"] = sorted({e["assert_fail"] for e in events if "assert_fail" in e})
    return out


def hexval(s: str) -> int | None:
    return None if re.search(r"[xXzZ]", s) else int(s, 16)


def decode_state(raw: dict) -> dict:
    st: dict = {}
    for k, v in raw.items():
        if isinstance(v, list):
            st[k] = [None if x == "unwritten" else hexval(x) for x in v]
        else:
            st[k] = hexval(v)
    return st


def self_check(name: str, out: dict) -> list[str]:
    """Report bytes against the probed registers of the same run."""
    errs = []
    rep, st = out["report"], decode_state(out["state"])
    if rep["sync"] != 0xDE or rep["end"] != 0xAD:
        errs.append(f"{name}: report framing {rep['sync']:#x}..{rep['end']:#x}")
    for f in ("pc", "mu", "error_code"):
        if f in st and st[f] != rep[f]:
            errs.append(f"{name}: report {f}={rep[f]} but register holds {st[f]}")
    for bit, f in ((1, "halted"), (2, "err"), (4, "certified")):
        if f in st and bool(rep["status"] & bit) != bool(st[f]):
            errs.append(f"{name}: report status bit {f} disagrees with the register")
    for f in ("halted", "err"):
        if f in st and bool(out["leds"][f]) != bool(st[f]):
            errs.append(f"{name}: LED {f} disagrees with the register")
    for k, v in st.items():
        if k.endswith("_direct"):
            continue
        if v is None or (isinstance(v, list) and any(x is None for x in v)):
            errs.append(f"{name}: {k} has undefined or never-written values")
    return errs


def slots(word: int, n: int, w: int) -> list[int]:
    return [(word >> (i * w)) & ((1 << w) - 1) for i in range(n)]


def cpu_view(st: dict) -> dict:
    sizes, bases = slots(st["ptTable"], 64, 32), slots(st["ptBases"], 64, 32)
    nxt = st["pt_next_id"]
    modules = {i: list(range(bases[i], bases[i] + sizes[i]))
               for i in range(64) if i < nxt and sizes[i] != 0}
    valid = slots(st["morph_valid_table"], 16, 1)
    src, dst = slots(st["morph_src_table"], 16, 6), slots(st["morph_dst_table"], 16, 6)
    ident = slots(st["morph_identity_table"], 16, 1)
    morphs = {j: (src[j], dst[j], bool(ident[j])) for j in range(16) if valid[j]}
    view = {"pc": st["pc"], "mu": st["mu"], "err": bool(st["err"]),
            "certified": bool(st["certified"]), "regs": slots(st["regs"], 16, 32),
            "mem": st["mem"], "pt_next_id": nxt, "modules": modules,
            "morph_next_id": st["morph_next_id"], "morphisms": morphs}
    if all(w in st for w in WITNESS_ORDER):
        view["witness"] = [st[w] for w in WITNESS_ORDER]
    if "logic_acc" in st:
        view["logic_acc"] = st["logic_acc"]
    return view


def vm_view(program: list[str], fuel: int) -> dict:
    sys.path.insert(0, str(ROOT))
    from build.thiele_vm import run_vm, _runner_available
    if not _runner_available():
        raise SystemExit("the OCaml extracted runner (build/extracted_vm_runner) is not built")
    s = run_vm(program, fuel=fuel)
    g = s.graph
    mem = list(s.mem) + [0] * (128 - len(s.mem))
    return {"pc": s.pc, "mu": s.mu, "err": bool(s.err), "certified": bool(s.certified),
            "regs": list(s.regs[:16]), "mem": mem[:128], "pt_next_id": g.pg_next_id,
            "modules": {mid: list(ms.module_region) for mid, ms in g.pg_modules},
            "morph_next_id": g.pg_next_morph_id,
            "morphisms": {mid: (m.morph_source, m.morph_target, bool(m.morph_is_identity))
                          for mid, m in g.pg_morphisms},
            "witness": list(s.witness), "logic_acc": s.logic_acc}


def diff(a: dict, b: dict, la: str, lb: str, keys=None) -> list[str]:
    errs = []
    for k in keys or sorted(set(a) & set(b)):
        if k in a and k in b and a[k] != b[k]:
            errs.append(f"{k}: {la}={a[k]!r} {lb}={b[k]!r}")
    return errs


def shard_programs(names: list[str], count: int) -> list[list[str]]:
    """Balance serial traffic without changing any program or comparison."""
    if not 1 <= count <= len(names):
        raise ValueError("shard count must be between one and the program count")
    groups = [[] for _ in range(count)]
    loads = [0] * count
    for name in sorted(names, key=lambda n: -len(program_stream(PROGRAMS[n]["cpu"]))):
        index = min(range(count), key=lambda i: loads[i])
        groups[index].append(name)
        loads[index] += len(program_stream(PROGRAMS[name]["cpu"]))
    return groups


def combine_reports(paths: list[Path], names: list[str], expected_covers: set[str]) -> dict:
    """Fail closed on missing, duplicate, incomplete or inconsistent shards."""
    programs, covers, digests, shards = {}, set(), set(), set()
    for path in paths:
        report = json.loads(path.read_text(encoding="utf-8"))
        if not report.get("complete") or not report.get("ok"):
            raise ValueError(f"incomplete or failed report: {path}")
        if not report.get("power_on") or not report.get("props") or not report.get("vm"):
            raise ValueError(f"report omitted required comparisons: {path}")
        shard = report.get("shard_index")
        if shard in shards or report.get("shard_count") != len(paths):
            raise ValueError(f"duplicate or inconsistent shard: {path}")
        shards.add(shard)
        digests.add(report.get("netlist_sha256"))
        if set(report["programs"]) != set(report["planned_programs"]):
            raise ValueError(f"missing planned programs: {path}")
        for name, result in report["programs"].items():
            if name in programs or not result.get("ok") or result.get("errors"):
                raise ValueError(f"duplicate or failed program: {name}")
            required = {"rtl_report", "rtl_power_on_report", "gates_report",
                        "gates_power_on_report", "compared_with_vm"}
            if not required <= result.keys() or not result["compared_with_vm"]:
                raise ValueError(f"missing comparison results: {name}")
            programs[name] = result
        covers.update(report.get("covers_hit", []))
    if shards != set(range(len(paths))) or len(digests) != 1 or None in digests:
        raise ValueError("missing shards or inconsistent netlists")
    if set(programs) != set(names):
        raise ValueError("combined program set differs from the requested suite")
    if expected_covers - covers:
        raise ValueError(f"covers not reached: {sorted(expected_covers - covers)}")
    return {"complete": True, "ok": True, "programs": programs,
            "covers_hit": sorted(covers), "netlist_sha256": digests.pop()}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    src = ap.add_mutually_exclusive_group()
    src.add_argument("--netlist-json", type=Path, help="the JSON netlist the bitstream was built from")
    src.add_argument("--synthesize", action="store_true", help="run synth_xc7.ys to make it")
    ap.add_argument("--no-gates", action="store_true")
    ap.add_argument("--no-vm", action="store_true")
    ap.add_argument("--power-on", action="store_true",
                    help="also run the gates without pressing reset (state as configuration leaves it)")
    ap.add_argument("--long", action="store_true", help="include the 65-instruction capacity program")
    ap.add_argument("--program", action="append", choices=sorted(PROGRAMS))
    ap.add_argument("--random", type=int, default=0, metavar="N",
                    help="also run N random programs (gates against RTL against VM)")
    ap.add_argument("--seed", type=int, default=20261003)
    ap.add_argument("--shard-count", type=int, default=1)
    ap.add_argument("--shard-index", type=int, default=0)
    ap.add_argument("--combine-reports", type=Path, nargs="+")
    ap.add_argument("--sim", choices=["verilator", "iverilog"], default="verilator")
    ap.add_argument("--props", action="store_true",
                    help="run the property files as simulation checks in the RTL run")
    ap.add_argument("--report", type=Path, help="write a JSON report here")
    args = ap.parse_args()

    names = args.program or [n for n, p in PROGRAMS.items() if args.long or not p.get("long")]
    if args.random:
        import random
        rng = random.Random(args.seed)
        for k in range(args.random):
            PROGRAMS[f"random_{args.seed}_{k}"] = {"cpu": random_program(rng)}
            names.append(f"random_{args.seed}_{k}")
    expected = REACHABLE_COVERS | (LONG_COVERS if args.long and not args.program else set())
    if args.combine_reports:
        summary = combine_reports(args.combine_reports, names, expected)
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        print(f"[board-gls] all {len(names)} programs and {len(expected)} coverage targets passed")
        return 0
    if not 0 <= args.shard_index < args.shard_count:
        ap.error("shard index must be in [0, shard count)")
    names = shard_programs(names, args.shard_count)[args.shard_index]
    ratio = mmcm_ratio(wrapper_mmcm_params())
    defines = {"GLS_MMCM_RATIO": ratio}
    failures: list[str] = []
    summary: dict = {"mmcm_ratio": ratio, "programs": {},
                     "planned_programs": list(names), "complete": False,
                     "shard_index": args.shard_index, "shard_count": args.shard_count,
                     "power_on": args.power_on, "props": args.props, "vm": not args.no_vm}

    def save_progress():
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    save_progress()

    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        rtl_inc = work / "rtl"
        rtl_inc.mkdir()
        (rtl_inc / "gls_probes.vh").write_text(probes_include(rtl_probes()), encoding="utf-8")
        rtl_sources = list(RTL_SOURCES)
        if args.props:
            sys.path.insert(0, str(ROOT / "scripts"))
            from formal_prepare import with_include
            for vh in ("cpu_props.vh", "system_props.vh"):
                shutil.copyfile(FORMAL_DIR / vh, rtl_inc / vh)
            kami = work / "thiele_cpu_kami_props.v"
            kami.write_text(with_include(RTL / "thiele_cpu_kami.v", "mkModule1", "cpu_props.vh"),
                            encoding="utf-8")
            system = work / "thiele_system_props.v"
            system.write_text(with_include(RTL / "thiele_system.v", "mkThieleSystem", "system_props.vh"),
                              encoding="utf-8")
            rtl_sources = [RTL / "RegFile.v", kami, system, WRAPPER]
        rtl_bin = build_sim("rtl", [BOARD_CELLS, *rtl_sources], defines, work, args.sim)
        rtl_po_bin = None
        if args.power_on:
            po_dir = work / "power_on_src"
            po_dir.mkdir()
            po_sources = []
            for src in RTL_SOURCES:
                if src == WRAPPER:
                    po_sources.append(src)
                    continue
                configuration_state_copy(src, po_dir / src.name)
                po_sources.append(po_dir / src.name)
            (work / "rtl_power_on").mkdir()
            (work / "rtl_power_on" / "gls_probes.vh").write_text(probes_include(rtl_probes()),
                                                                 encoding="utf-8")
            rtl_po_bin = build_sim("rtl_power_on", [BOARD_CELLS, *po_sources], defines, work, args.sim)
        covers_hit: set[str] = set()

        gate_bin = None
        if not args.no_gates:
            json_path = args.netlist_json
            if args.synthesize or json_path is None:
                run(["yosys", "-ql", str(work / "yosys_xc7.log"), "synth_xc7.ys"], cwd=RTL,
                    timeout=7200)
                json_path = ROOT / "build" / "thiele_xc7k325t.json"
            summary["netlist_sha256"] = hashlib.sha256(json_path.read_bytes()).hexdigest()
            gv, net, probes, missing = write_gate_verilog(json_path, work)
            types = net.cell_types()
            known = cells_sim_modules(yosys_datdir() / "xilinx" / "cells_sim.v") | BOARD_CELL_TYPES
            unknown = sorted(t for t in types if t not in known)
            if unknown:
                raise SystemExit(f"netlist cells with no simulation model: {unknown}")
            for t in BOARD_CELL_TYPES:
                if types.get(t) != 1:
                    raise SystemExit(f"expected exactly one {t} in the netlist, found {types.get(t, 0)}")
            for cell in net.top["cells"].values():
                if cell["type"] != "RAMB36E1":
                    continue
                conn = cell["connections"]
                if conn["CLKARDCLK"] != conn["CLKBWRCLK"]:
                    raise SystemExit("RAMB36E1 simulation requires a common read/write clock")
                for port in ("WEA", "REGCEAREGCE", "REGCEB", "RSTRAMARSTRAM", "RSTRAMB",
                             "RSTREGARSTREG", "RSTREGB", "CASCADEINA", "CASCADEINB",
                             "INJECTDBITERR", "INJECTSBITERR"):
                    if any(bit != "0" for bit in conn.get(port, [])):
                        raise SystemExit(f"unsupported active RAMB36E1 pin: {port}")
            mmcm = next(c for c in net.top["cells"].values() if c["type"] == "MMCME2_BASE")
            if mmcm_ratio(mmcm["parameters"]) != ratio:
                raise SystemExit("the netlist's MMCM parameters differ from the wrapper source")
            summary["cell_types"] = types
            summary["absent_in_netlist"] = missing
            print(f"[board-gls] netlist {summary['netlist_sha256'][:16]}: {sum(types.values())} cells; "
                  f"absent fields: {missing or 'none'}", flush=True)
            req = [m for m in missing if m.endswith("(required)")]
            if req:
                raise SystemExit(f"required fields not observable in the netlist: {req}")
            (work / "gates").mkdir()
            (work / "gates" / "gls_probes.vh").write_text(probes_include(probes), encoding="utf-8")
            gate_defines = {**defines, "GLS_XILINX_BRAM": 1}
            gate_bin = build_sim("gates", [*gate_cell_sources(work), gv], gate_defines, work, args.sim)

        for name in names:
            summary["current_program"] = name
            save_progress()
            print(f"[board-gls] starting {name}", flush=True)
            prog = PROGRAMS[name]
            stream = program_stream(prog["cpu"])
            errs: list[str] = []
            rtl = simulate(rtl_bin, stream, work, [])
            errs += self_check("rtl", rtl)
            errs += [f"rtl: property {a} failed" for a in rtl["assert_fail"]]
            covers_hit |= set(rtl["covers"])
            rst = decode_state(rtl["state"])
            for mem in MEMORIES:
                if f"{mem}_direct" in rst and rst[f"{mem}_direct"] != rst.get(mem):
                    errs.append(f"rtl: {mem} write-port reconstruction differs from the RegFile array")
            result = {"rtl_report": rtl["report"]}
            if rtl_po_bin is not None:
                po = simulate(rtl_po_bin, stream, work, ["+NO_RESET_PRESS"])
                errs += self_check("rtl_power_on", po)
                pst = decode_state(po["state"])
                rcmp = {k: v for k, v in rst.items() if not k.endswith("_direct")}
                pcmp = {k: v for k, v in pst.items() if not k.endswith("_direct")}
                errs += ["rtl_power_on vs rtl: " + e for e in diff(rcmp, pcmp, "rtl", "rtl_power_on")]
                if po["report"] != rtl["report"] or po["leds"] != rtl["leds"]:
                    errs.append(f"rtl_power_on vs rtl: report or LEDs differ: {po['report']} {po['leds']}")
                result["rtl_power_on_report"] = po["report"]
            if name.startswith("random_"):
                result["program"] = prog["cpu"]
            if gate_bin is not None:
                for label, extra in (("gates", []),) + ((("gates_power_on", ["+NO_RESET_PRESS"]),)
                                                         if args.power_on else ()):
                    g = simulate(gate_bin, stream, work, extra)
                    errs += self_check(label, g)
                    gst = decode_state(g["state"])
                    rcmp = {k: v for k, v in rst.items() if not k.endswith("_direct")}
                    errs += [f"{label} vs rtl: " + e for e in diff(rcmp, gst, "rtl", label)]
                    if g["report"] != rtl["report"] or g["leds"] != rtl["leds"]:
                        errs.append(f"{label} vs rtl: report or LEDs differ: {g['report']} {g['leds']}")
                    result[f"{label}_report"] = g["report"]
            if not args.no_vm:
                vm = vm_view(prog.get("vm", prog["cpu"]), prog.get("fuel", 1000))
                cv = cpu_view(rst)
                errs += ["vm vs rtl: " + e for e in diff(vm, cv, "vm", "rtl")]
                result["compared_with_vm"] = sorted(set(vm) & set(cv))
                result["rtl_view"] = {k: v for k, v in cv.items() if k != "mem"}
                result["vm_view"] = {k: v for k, v in vm.items() if k != "mem"}
            summary["programs"][name] = {"ok": not errs, "errors": errs, **result}
            save_progress()
            print(f"[board-gls] {name}: {'agree' if not errs else 'DISAGREE'}", flush=True)
            for e in errs:
                print(f"    {e}", flush=True)
            failures += errs

    if args.props:
        expected = REACHABLE_COVERS | (LONG_COVERS if args.long and not args.program else set())
        missed = sorted(expected - covers_hit)
        summary["covers_hit"] = sorted(covers_hit)
        print(f"[board-gls] covers hit from reset: {sorted(covers_hit)}")
        if args.program is None and args.shard_count == 1 and missed:
            failures.append(f"covers not reached by the program set: {missed}")
            print(f"    covers not reached: {missed}")
    summary["complete"] = True
    summary["ok"] = not failures
    summary.pop("current_program", None)
    save_progress()
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
