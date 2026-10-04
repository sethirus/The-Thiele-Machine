"""The board-top simulation harness and the formal property copies.

The pure-Python parts of scripts/board_gls.py and scripts/formal_prepare.py
are checked without any simulator. test_board_top_rtl_matches_vm runs the
board top's RTL (wrapper, loader, status report and CPU) under iverilog on
every short program and compares it with the extracted VM field by field;
the gate netlist runs only in CI (Full), after the bitstream job.
"""
from __future__ import annotations

import json
import random
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import board_gls  # noqa: E402
import formal_prepare  # noqa: E402


def test_shards_partition_the_entire_program_suite_once():
    names = list(board_gls.PROGRAMS)
    groups = board_gls.shard_programs(names, 4)
    assert sorted(n for group in groups for n in group) == sorted(names)
    assert all(groups)
    assert groups == board_gls.shard_programs(names, 4)


def _shard_reports(tmp_path):
    paths = []
    for i, name in enumerate(["arith_halt", "jump_loop"]):
        result = {"ok": True, "errors": [], "compared_with_vm": ["pc"],
                  **{k: {} for k in ["rtl_report", "rtl_power_on_report",
                                     "gates_report", "gates_power_on_report"]}}
        report = {"complete": True, "ok": True, "power_on": True, "props": True,
                  "vm": True, "shard_index": i, "shard_count": 2,
                  "netlist_sha256": "a" * 64, "planned_programs": [name],
                  "programs": {name: result}, "covers_hit": [f"cover{i}"]}
        path = tmp_path / f"{i}.json"
        path.write_text(json.dumps(report), encoding="utf-8")
        paths.append(path)
    return paths


def test_combined_shards_require_all_programs_and_union_of_covers(tmp_path):
    paths = _shard_reports(tmp_path)
    result = board_gls.combine_reports(paths, ["arith_halt", "jump_loop"], {"cover0", "cover1"})
    assert result["ok"] and len(result["programs"]) == 2


@pytest.mark.parametrize("damage", ["incomplete", "failed", "missing_program", "duplicate",
                                   "wrong_netlist", "missing_cover", "no_power_on", "no_vm",
                                   "missing_result"])
def test_combined_shards_reject_missing_evidence(tmp_path, damage):
    paths = _shard_reports(tmp_path)
    report = json.loads(paths[1].read_text(encoding="utf-8"))
    if damage == "incomplete": report["complete"] = False
    elif damage == "failed": report["programs"]["jump_loop"]["ok"] = False
    elif damage == "missing_program": report["programs"] = {}
    elif damage == "duplicate": report["shard_index"] = 0
    elif damage == "wrong_netlist": report["netlist_sha256"] = "b" * 64
    elif damage == "missing_cover": report["covers_hit"] = []
    elif damage == "no_power_on": report["power_on"] = False
    elif damage == "no_vm": report["vm"] = False
    elif damage == "missing_result": del report["programs"]["jump_loop"]["gates_power_on_report"]
    paths[1].write_text(json.dumps(report), encoding="utf-8")
    with pytest.raises(ValueError):
        board_gls.combine_reports(paths, ["arith_halt", "jump_loop"], {"cover0", "cover1"})


def test_wrapper_mmcm_divides_the_board_clock_by_ten():
    assert board_gls.mmcm_ratio(board_gls.wrapper_mmcm_params()) == 10


@pytest.mark.parametrize("params", [
    {"CLKFBOUT_MULT_F": "5.000", "DIVCLK_DIVIDE": 1, "CLKOUT0_DIVIDE_F": "50.000"},
    {"CLKFBOUT_MULT_F": 5.0, "DIVCLK_DIVIDE": "00000000000000000000000000000001",
     "CLKOUT0_DIVIDE_F": 50.0},
])
def test_mmcm_ratio_reads_netlist_parameter_forms(params):
    assert board_gls.mmcm_ratio(params) == 10


def test_mmcm_ratio_rejects_a_ratio_the_model_cannot_produce():
    with pytest.raises(SystemExit):
        board_gls.mmcm_ratio({"CLKFBOUT_MULT_F": "5", "DIVCLK_DIVIDE": 1, "CLKOUT0_DIVIDE_F": "7.5"})


@pytest.mark.parametrize("name", sorted(board_gls.PROGRAMS))
def test_every_program_is_serially_loadable(name):
    prog = board_gls.PROGRAMS[name]["cpu"]
    stream = board_gls.program_stream(prog)
    assert stream[0] + 256 * stream[1] == len(prog)
    assert len(stream) == 2 + 16 * len(prog)


def test_random_programs_are_reproducible_and_loadable():
    a = [board_gls.random_program(random.Random(7)) for _ in range(3)]
    b = [board_gls.random_program(random.Random(7)) for _ in range(3)]
    assert a == b
    for prog in a:
        assert prog[-1] == "HALT 0"
        board_gls.program_stream(prog)


def test_probe_include_names_every_required_field():
    text = board_gls.probes_include(board_gls.rtl_probes())
    for field, (_w, required) in board_gls.REG_FIELDS.items():
        if required:
            assert f"dut.system.m1.{field}" in text
    for mem in board_gls.MEMORIES:
        assert f"dut.system.m1.{mem}$WE" in text
        assert f"dut.system.m1.{mem}.arr" in text


def test_gate_probes_from_a_flattened_netlist(tmp_path):
    def net(bits):
        return {"hide_name": 0, "bits": bits}
    netnames = {"cpu_clk": net([2])}
    nxt = 10
    for field, (width, _r) in board_gls.REG_FIELDS.items():
        netnames["system.m1." + field] = net(list(range(nxt, nxt + width)))
        nxt += width
    for mem, (abits, dbits, _d, _r) in board_gls.MEMORIES.items():
        for port, w in (("$WE", 1), ("$ADDR_IN", abits), ("$D_IN", dbits)):
            netnames[f"system.m1.{mem}{port}"] = net(list(range(nxt, nxt + w)))
            nxt += w
    tmp = tmp_path / "netlist.json"
    tmp.write_text(json.dumps({"modules": {board_gls.TOP: {"netnames": netnames, "cells": {}}}}))
    wires, probes, missing = board_gls.gate_probes(board_gls.Netlist(tmp))
    assert missing == []
    assert "wire [31:0] gls_pc = \\system.m1.pc ;" in wires
    assert probes["mem"]["we"] == "dut.gls_mem_we"


def mapped_memory_netlist(tmp_path, cells):
    path = tmp_path / "mapped.json"
    path.write_text(json.dumps({"modules": {board_gls.TOP: {
        "netnames": {"cpu_clk": {"bits": [2], "hide_name": 0}}, "cells": cells}}}))
    return board_gls.Netlist(path)


def test_banked_lut_ram_observes_each_bank_enable(tmp_path):
    cells = {f"system.m1.mem.arr.0.{bank}": {
        "type": "RAM64M", "hide_name": 0,
        "connections": {"WE": [10 + bank], "WCLK": [2], "ADDRD": list(range(30, 36))}}
        for bank in range(2)}
    # An unrelated RAM with the same data must not contribute its write enable.
    cells["system.m1.imem.arr.0.0"] = {
        "type": "RAM64M", "hide_name": 0,
        "connections": {"WE": [99], "WCLK": [2]}}
    port = mapped_memory_netlist(tmp_path, cells).ram_write_port("mem", 7)
    assert port["WE"] == r"(\system.m1.mem.arr.0.0 .WE | \system.m1.mem.arr.0.1 .WE)"
    assert port["ADDR"] == r"{(\system.m1.mem.arr.0.1 .WE), \system.m1.mem.arr.0.0 .ADDRD}"
    assert port["CONFLICT"] == r"(\system.m1.mem.arr.0.0 .WE && \system.m1.mem.arr.0.1 .WE)"


@pytest.mark.parametrize("change", ["missing_bank", "different_address", "replica_order"])
def test_lut_ram_rejects_an_unrecognized_bank_layout(tmp_path, change):
    cells = {f"system.m1.mem.arr.{replica}.{bank}": {
        "type": "RAM64M", "hide_name": 0,
        "connections": {"WE": [10 + bank], "WCLK": [2], "ADDRD": list(range(30, 36))}}
        for replica in range(2) for bank in range(2)}
    if change == "missing_bank":
        del cells["system.m1.mem.arr.1.1"]
    elif change == "different_address":
        cells["system.m1.mem.arr.1.1"]["connections"]["ADDRD"][0] = 99
    else:
        cells["system.m1.mem.arr.1.0"]["connections"]["WE"] = [11]
        cells["system.m1.mem.arr.1.1"]["connections"]["WE"] = [10]
    assert mapped_memory_netlist(tmp_path, cells).ram_write_port("mem", 7) is None


def test_gate_probe_uses_physical_bank_address_over_undriven_logical_name(tmp_path):
    path = tmp_path / "mapped.json"
    def net(bits):
        return {"bits": bits, "hide_name": 0}

    cells = {f"system.m1.mem.arr.0.{bank}": {
        "type": "RAM64M", "hide_name": 0,
        "connections": {"WE": [10 + bank], "WCLK": [2], "ADDRD": list(range(30, 36))}}
        for bank in range(2)}
    netnames = {"cpu_clk": net([2]), "system.m1.mem$ADDR_IN": net(list(range(30, 36)) + [99]),
                "system.m1.mem$D_IN": net(list(range(100, 132)))}
    path.write_text(json.dumps({"modules": {board_gls.TOP: {"netnames": netnames, "cells": cells}}}))
    wires, probes, _ = board_gls.gate_probes(board_gls.Netlist(path))
    assert "mem" in probes
    addr = next(w for w in wires if "gls_mem_addr =" in w)
    assert "ADDR_IN" not in addr
    assert ".WE" in addr and ".ADDRD" in addr


def block_ram_cell():
    return {"type": "RAMB36E1", "hide_name": 0,
            "parameters": {"RAM_MODE": "SDP", "WRITE_WIDTH_A": "0", "WRITE_WIDTH_B": "1001000"},
            "connections": {"CLKBWRCLK": [2], "ENBWREN": ["1"],
                            "WEBWE": [20] * 7 + ["0"],
                            "ADDRBWRADDR": ["0"] * 6 + list(range(30, 37)) + ["0"] * 3}}


def test_block_ram_recovers_removed_write_address_and_enable(tmp_path):
    cell = block_ram_cell()
    net = mapped_memory_netlist(tmp_path, {"system.m1.imem.arr.0.0": cell})
    port = net.ram_write_port("imem", 7)
    assert port["WE"] == r"((|\system.m1.imem.arr.0.0 .WEBWE))"
    assert port["ADDR"] == r"\system.m1.imem.arr.0.0 .ADDRBWRADDR[12:6]"


@pytest.mark.parametrize("change", ["partial_write", "different_clock", "high_address", "unsupported_mode"])
def test_block_ram_rejects_unsupported_write_contract(tmp_path, change):
    cell = block_ram_cell()
    if change == "partial_write":
        cell["connections"]["WEBWE"][1] = 21
    elif change == "different_clock":
        cell["connections"]["CLKBWRCLK"] = [3]
    elif change == "high_address":
        cell["connections"]["ADDRBWRADDR"][13] = 40
    else:
        cell["parameters"]["RAM_MODE"] = "TDP"
    net = mapped_memory_netlist(tmp_path, {"system.m1.imem.arr.0.0": cell})
    assert net.ram_write_port("imem", 7) is None


def test_failed_simulator_output_is_visible(capsys):
    with pytest.raises(subprocess.CalledProcessError):
        board_gls.run([sys.executable, "-c", "import sys; sys.stdout.write('simulator cause'); sys.exit(2)"])
    assert "simulator cause" in capsys.readouterr().err


def test_gate_cell_library_replaces_the_empty_bram_declaration(tmp_path, monkeypatch):
    datdir = tmp_path / "share"
    (datdir / "xilinx").mkdir(parents=True)
    (datdir / "xilinx" / "cells_sim.v").write_text(
        "module LUT1(); endmodule\nmodule RAMB36E1 ();\nendmodule\n")
    monkeypatch.setattr(board_gls, "yosys_datdir", lambda: datdir)
    sources = board_gls.gate_cell_sources(tmp_path)
    assert "module RAMB36E1" not in sources[1].read_text()
    assert "module LUT1" in sources[1].read_text()
    assert sources[2].name == "ramb36_sdp72.v"
    assert sources[3].name == "glbl.v"


@pytest.mark.strict_rtl
@pytest.mark.parametrize("sim", ["reference_iverilog", "iverilog", "verilator"])
def test_vendor_block_ram_stores_and_reads_the_synthesized_sdp72_mode(tmp_path, sim):
    compiler = "iverilog" if sim == "reference_iverilog" else sim
    if shutil.which(compiler) is None:
        pytest.skip(f"{compiler} not installed")
    tb = tmp_path / "bram_tb.v"
    tb.write_text(r"""
`timescale 1ns/1ps
module bram_tb;
  glbl glbl();
  reg clk = 0;
  always #5 clk = ~clk;
  reg [7:0] we = 0;
  reg [63:0] din = 0;
  reg [7:0] parity = 0;
  reg ren = 1, wen = 1;
  reg [15:0] raddr = 320;
  wire [63:0] dout;
  wire [7:0] pout;
  RAMB36E1 #(.RAM_MODE("SDP"), .READ_WIDTH_A(72), .READ_WIDTH_B(0),
    .WRITE_WIDTH_A(0), .WRITE_WIDTH_B(72), .DOA_REG(0), .DOB_REG(0),
    .WRITE_MODE_A("WRITE_FIRST"), .WRITE_MODE_B("WRITE_FIRST"),
    .INIT_01({128'b0, 64'h1122334455667788, 64'b0}), .INITP_00(256'h6c0000000000)) ram (
    .CLKARDCLK(clk), .CLKBWRCLK(clk), .ENARDEN(ren), .ENBWREN(wen),
    .ADDRARDADDR(raddr), .ADDRBWRADDR(16'd320), .WEA(4'b0), .WEBWE(we),
    .DIADI(din[31:0]), .DIBDI(din[63:32]), .DIPADIP(parity[3:0]), .DIPBDIP(parity[7:4]),
    .DOADO(dout[31:0]), .DOBDO(dout[63:32]), .DOPADOP(pout[3:0]), .DOPBDOP(pout[7:4]),
    .REGCEAREGCE(1'b0), .REGCEB(1'b0), .RSTRAMARSTRAM(1'b0), .RSTRAMB(1'b0),
    .RSTREGARSTREG(1'b0), .RSTREGB(1'b0), .CASCADEINA(1'b0), .CASCADEINB(1'b0),
    .INJECTDBITERR(1'b0), .INJECTSBITERR(1'b0));
  initial begin
    #25;
    if (dout !== 0 || pout !== 0) $fatal(1, "GSR reset mismatch");
    #175;
    @(negedge clk);
    if (dout !== 64'h1122334455667788 || pout !== 8'h6c)
      $fatal(1, "SDP72 INIT layout mismatch %h %h", dout, pout);
    @(negedge clk); din = 64'hfedcba9876543210; parity = 8'h5b; we = 8'hff;
    @(negedge clk); we = 0;
    repeat (2) @(negedge clk);
    if (dout !== din || pout !== parity) $fatal(1, "SDP72 readback mismatch %h %h", dout, pout);
    @(negedge clk); din = 64'haa; parity = 0; we = 1;
    @(negedge clk); we = 0;
    repeat (2) @(negedge clk);
    if (dout !== 64'hfedcba98765432aa || pout !== 8'h5a)
      $fatal(1, "SDP72 byte-mask mismatch %h %h", dout, pout);
    @(negedge clk); wen = 0; we = 8'hff; din = 0;
    @(negedge clk); wen = 1; we = 0;
    repeat (2) @(negedge clk);
    if (dout !== 64'hfedcba98765432aa || pout !== 8'h5a)
      $fatal(1, "write enable mismatch");
    ren = 0; raddr = 0;
    repeat (2) @(negedge clk);
    if (dout !== 64'hfedcba98765432aa || pout !== 8'h5a)
      $fatal(1, "read enable hold mismatch");
    ren = 1;
    repeat (2) @(negedge clk);
    if (dout !== 0 || pout !== 0) $fatal(1, "read address mismatch");
    $display("BRAM_PASS"); $finish;
  end
  initial begin #1000; $fatal(1, "BRAM timeout"); end
endmodule
""")
    model = (board_gls.XILINX_MODELS / "RAMB36E1.v" if sim == "reference_iverilog"
             else board_gls.BOARD_CELLS.parent / "ramb36_sdp72.v")
    sources = [str(tb), str(model),
               str(board_gls.XILINX_MODELS / "glbl.v")]
    if compiler == "iverilog":
        exe = tmp_path / "bram.vvp"
        cmd = ["iverilog", "-g2012", "-s", "bram_tb", "-o", str(exe), *sources]
        binary = ["vvp", str(exe)]
    else:
        obj = tmp_path / "obj"
        cmd = ["verilator", "--binary", "--timing", "-Wno-fatal", "-j", "2",
               "--top-module", "bram_tb", "--Mdir", str(obj), *sources]
        binary = [str(obj / "Vbram_tb")]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=180)
    assert proc.returncode == 0, proc.stdout[-3000:] + proc.stderr[-6000:]
    proc = subprocess.run(binary, capture_output=True, text=True, timeout=30)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "BRAM_PASS" in proc.stdout


def test_cpu_view_decodes_slots_and_morphisms():
    st = {"pc": 5, "mu": 0, "err": 0, "certified": 0, "regs": 3, "mem": [0] * 128,
          "ptTable": 1 << 32, "ptBases": 1 << 32, "pt_next_id": 2,
          "morph_valid_table": 0b1110, "morph_src_table": (1 << 6) | (1 << 12) | (1 << 18),
          "morph_dst_table": (1 << 6) | (1 << 12) | (1 << 18),
          "morph_identity_table": 0b1110, "morph_next_id": 4}
    view = board_gls.cpu_view(st)
    assert view["modules"] == {1: [1]}
    assert view["morphisms"] == {1: (1, 1, True), 2: (1, 1, True), 3: (1, 1, True)}
    assert view["regs"][0] == 3


@pytest.mark.parametrize("src,module,include", [
    ("thiele_cpu_kami.v", "mkModule1", "cpu_props.vh"),
    ("thiele_system.v", "mkThieleSystem", "system_props.vh"),
])
def test_formal_copy_adds_only_the_include(src, module, include):
    path = ROOT / "thielecpu" / "hardware" / "rtl" / src
    original = path.read_text(encoding="utf-8").splitlines()
    copy = formal_prepare.with_include(path, module, include).splitlines()
    assert len(copy) == len(original) + 1
    assert [ln for ln in copy if ln not in set(original)] == [f'`include "{include}"']


def test_formal_tasks_in_ci_exist_in_the_sby_file():
    text = (ROOT / "formal" / "thiele.sby").read_text(encoding="utf-8")
    tasks = text.split("[tasks]")[1].split("[")[0].split()
    assert set(formal_prepare.CI_TASKS) <= set(tasks)


@pytest.mark.strict_rtl
@pytest.mark.skipif(shutil.which("iverilog") is None, reason="iverilog not installed")
def test_board_top_rtl_matches_vm(tmp_path):
    """The board top's RTL, loaded over its UART pin, ends in the VM's state."""
    report = tmp_path / "gls.json"
    proc = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "board_gls.py"), "--no-gates", "--sim", "iverilog",
         "--report", str(report)],
        capture_output=True, text=True, timeout=1800)
    assert proc.returncode == 0, proc.stdout[-4000:] + proc.stderr[-4000:]
    data = json.loads(report.read_text())
    assert set(data["programs"]) == {n for n, p in board_gls.PROGRAMS.items() if not p.get("long")}
    assert all(p["ok"] for p in data["programs"].values())
