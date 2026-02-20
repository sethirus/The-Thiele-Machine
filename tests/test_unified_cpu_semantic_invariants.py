"""Strict semantic invariants for unified RTL CPU.

These tests intentionally target end-to-end CPU semantics (not just parse/smoke):
- HALT must behave as a terminal state for execution.
- Post-HALT instructions must not produce side-effects.
- Receipt checker wiring must be receipt-driven, not instruction-cycle-driven.
- Module metadata storage semantics must be unambiguous.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
RTL_FILE = REPO_ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_unified.v"


pytestmark = [
    pytest.mark.hardware,
    pytest.mark.skipif(shutil.which("iverilog") is None, reason="iverilog not installed"),
]


def _run_tb(tb_src: str) -> tuple[int, str, str]:
    with tempfile.TemporaryDirectory(prefix="thiele_semantic_tb_") as td:
        td_path = Path(td)
        tb_path = td_path / "tb.v"
        sim_path = td_path / "sim.vvp"
        tb_path.write_text(tb_src, encoding="utf-8")

        compile_cmd = [
            "iverilog",
            "-g2012",
            "-I",
            str(RTL_FILE.parent),
            "-o",
            str(sim_path),
            str(RTL_FILE),
            str(tb_path),
        ]
        c = subprocess.run(compile_cmd, capture_output=True, text=True, timeout=120)
        if c.returncode != 0:
            return c.returncode, c.stdout, c.stderr

        r = subprocess.run(["vvp", str(sim_path)], capture_output=True, text=True, timeout=60)
        return r.returncode, r.stdout, r.stderr


def test_halt_freezes_pc_and_blocks_side_effects() -> None:
    """After first HALT executes, PC and info_gain must stay unchanged."""
    tb = r'''
`timescale 1ns/1ps
module tb;
  reg clk;
  reg rst_n;

  wire [31:0] cert_addr;
  wire [31:0] status;
  wire [31:0] error_code;
  wire [31:0] partition_ops;
  wire [31:0] mdl_ops;
  wire [31:0] info_gain;
  wire [31:0] mu;
  wire [31:0] mu_tensor_0, mu_tensor_1, mu_tensor_2, mu_tensor_3;
  wire bianchi_alarm;
  wire [31:0] mem_addr, mem_wdata;
  reg  [31:0] mem_rdata;
  wire mem_we, mem_en;
  wire logic_req;
  wire [31:0] logic_addr;
  reg logic_ack;
  reg [31:0] logic_data;
  wire py_req;
  wire [31:0] py_code_addr;
  reg py_ack;
  reg [31:0] py_result;
  reg [31:0] instr_mem [0:15];
  wire [31:0] pc;

  thiele_cpu dut (
    .clk(clk), .rst_n(rst_n),
    .cert_addr(cert_addr), .status(status), .error_code(error_code),
    .partition_ops(partition_ops), .mdl_ops(mdl_ops), .info_gain(info_gain), .mu(mu),
    .mu_tensor_0(mu_tensor_0), .mu_tensor_1(mu_tensor_1), .mu_tensor_2(mu_tensor_2), .mu_tensor_3(mu_tensor_3),
    .bianchi_alarm(bianchi_alarm),
    .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_rdata(mem_rdata), .mem_we(mem_we), .mem_en(mem_en),
    .logic_req(logic_req), .logic_addr(logic_addr), .logic_ack(logic_ack), .logic_data(logic_data),
    .py_req(py_req), .py_code_addr(py_code_addr), .py_ack(py_ack), .py_result(py_result),
    .instr_data(instr_mem[pc[31:2]]), .pc(pc)
  );

  integer i;
  reg halt_seen;
  reg [31:0] pc_at_halt;
  reg [31:0] info_gain_at_halt;
  integer post_halt_cycles;

  initial begin
    clk = 0;
    rst_n = 0;
    mem_rdata = 0;
    logic_ack = 0;
    logic_data = 0;
    py_ack = 0;
    py_result = 0;
    halt_seen = 0;
    post_halt_cycles = 0;

    for (i = 0; i < 16; i = i + 1) instr_mem[i] = 32'h00000000;
    // 0: HALT
    instr_mem[0] = {8'hFF, 8'h00, 8'h00, 8'h00};
    // 1: EMIT operand_b=5 (must never execute after proper HALT)
    instr_mem[1] = {8'h0E, 8'h00, 8'h05, 8'h00};
    // 2: HALT
    instr_mem[2] = {8'hFF, 8'h00, 8'h00, 8'h00};

    #20 rst_n = 1;
    #1200;
    $display("FAIL: timeout without semantic verdict");
    $finish;
  end

  always #5 clk = ~clk;

  always @(posedge clk) begin
    if (!rst_n) begin
      halt_seen <= 0;
      post_halt_cycles <= 0;
    end else begin
      if (!halt_seen && dut.state == 4'h2 && dut.opcode == 8'hFF) begin
        halt_seen <= 1;
        pc_at_halt <= pc;
        info_gain_at_halt <= info_gain;
      end else if (halt_seen) begin
        post_halt_cycles <= post_halt_cycles + 1;

        if (pc != pc_at_halt) begin
          $display("FAIL: PC moved after HALT (pc=%0d expected=%0d)", pc, pc_at_halt);
          $finish;
        end

        if (info_gain != info_gain_at_halt) begin
          $display("FAIL: side-effect after HALT (info_gain=%0d expected=%0d)", info_gain, info_gain_at_halt);
          $finish;
        end

        if (post_halt_cycles >= 6) begin
          $display("PASS: HALT is terminal and side-effect free");
          $finish;
        end
      end
    end
  end
endmodule
'''

    rc, out, err = _run_tb(tb)
    assert rc == 0, f"simulation execution failed\nSTDOUT:\n{out}\nSTDERR:\n{err}"
    assert "PASS: HALT is terminal and side-effect free" in out, (
        "Unified CPU semantic HALT invariant failed.\n"
        f"STDOUT:\n{out}\nSTDERR:\n{err}"
    )


def test_receipt_checker_wiring_is_receipt_driven() -> None:
    """Receipt integrity checker must be driven by receipt_valid, not instr_valid."""
    text = RTL_FILE.read_text(encoding="utf-8")
    assert ".receipt_valid(instr_valid)" not in text, (
        "receipt_integrity_checker is currently wired to instr_valid, which validates "
        "instruction cycles instead of receipt events."
    )


def test_module_table_not_used_as_existence_flag() -> None:
    """module_table should represent region size only; existence belongs to module_exists."""
    text = RTL_FILE.read_text(encoding="utf-8")
    bad_pattern = re.compile(r"module_table\s*\[\s*i\s*\]\s*==\s*32'd1")
    assert bad_pattern.search(text) is None, (
        "module_table is used as an existence flag in dedup logic; this conflicts with "
        "its region-size role and with module_exists[]."
    )
