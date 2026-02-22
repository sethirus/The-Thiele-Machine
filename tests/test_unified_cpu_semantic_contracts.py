"""Strict semantic contracts for unified RTL CPU behavior.

These checks target invariants that parse/smoke tests do not guarantee.
They are intended to fail on semantic regressions even when synthesis still passes.
"""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RTL = ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_unified.v"


def _run_custom_tb(program_words: list[int]) -> dict[str, int]:
    init_lines = "\n    ".join(
        f"instr_mem[{idx}] = 32'h{word:08X};" for idx, word in enumerate(program_words)
    )
    tb = f"""
`timescale 1ns/1ps
module semantic_tb;
  reg clk = 0;
  reg rst_n = 0;

  wire [31:0] cert_addr, status, error_code, partition_ops, mdl_ops, info_gain, mu;
  wire [31:0] mem_addr, mem_wdata, logic_addr, pc;
  reg  [31:0] mem_rdata = 32'h0;
  wire mem_we, mem_en, logic_req;
  reg logic_ack = 1'b0;
  reg [31:0] logic_data = 32'h0;

  reg [31:0] instr_mem [0:31];
  integer i;

  thiele_cpu dut (
    .clk(clk), .rst_n(rst_n),
    .cert_addr(cert_addr), .status(status), .error_code(error_code),
    .partition_ops(partition_ops), .mdl_ops(mdl_ops), .info_gain(info_gain), .mu(mu),
    .mu_tensor_0(), .mu_tensor_1(), .mu_tensor_2(), .mu_tensor_3(), .bianchi_alarm(),
    .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_rdata(mem_rdata), .mem_we(mem_we), .mem_en(mem_en),
    .logic_req(logic_req), .logic_addr(logic_addr), .logic_ack(logic_ack), .logic_data(logic_data),
    .instr_data(instr_mem[pc[31:2]]), .pc(pc)
  );

  always #5 clk = ~clk;

  initial begin
    for (i = 0; i < 32; i = i + 1) instr_mem[i] = 32'h00000000;
        {init_lines}

    #20 rst_n = 1'b1;

    repeat (120) begin
      @(posedge clk);
      if (dut.state == 4'hC) begin
        $display("RESULT status=%0d error=%0d mu=%0d pc=%0d", status, error_code, mu, pc);
        $finish;
      end
    end

    $display("RESULT status=%0d error=%0d mu=%0d pc=%0d", status, error_code, mu, pc);
    $finish;
  end
endmodule
"""

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        tb_path = td_path / "semantic_tb.v"
        out_path = td_path / "sim.out"
        tb_path.write_text(tb, encoding="utf-8")

        compile_res = subprocess.run(
            ["iverilog", "-g2012", "-DYOSYS_LITE", "-o", str(out_path), str(RTL), str(tb_path)],
            capture_output=True,
            text=True,
            check=True,
        )
        assert compile_res.returncode == 0

        run_res = subprocess.run(["vvp", str(out_path)], capture_output=True, text=True, check=True)
        line = next((ln for ln in run_res.stdout.splitlines() if ln.startswith("RESULT ")), "")
        assert line, f"No RESULT line in output:\n{run_res.stdout}\n{run_res.stderr}"

    parts = dict(tok.split("=") for tok in line.replace("RESULT ", "").split())
    return {k: int(v) for k, v in parts.items()}


def _word(op: int, a: int = 0, b: int = 0, c: int = 0) -> int:
    return ((op & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (c & 0xFF)


def test_halt_is_terminal_and_blocks_following_ops() -> None:
    # HALT first; trailing EMIT must not execute.
    program = [
        _word(0xFF, 0, 0, 0),
        _word(0x0E, 0, 7, 5),
    ]
    r = _run_custom_tb(program)
    assert r["mu"] == 0, f"HALT should block later ops, got mu={r['mu']}"


def test_chsh_supra_quantum_sets_error() -> None:
    # S = 4 pattern: E00=E01=E10=+1, E11=-1.
    program = [
        _word(0x09, 0b00, 0b00, 0),
        _word(0x09, 0b01, 0b00, 0),
        _word(0x09, 0b10, 0b00, 0),
        _word(0x09, 0b11, 0b10, 0),
        _word(0xFF, 0, 0, 0),
    ]
    r = _run_custom_tb(program)
    assert r["error"] == int("BADC45C", 16), f"Expected Tsirelson violation error, got {r['error']:08X}"


def test_chsh_classical_pattern_no_error() -> None:
    # S = 2 pattern: all correlations +1.
    program = [
        _word(0x09, 0b00, 0b00, 0),
        _word(0x09, 0b01, 0b00, 0),
        _word(0x09, 0b10, 0b00, 0),
        _word(0x09, 0b11, 0b00, 0),
        _word(0xFF, 0, 0, 0),
    ]
    r = _run_custom_tb(program)
    assert r["error"] == 0, f"Classical CHSH pattern must not set error, got {r['error']:08X}"


def test_static_contract_receipt_checker_uses_receipt_valid() -> None:
    txt = RTL.read_text(encoding="utf-8")
    assert ".receipt_valid(receipt_valid)" in txt


def test_static_contract_no_chsh_placeholder_left() -> None:
    txt = RTL.read_text(encoding="utf-8")
    assert "Placeholder: use ALU result in real impl" not in txt
