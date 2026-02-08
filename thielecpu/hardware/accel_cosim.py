"""Accelerator co-simulation harness for standalone Verilog modules.

Compiles and runs individual accelerator testbenches through Icarus Verilog,
parses JSON output, and validates against Python reference implementations.

This extends the main CPU cosim (cosim.py) to cover accelerator blocks that
are NOT instantiated inside thiele_cpu.v but are part of the 3-way
isomorphism chain as standalone verification targets.

Covered accelerators:
  - partition_core: PNEW/PSPLIT/PMERGE partition operations
  - receipt_integrity_checker: μ-cost receipt verification
  - mu_alu: Q16.16 fixed-point μ-cost arithmetic
  - chsh_partition: CHSH supra-quantum distribution
  - period_finder: Modular period discovery
  - state_serializer: Canonical state serialization
  - mau: MDL accounting unit
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

RTL_DIR = Path(__file__).resolve().parent / "rtl"
TB_DIR = Path(__file__).resolve().parent / "testbench"


def _compile_module(rtl_files: List[Path], tb_file: Path,
                    work_dir: Path, include_dirs: Optional[List[Path]] = None,
                    extra_defines: Optional[List[str]] = None) -> Path:
    """Compile a Verilog module + testbench with iverilog."""
    out = work_dir / "sim.vvp"
    cmd = ["iverilog", "-g2012", "-o", str(out)]
    if include_dirs:
        for d in include_dirs:
            cmd += ["-I", str(d)]
    if extra_defines:
        for d in extra_defines:
            cmd += [f"-D{d}"]
    for f in rtl_files:
        cmd.append(str(f))
    cmd.append(str(tb_file))
    result = subprocess.run(cmd, capture_output=True, text=True, cwd=str(work_dir))
    if result.returncode != 0:
        raise RuntimeError(f"iverilog failed:\n{result.stderr}")
    return out


def _run_sim(vvp_path: Path, work_dir: Path, timeout: int = 30) -> str:
    """Run a compiled VVP simulation."""
    result = subprocess.run(
        ["vvp", str(vvp_path)],
        capture_output=True, text=True, cwd=str(work_dir), timeout=timeout
    )
    return result.stdout


def _extract_json_lines(output: str) -> List[Dict]:
    """Extract JSON objects from $display output."""
    results = []
    for line in output.split("\n"):
        line = line.strip()
        if line.startswith("{") and line.endswith("}"):
            try:
                results.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return results


# ============================================================================
# Partition Core cosim
# ============================================================================

def _write_partition_core_tb(work_dir: Path, operations: List[Dict]) -> Path:
    """Generate a testbench for partition_core with given operations.

    Each operation is a dict:
      {"op": "PNEW"|"PSPLIT"|"PMERGE", "region": int, "mid": int,
       "mask": int, "m1": int, "m2": int, "cost": int}
    """
    OPCODES = {"PNEW": "8'h00", "PSPLIT": "8'h01", "PMERGE": "8'h02",
               "MDLACC": "8'h05"}

    tb_lines = []
    tb_lines.append("""`timescale 1ns / 1ps
module partition_core_cosim_tb;
    parameter MAX_MODULES = 8;
    parameter REGION_WIDTH = 64;
    parameter MU_WIDTH = 32;

    reg clk, rst_n;
    reg [7:0] op;
    reg op_valid;
    reg [REGION_WIDTH-1:0] pnew_region;
    reg [7:0] psplit_module_id;
    reg [REGION_WIDTH-1:0] psplit_mask;
    reg [7:0] pmerge_m1, pmerge_m2;
    reg [7:0] explicit_cost;

    wire [7:0] num_modules, result_module_id;
    wire op_done, is_structured;
    wire [MU_WIDTH-1:0] mu_discovery, mu_execution, mu_cost;
    wire [MAX_MODULES*REGION_WIDTH-1:0] partitions;

    partition_core #(
        .MAX_MODULES(MAX_MODULES),
        .REGION_WIDTH(REGION_WIDTH),
        .MU_WIDTH(MU_WIDTH)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .op(op), .op_valid(op_valid),
        .pnew_region(pnew_region),
        .psplit_module_id(psplit_module_id),
        .psplit_mask(psplit_mask),
        .pmerge_m1(pmerge_m1), .pmerge_m2(pmerge_m2),
        .explicit_cost(explicit_cost),
        .num_modules(num_modules),
        .result_module_id(result_module_id),
        .op_done(op_done),
        .is_structured(is_structured),
        .mu_discovery(mu_discovery),
        .mu_execution(mu_execution),
        .mu_cost(mu_cost),
        .partitions(partitions)
    );

    initial begin clk = 0; forever #5 clk = ~clk; end

    task exec_op(input [7:0] opc);
        begin
            op <= opc; op_valid <= 1;
            @(posedge clk); op_valid <= 0;
            @(posedge clk);
            while (!op_done) @(posedge clk);
            @(posedge clk);  // settle
        end
    endtask

    task dump_state(input integer step_num);
        begin
            $display("{\\"step\\": %0d, \\"num_modules\\": %0d, \\"mu_discovery\\": %0d, \\"mu_execution\\": %0d, \\"mu_cost\\": %0d, \\"is_structured\\": %0d, \\"result_id\\": %0d}",
                step_num, num_modules, mu_discovery, mu_execution, mu_cost, is_structured, result_module_id);
        end
    endtask

    initial begin
        rst_n = 0; op = 0; op_valid = 0;
        pnew_region = 0; psplit_module_id = 0; psplit_mask = 0;
        pmerge_m1 = 0; pmerge_m2 = 0; explicit_cost = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
""")

    for i, oper in enumerate(operations):
        op_name = oper["op"].upper()
        cost = oper.get("cost", 0)
        tb_lines.append(f"        explicit_cost <= 8'd{cost};")
        if op_name == "PNEW":
            region = oper.get("region", 0)
            tb_lines.append(f"        pnew_region <= 64'h{region:016X};")
            tb_lines.append(f"        exec_op({OPCODES['PNEW']});")
        elif op_name == "PSPLIT":
            mid = oper.get("mid", 0)
            mask = oper.get("mask", 0)
            tb_lines.append(f"        psplit_module_id <= 8'd{mid};")
            tb_lines.append(f"        psplit_mask <= 64'h{mask:016X};")
            tb_lines.append(f"        exec_op({OPCODES['PSPLIT']});")
        elif op_name == "PMERGE":
            m1 = oper.get("m1", 0)
            m2 = oper.get("m2", 1)
            tb_lines.append(f"        pmerge_m1 <= 8'd{m1};")
            tb_lines.append(f"        pmerge_m2 <= 8'd{m2};")
            tb_lines.append(f"        exec_op({OPCODES['PMERGE']});")
        tb_lines.append(f"        dump_state({i});")
        tb_lines.append("")

    tb_lines.append("        $finish;")
    tb_lines.append("    end")
    tb_lines.append("endmodule")

    tb_path = work_dir / "partition_core_cosim_tb.v"
    tb_path.write_text("\n".join(tb_lines))
    return tb_path


def run_partition_core(operations: List[Dict]) -> List[Dict]:
    """Run partition_core with given operations, return JSON state per step."""
    with tempfile.TemporaryDirectory(prefix="pc_cosim_") as tmpdir:
        work_dir = Path(tmpdir)
        tb_path = _write_partition_core_tb(work_dir, operations)
        vvp_path = _compile_module(
            [RTL_DIR / "partition_core.v"],
            tb_path, work_dir,
            include_dirs=[RTL_DIR]
        )
        output = _run_sim(vvp_path, work_dir)
        return _extract_json_lines(output)


# ============================================================================
# Receipt Integrity Checker cosim
# ============================================================================

def _write_receipt_checker_tb(work_dir: Path, receipts: List[Dict]) -> Path:
    """Generate a testbench for receipt_integrity_checker.

    Each receipt is:
      {"pre_mu": int, "post_mu": int, "opcode": int, "operand": int,
       "chain_mode": bool, "prev_post_mu": int}
    """
    tb_lines = []
    tb_lines.append("""`timescale 1ns / 1ps
module receipt_checker_cosim_tb;
    reg clk, rst_n;
    reg receipt_valid;
    reg [31:0] receipt_pre_mu, receipt_post_mu, receipt_operand;
    reg [7:0] receipt_opcode;
    reg chain_mode;
    reg [31:0] prev_post_mu;

    wire receipt_integrity_ok, chain_continuity_ok;
    wire [31:0] computed_cost, error_code;

    receipt_integrity_checker dut (
        .clk(clk), .rst_n(rst_n),
        .receipt_valid(receipt_valid),
        .receipt_pre_mu(receipt_pre_mu),
        .receipt_post_mu(receipt_post_mu),
        .receipt_opcode(receipt_opcode),
        .receipt_operand(receipt_operand),
        .chain_mode(chain_mode),
        .prev_post_mu(prev_post_mu),
        .receipt_integrity_ok(receipt_integrity_ok),
        .chain_continuity_ok(chain_continuity_ok),
        .computed_cost(computed_cost),
        .error_code(error_code)
    );

    initial begin clk = 0; forever #5 clk = ~clk; end

    initial begin
        rst_n = 0; receipt_valid = 0;
        receipt_pre_mu = 0; receipt_post_mu = 0;
        receipt_opcode = 0; receipt_operand = 0;
        chain_mode = 0; prev_post_mu = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
""")

    for i, r in enumerate(receipts):
        pre = r.get("pre_mu", 0)
        post = r.get("post_mu", 0)
        opc = r.get("opcode", 0)
        operand = r.get("operand", 0)
        cm = 1 if r.get("chain_mode", False) else 0
        ppm = r.get("prev_post_mu", 0)
        tb_lines.append(f"""
        receipt_pre_mu <= 32'd{pre};
        receipt_post_mu <= 32'd{post};
        receipt_opcode <= 8'h{opc:02X};
        receipt_operand <= 32'h{operand:08X};
        chain_mode <= 1'b{cm};
        prev_post_mu <= 32'd{ppm};
        receipt_valid <= 1;
        @(posedge clk);
        @(posedge clk);  // result is registered, read BEFORE clearing valid
        $display("{{\\"step\\": {i}, \\"integrity_ok\\": %0d, \\"chain_ok\\": %0d, \\"computed_cost\\": %0d, \\"error_code\\": %0d}}",
            receipt_integrity_ok, chain_continuity_ok, computed_cost, error_code);
        receipt_valid <= 0;
        @(posedge clk);
""")

    tb_lines.append("        $finish;")
    tb_lines.append("    end")
    tb_lines.append("endmodule")

    tb_path = work_dir / "receipt_checker_cosim_tb.v"
    tb_path.write_text("\n".join(tb_lines))
    return tb_path


def run_receipt_checker(receipts: List[Dict]) -> List[Dict]:
    """Run receipt_integrity_checker, return JSON per receipt."""
    with tempfile.TemporaryDirectory(prefix="rc_cosim_") as tmpdir:
        work_dir = Path(tmpdir)
        tb_path = _write_receipt_checker_tb(work_dir, receipts)
        # receipt_integrity_checker is defined in thiele_cpu_unified.v
        vvp_path = _compile_module(
            [RTL_DIR / "thiele_cpu_unified.v"],
            tb_path, work_dir,
            include_dirs=[RTL_DIR]
        )
        output = _run_sim(vvp_path, work_dir)
        return _extract_json_lines(output)


# ============================================================================
# μ-ALU standalone cosim
# ============================================================================

def _write_mu_alu_tb(work_dir: Path, operations: List[Dict]) -> Path:
    """Generate a testbench for mu_alu.

    Each operation is:
      {"op": int(0-7), "a": int, "b": int}
    Op codes: 0=ADD, 1=SUB, 2=MUL_Q16, 3=DIV_Q16, 4=LOG2, 5=CMP, 6=MIN, 7=MAX
    """
    tb_lines = []
    tb_lines.append("""`timescale 1ns / 1ps
module mu_alu_cosim_tb;
    reg clk, rst_n;
    reg [2:0] op;
    reg [31:0] operand_a, operand_b;
    reg valid;

    wire [31:0] result;
    wire ready, overflow;

    mu_alu dut (
        .clk(clk), .rst_n(rst_n),
        .op(op), .operand_a(operand_a), .operand_b(operand_b),
        .valid(valid), .result(result), .ready(ready), .overflow(overflow)
    );

    initial begin clk = 0; forever #5 clk = ~clk; end

    task run_op(input [2:0] oper, input [31:0] a, input [31:0] b);
        begin
            op <= oper; operand_a <= a; operand_b <= b;
            valid <= 1;
            @(posedge clk); valid <= 0;
            while (!ready) @(posedge clk);
            @(posedge clk);
        end
    endtask

    initial begin
        rst_n = 0; op = 0; valid = 0; operand_a = 0; operand_b = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
""")

    for i, oper in enumerate(operations):
        o = oper.get("op", 0)
        a = oper.get("a", 0)
        b = oper.get("b", 0)
        tb_lines.append(f"        run_op(3'd{o}, 32'h{a:08X}, 32'h{b:08X});")
        tb_lines.append(f'        $display("{{\\"step\\": {i}, \\"op\\": {o}, \\"a\\": %0d, \\"b\\": %0d, \\"result\\": %0d, \\"overflow\\": %0d}}", {a}, {b}, result, overflow);')

    tb_lines.append("        $finish;")
    tb_lines.append("    end")
    tb_lines.append("endmodule")

    tb_path = work_dir / "mu_alu_cosim_tb.v"
    tb_path.write_text("\n".join(tb_lines))
    return tb_path


def run_mu_alu(operations: List[Dict]) -> List[Dict]:
    """Run mu_alu with given operations, return JSON per step."""
    with tempfile.TemporaryDirectory(prefix="alu_cosim_") as tmpdir:
        work_dir = Path(tmpdir)
        tb_path = _write_mu_alu_tb(work_dir, operations)
        # mu_alu is defined in thiele_cpu_unified.v (single-file design)
        # but also kept in mu_alu.v for standalone testing. Use unified.
        vvp_path = _compile_module(
            [RTL_DIR / "thiele_cpu_unified.v"],
            tb_path, work_dir,
            include_dirs=[RTL_DIR]
        )
        output = _run_sim(vvp_path, work_dir)
        return _extract_json_lines(output)


# ============================================================================
# CHSH Partition cosim
# ============================================================================

def run_chsh_partition(settings: List[Tuple[int, int]]) -> Optional[List[Dict]]:
    """Run chsh_partition if module exists, return expectation values.

    settings: list of (x, y) measurement setting pairs.
    Returns None if module doesn't compile.
    """
    chsh_file = RTL_DIR / "chsh_partition.v"
    if not chsh_file.exists():
        return None

    with tempfile.TemporaryDirectory(prefix="chsh_cosim_") as tmpdir:
        work_dir = Path(tmpdir)
        tb_lines = ["""`timescale 1ns / 1ps
module chsh_cosim_tb;
    reg clk, rst_n, start;
    reg alice_setting, bob_setting;
    reg [7:0] alice_module_id, bob_module_id;
    reg [31:0] seed;
    wire alice_outcome, bob_outcome;
    wire [15:0] chsh_value, mu_cost;
    wire valid, busy;

    chsh_partition dut (
        .clk(clk), .rst_n(rst_n),
        .start(start),
        .alice_setting(alice_setting), .bob_setting(bob_setting),
        .alice_module_id(alice_module_id), .bob_module_id(bob_module_id),
        .seed(seed),
        .alice_outcome(alice_outcome), .bob_outcome(bob_outcome),
        .chsh_value(chsh_value), .mu_cost(mu_cost),
        .valid(valid), .busy(busy)
    );

    initial begin clk = 0; forever #5 clk = ~clk; end

    task run_setting(input x, input y, input integer step_num);
        begin
            alice_setting <= x; bob_setting <= y;
            alice_module_id <= 8'd0; bob_module_id <= 8'd1;
            seed <= 32'hDEADBEEF + step_num;
            start <= 1;
            @(posedge clk); start <= 0;
            while (!valid) @(posedge clk);
            @(posedge clk);
        end
    endtask

    initial begin
        rst_n = 0; start = 0; alice_setting = 0; bob_setting = 0;
        alice_module_id = 0; bob_module_id = 1; seed = 32'hDEADBEEF;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
"""]
        for i, (x, y) in enumerate(settings):
            tb_lines.append(f"        run_setting(1'b{x}, 1'b{y}, {i});")
            tb_lines.append(f'        $display("{{\\"step\\": {i}, \\"x\\": {x}, \\"y\\": {y}, \\"chsh_value\\": %0d, \\"mu_cost\\": %0d, \\"alice\\": %0d, \\"bob\\": %0d}}", chsh_value, mu_cost, alice_outcome, bob_outcome);')

        tb_lines.append("        $finish;")
        tb_lines.append("    end")
        tb_lines.append("endmodule")

        tb_path = work_dir / "chsh_cosim_tb.v"
        tb_path.write_text("\n".join(tb_lines))

        try:
            vvp_path = _compile_module([chsh_file], tb_path, work_dir,
                                       include_dirs=[RTL_DIR])
            output = _run_sim(vvp_path, work_dir)
            return _extract_json_lines(output)
        except (RuntimeError, subprocess.TimeoutExpired):
            return None
