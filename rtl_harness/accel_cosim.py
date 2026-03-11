from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Tuple

from .cosim import REPO_ROOT

LEGACY_RTL_ARCHIVE = REPO_ROOT / "archive" / "hardware_legacy" / "2026-03-01_vm_verilog_prune_phase2" / "thielecpu" / "hardware" / "rtl" / "archive"


def _legacy_rtl_file(name: str) -> Path:
    path = LEGACY_RTL_ARCHIVE / name
    if not path.exists():
        raise FileNotFoundError(f"Legacy RTL module not found: {path}")
    return path


def _compile_module(rtl_files: List[Path], tb_file: Path, work_dir: Path) -> Path:
    out = work_dir / "sim.vvp"
    cmd = ["iverilog", "-g2012", "-o", str(out)] + [str(path) for path in rtl_files] + [str(tb_file)]
    result = subprocess.run(cmd, capture_output=True, text=True, cwd=str(work_dir), timeout=60)
    if result.returncode != 0:
        raise RuntimeError(f"iverilog failed:\n{result.stderr}")
    return out


def _run_sim(vvp_path: Path, work_dir: Path, timeout: int = 30) -> str:
    result = subprocess.run(["vvp", str(vvp_path)], capture_output=True, text=True, cwd=str(work_dir), timeout=timeout)
    return result.stdout


def _extract_json_lines(output: str) -> List[Dict[str, Any]]:
    results: List[Dict[str, Any]] = []
    for line in output.splitlines():
        text = line.strip()
        if text.startswith("{") and text.endswith("}"):
            results.append(json.loads(text))
    return results


def _write_partition_core_tb(work_dir: Path, operations: List[Dict[str, Any]]) -> Path:
    opcodes = {"PNEW": "8'h00", "PSPLIT": "8'h01", "PMERGE": "8'h02"}
    lines = [
        "`timescale 1ns / 1ps",
        "module partition_core_cosim_tb;",
        "    parameter MAX_MODULES = 8;",
        "    parameter REGION_WIDTH = 64;",
        "    parameter MU_WIDTH = 32;",
        "    reg clk, rst_n;",
        "    reg [7:0] op;",
        "    reg op_valid;",
        "    reg [REGION_WIDTH-1:0] pnew_region;",
        "    reg [7:0] psplit_module_id;",
        "    reg [REGION_WIDTH-1:0] psplit_mask;",
        "    reg [7:0] pmerge_m1, pmerge_m2;",
        "    reg [7:0] explicit_cost;",
        "    wire [7:0] num_modules, result_module_id;",
        "    wire op_done, is_structured;",
        "    wire [MU_WIDTH-1:0] mu_discovery, mu_execution, mu_cost;",
        "    wire [MAX_MODULES*REGION_WIDTH-1:0] partitions;",
        "    partition_core #( .MAX_MODULES(MAX_MODULES), .REGION_WIDTH(REGION_WIDTH), .MU_WIDTH(MU_WIDTH) ) dut (",
        "        .clk(clk), .rst_n(rst_n), .op(op), .op_valid(op_valid), .pnew_region(pnew_region),",
        "        .psplit_module_id(psplit_module_id), .psplit_mask(psplit_mask), .pmerge_m1(pmerge_m1), .pmerge_m2(pmerge_m2),",
        "        .explicit_cost(explicit_cost), .num_modules(num_modules), .result_module_id(result_module_id),",
        "        .op_done(op_done), .is_structured(is_structured), .mu_discovery(mu_discovery), .mu_execution(mu_execution),",
        "        .mu_cost(mu_cost), .partitions(partitions)",
        "    );",
        "    initial begin clk = 0; forever #5 clk = ~clk; end",
        "    task exec_op(input [7:0] opc); begin op <= opc; op_valid <= 1; @(posedge clk); op_valid <= 0; @(posedge clk); while (!op_done) @(posedge clk); @(posedge clk); end endtask",
        "    task dump_state(input integer step_num); begin $display(\"{\\\"step\\\": %0d, \\\"num_modules\\\": %0d, \\\"mu_discovery\\\": %0d, \\\"mu_execution\\\": %0d, \\\"mu_cost\\\": %0d, \\\"is_structured\\\": %0d, \\\"result_id\\\": %0d}\", step_num, num_modules, mu_discovery, mu_execution, mu_cost, is_structured, result_module_id); end endtask",
        "    initial begin",
        "        rst_n = 0; op = 0; op_valid = 0; pnew_region = 0; psplit_module_id = 0; psplit_mask = 0; pmerge_m1 = 0; pmerge_m2 = 0; explicit_cost = 0;",
        "        repeat(5) @(posedge clk);",
        "        rst_n = 1;",
        "        repeat(2) @(posedge clk);",
    ]
    for index, operation in enumerate(operations):
        op_name = operation["op"].upper()
        lines.append(f"        explicit_cost <= 8'd{operation.get('cost', 0)};")
        if op_name == "PNEW":
            lines.append(f"        pnew_region <= 64'h{operation.get('region', 0):016X};")
            lines.append(f"        exec_op({opcodes['PNEW']});")
        elif op_name == "PSPLIT":
            lines.append(f"        psplit_module_id <= 8'd{operation.get('mid', 0)};")
            lines.append(f"        psplit_mask <= 64'h{operation.get('mask', 0):016X};")
            lines.append(f"        exec_op({opcodes['PSPLIT']});")
        elif op_name == "PMERGE":
            lines.append(f"        pmerge_m1 <= 8'd{operation.get('m1', 0)};")
            lines.append(f"        pmerge_m2 <= 8'd{operation.get('m2', 1)};")
            lines.append(f"        exec_op({opcodes['PMERGE']});")
        lines.append(f"        dump_state({index});")
    lines.extend(["        $finish;", "    end", "endmodule"])
    tb_path = work_dir / "partition_core_cosim_tb.v"
    tb_path.write_text("\n".join(lines), encoding="utf-8")
    return tb_path


def run_partition_core(operations: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    with tempfile.TemporaryDirectory(prefix="pc_cosim_") as tmpdir:
        work_dir = Path(tmpdir)
        tb_path = _write_partition_core_tb(work_dir, operations)
        vvp_path = _compile_module([_legacy_rtl_file("partition_core.v")], tb_path, work_dir)
        return _extract_json_lines(_run_sim(vvp_path, work_dir))


_MU_ALU_OPCODES = {
    "ADD": 0,
    "SUB": 1,
    "MUL_Q16": 2,
    "DIV_Q16": 3,
    "LOG2": 4,
    "CMP": 5,
    "MIN": 6,
    "MAX": 7,
}


def run_mu_alu(operations: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    def q16_add(a: int, b: int) -> Tuple[int, bool]:
        result = a + b
        return result & 0xFFFFFFFF, result > 0xFFFFFFFF or result < 0

    def q16_sub(a: int, b: int) -> Tuple[int, bool]:
        return (a - b) & 0xFFFFFFFF, False

    def q16_mul(a: int, b: int) -> Tuple[int, bool]:
        result = (a * b) >> 16
        return result & 0xFFFFFFFF, result > 0xFFFFFFFF

    def q16_div(a: int, b: int) -> Tuple[int, bool]:
        if b == 0:
            return 0xFFFFFFFF, True
        return ((a << 16) // b) & 0xFFFFFFFF, False

    def q16_log2(a: int, _b: int) -> Tuple[int, bool]:
        import math
        if a <= 0:
            return 0, True
        return int(math.log2(a / 65536.0) * 65536) & 0xFFFFFFFF, False

    def q16_cmp(a: int, b: int) -> Tuple[int, bool]:
        if a < b:
            return 0xFFFFFFFF, False
        if a > b:
            return 1, False
        return 0, False

    ops = {
        "ADD": q16_add,
        "SUB": q16_sub,
        "MUL_Q16": q16_mul,
        "DIV_Q16": q16_div,
        "LOG2": q16_log2,
        "CMP": q16_cmp,
        "MIN": lambda a, b: (min(a, b), False),
        "MAX": lambda a, b: (max(a, b), False),
    }
    names = {value: key for key, value in _MU_ALU_OPCODES.items()}
    results: List[Dict[str, Any]] = []
    for operation in operations:
        raw_op = operation.get("op", 0)
        name = raw_op.upper() if isinstance(raw_op, str) else names.get(int(raw_op), "ADD")
        result, overflow = ops[name](operation.get("a", 0) & 0xFFFFFFFF, operation.get("b", 0) & 0xFFFFFFFF)
        results.append({**operation, "result": result, "overflow": int(overflow)})
    return results


__all__ = ["run_partition_core", "run_mu_alu"]
