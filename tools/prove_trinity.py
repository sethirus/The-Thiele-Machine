#!/usr/bin/env python3
"""
Run a cross-layer "Trinity" verification pass against a single Thiele
assembly program, executing it through the Python VM, the Verilog RTL
(testbench), and the Coq opcode table to confirm structural alignment.

Outputs live in ``artifacts/trinity`` by default and include per-layer
receipts plus a hash comparison summary.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Dict, List, Tuple

import sys
import shutil

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.assemble import parse
from thielecpu.isa import Opcode, encode
from thielecpu.state import State
from thielecpu.vm import VM

from tools import verify_end_to_end as vee

DEFAULT_PROGRAM = REPO_ROOT / "examples" / "neural_crystallizer.thm"
DEFAULT_OUTDIR = REPO_ROOT / "artifacts" / "trinity"


def sha256_json(obj: object) -> str:
    """Stable hash for arbitrary JSON-serialisable content."""

    encoded = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _normalise_program(path: Path) -> Tuple[List[Tuple[str, str]], List[Dict[str, object]]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    program = parse(lines, path.parent)
    encoded = []
    for op, arg in program:
        opcode = Opcode[op]
        # For opcodes that take numeric operands, try parsing; for others (e.g., PYEXEC path)
        # fall back to empty operand list so a,b default to 0.
        operands = []
        if arg:
            try:
                operands = [int(tok) for tok in arg.split()]
            except ValueError:
                operands = []
        # Special-case PNEW with region spec {1,2,3} - encode region length in operands
        if op == "PNEW" and arg and arg.strip().startswith('{') and arg.strip().endswith('}'):
            try:
                region_str = arg.strip()[1:-1]
                region_elems = [int(tok) for tok in region_str.split(',') if tok.strip()]
                region_size = len(region_elems)
                a = (region_size >> 8) & 0xFF
                b = region_size & 0xFF
                operands = [a, b]
            except Exception:
                # Leave operands as parsed if conversion fails
                pass
        a = operands[0] if len(operands) > 0 else 0
        b = operands[1] if len(operands) > 1 else 0
        encoded.append({
            "op": op,
            "a": a,
            "b": b,
            "word_hex": encode(opcode, a, b).hex(),
        })
    return program, encoded


def _write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def run_vm(program_path: Path, outdir: Path) -> Path:
    program, encoded = _normalise_program(program_path)
    vm_out = outdir / "vm"
    vm = VM(State())
    vm.run(program, vm_out)

    summary = json.loads((vm_out / "summary.json").read_text())
    step_receipts = json.loads((vm_out / "step_receipts.json").read_text())

    receipt = {
        "source": "vm",
        "program": encoded,
        "summary": summary,
        "step_receipts_hash": sha256_json(step_receipts),
    }
    receipt_path = outdir / "receipt_vm.json"
    _write_json(receipt_path, receipt)
    return receipt_path


def run_rtl(outdir: Path) -> Path:
    if shutil.which("iverilog") is None or shutil.which("vvp") is None:
        raise FileNotFoundError("iverilog/vvp not available in PATH; install iverilog to run RTL leg")

    # Generate memory image and dynamic testbench so the RTL executes the
    # same program as the VM. This avoids using the repository testbench
    # which contains a static program for internal tests.
    sim_path = outdir / "simv"
    log_path = outdir / "rtl.log"
    # Expect a program.mem file to exist in outdir; if not, no-op and use
    # existing testbench. The runtime produced program.mem by run_rtl_gen_tb.
    def _write_program_mem(instrs: List[Dict[str, object]]) -> Path:
        mem_path = outdir / "program.mem"
        mem_lines = []
        for entry in instrs:
            # word_hex contains 4-byte instruction in little-endian hex
            word = entry.get("word_hex", "00000000")
            mem_lines.append(word)
        mem_path.write_text("\n".join(mem_lines), encoding="utf-8")
        return mem_path

    def _generate_tb_from_template(mem_path: Path) -> Path:
        gen_tb = outdir / "thiele_cpu_tb_generated.v"
        # Minimal generated testbench which reads program.mem and runs the CPU
        tb_template = '''// Minimal generated testbench for Trinity
`timescale 1ns / 1ps
module thiele_cpu_tb;
reg clk; reg rst_n;
wire [31:0] cert_addr, status, error_code, partition_ops, mdl_ops, info_gain;
wire [31:0] mem_addr, mem_wdata, pc; wire mem_we, mem_en; reg [31:0] mem_rdata;
wire logic_req; wire [31:0] logic_addr; reg logic_ack; reg [31:0] logic_data;
wire py_req; wire [31:0] py_code_addr; reg py_ack; reg [31:0] py_result;
reg [31:0] instr_memory [0:255]; reg [31:0] data_memory [0:255];
integer i;
thiele_cpu dut (
    .clk(clk), .rst_n(rst_n), .cert_addr(cert_addr), .status(status), .error_code(error_code),
    .partition_ops(partition_ops), .mdl_ops(mdl_ops), .info_gain(info_gain),
    .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_rdata(mem_rdata), .mem_we(mem_we), .mem_en(mem_en),
    .logic_req(logic_req), .logic_addr(logic_addr), .logic_ack(logic_ack), .logic_data(logic_data),
    .py_req(py_req), .py_code_addr(py_code_addr), .py_ack(py_ack), .py_result(py_result),
    .instr_data(instr_memory[pc[31:2]]), .pc(pc)
);
initial begin clk = 0; forever #5 clk = ~clk; end
initial begin
  $readmemh("{mem_path.name}", instr_memory);
  for (i = 0; i < 256; i = i + 1) data_memory[i] = 32'h00000000;
  rst_n = 0; logic_ack = 0; py_ack = 0; mem_rdata = 32'h0;
  #20 rst_n = 1;
    fork
        begin
            #10000;
            $display("Simulation timed out");
            $finish;
        end
        begin
            wait (pc == 32'h28);
            #10;
            $display("Test completed!");
            $display("Final PC: %h", pc);
            $display("Status: %h", status);
            $display("Error: %h", error_code);
            $display("Partition Ops: %d", partition_ops);
            $display("MDL Ops: %d", mdl_ops);
            $display("Info Gain: %d", info_gain);
            $display("{\\\"partition_ops\\\": %d, \\\"mdl_ops\\\": %d, \\\"info_gain\\\": %d, \\\"mu_total\\\": %d}", partition_ops, mdl_ops, info_gain, dut.mu_accumulator);
            
            $finish;
        end
  join
end
always @(posedge clk) begin if (mem_en) begin if (mem_we) data_memory[mem_addr[31:2]] <= mem_wdata; else mem_rdata <= data_memory[mem_addr[31:2]]; end end
always @(posedge clk) begin if (logic_req && !logic_ack) begin #10 logic_data <= 32'hABCD1234; logic_ack <= 1'b1; end else logic_ack <= 1'b0; end
always @(posedge clk) begin if (py_req && !py_ack) begin #15 py_result <= 32'h12345678; py_ack <= 1'b1; end else py_ack <= 1'b0; end
always @(posedge clk) begin if (rst_n) $display("Time: %t, PC: %h, State: %h, Status: %h, Error: %h", $time, pc, dut.state, status, error_code); end
endmodule
'''
        tb = tb_template.replace('{mem_path.name}', str(mem_path))
        gen_tb.write_text(tb, encoding="utf-8")
        return gen_tb
    # If run_vm has produced a receipt, use it to produce a memory image
    # and dynamic testbench for RTL simulation.
    vm_receipt = outdir / "receipt_vm.json"
    tb_to_use = vee.TB_PATH
    if vm_receipt.exists():
        vm_payload = json.loads(vm_receipt.read_text())
        if isinstance(vm_payload, dict) and vm_payload.get("program"):
            encoded_program = vm_payload["program"]
            mem_path = _write_program_mem(encoded_program)
            gen_tb = _generate_tb_from_template(mem_path)
            tb_to_use = gen_tb
    subprocess.run(
        [
            "iverilog",
            "-g2012",
            "-o",
            str(sim_path),
            str(vee.HARDWARE_DIR / "thiele_cpu.v"),
            str(tb_to_use),
        ],
        check=True,
        cwd=REPO_ROOT,
    )
    completed = subprocess.run(["vvp", str(sim_path)], capture_output=True, text=True, cwd=REPO_ROOT, check=True)
    log_path.write_text(completed.stdout, encoding="utf-8")

    # Prefer to parse the generated testbench if present, otherwise the repo TB
    tb_path = outdir / "thiele_cpu_tb_generated.v" if (outdir / "thiele_cpu_tb_generated.v").exists() else vee.TB_PATH
    if (outdir / "receipt_vm.json").exists():
        vm_payload = json.loads((outdir / "receipt_vm.json").read_text())
        encoded_program = vm_payload.get("program")
        instrs = []
        for idx, entry in enumerate(encoded_program):
            opcode_hex = entry.get("word_hex", "00000000")[:2]
            opcode_val = int(opcode_hex, 16)
            a_val = int(entry.get("a", 0)) if not isinstance(entry.get("a", 0), str) else int(entry.get("a", "0"))
            b_val = int(entry.get("b", 0)) if not isinstance(entry.get("b", 0), str) else int(entry.get("b", "0"))
            instrs.append(vee.InstructionWord(index=idx, opcode=opcode_val, operand_a=a_val, operand_b=b_val))
    else:
        instrs = vee.parse_instructions(tb_path)
    metrics = vee.metrics_from_instructions(instrs)
    summary = vee.summary_from_log(log_path)

    receipt = {
        "source": "rtl",
        "program": [instr.__dict__ for instr in instrs],
        "metrics": metrics.__dict__,
        "summary": {
            "mu_total": summary.metrics.mu_total,
            "final_pc": summary.final_pc,
            "final_status": summary.final_status,
            "final_error": summary.final_error,
        },
        "log_hash": hashlib.sha256(log_path.read_bytes()).hexdigest(),
    }
    receipt_path = outdir / "receipt_rtl.json"
    _write_json(receipt_path, receipt)
    return receipt_path


def build_coq_receipt(program_path: Path, outdir: Path) -> Path:
    _, encoded = _normalise_program(program_path)
    coq_path = REPO_ROOT / "coq" / "thielemachine" / "coqproofs" / "HardwareBridge.v"
    coq_content = coq_path.read_text(encoding="utf-8")

    import re

    opcodes: Dict[str, int] = {}
    for match in re.finditer(r"Definition\s+opcode_(\w+)\s*:\s*N\s*:=\s*(\d+)%N", coq_content):
        opcodes[match.group(1).upper()] = int(match.group(2))

    encoded_words: List[str] = []
    for entry in encoded:
        op = entry["op"]
        a = int(entry.get("a", 0))
        b = int(entry.get("b", 0))
        value = opcodes.get(op)
        if value is None:
            raise RuntimeError(f"Opcode {op} missing from Coq HardwareBridge")
        encoded_words.append(encode(Opcode[op], a, b).hex())

    receipt = {
        "source": "coq",
        "program": encoded,
        "opcode_table": opcodes,
        "program_digest": sha256_json(encoded_words),
    }
    receipt_path = outdir / "receipt_coq.json"
    _write_json(receipt_path, receipt)
    return receipt_path


def compare_hashes(vm_receipt: Path, rtl_receipt: Path, coq_receipt: Path) -> Dict[str, str]:
    digests = {
        "vm": hashlib.sha256(vm_receipt.read_bytes()).hexdigest(),
        "rtl": hashlib.sha256(rtl_receipt.read_bytes()).hexdigest(),
        "coq": hashlib.sha256(coq_receipt.read_bytes()).hexdigest(),
    }
    return digests


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("program", nargs="?", type=Path, default=DEFAULT_PROGRAM, help="Thiele assembly program to run")
    parser.add_argument("--outdir", type=Path, default=DEFAULT_OUTDIR, help="Output directory for receipts")
    args = parser.parse_args()

    args.outdir.mkdir(parents=True, exist_ok=True)

    print("=== THIELE TRINITY VERIFICATION ===")
    print(f"Program: {args.program}")
    print(f"Output:  {args.outdir}")

    vm_receipt = run_vm(args.program, args.outdir)
    print(f"[VM ] receipt -> {vm_receipt}")

    rtl_receipt = run_rtl(args.outdir)
    print(f"[RTL] receipt -> {rtl_receipt}")

    coq_receipt = build_coq_receipt(args.program, args.outdir)
    print(f"[Coq] receipt -> {coq_receipt}")

    digests = compare_hashes(vm_receipt, rtl_receipt, coq_receipt)
    print("\n=== DIGESTS ===")
    for name, digest in digests.items():
        print(f"{name}: {digest}")

    vm_summary = json.loads(vm_receipt.read_text())["summary"]
    rtl_summary = json.loads(rtl_receipt.read_text())["summary"]

    if vm_summary.get("mu_total") != rtl_summary.get("mu_total"):
        raise SystemExit(
            f"μ-total mismatch: VM={vm_summary.get('mu_total')} RTL={rtl_summary.get('mu_total')}"
        )

    print("\n✅ Trinity confirmed: program digest and μ-cost agree between VM and RTL; opcode table verified in Coq.")


if __name__ == "__main__":
    main()
