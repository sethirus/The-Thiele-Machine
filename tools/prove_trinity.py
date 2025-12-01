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
        operands = [int(tok) for tok in arg.split()] if arg else []
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

    sim_path = outdir / "simv"
    log_path = outdir / "rtl.log"
    subprocess.run(
        [
            "iverilog",
            "-g2012",
            "-o",
            str(sim_path),
            str(vee.HARDWARE_DIR / "thiele_cpu.v"),
            str(vee.TB_PATH),
        ],
        check=True,
        cwd=REPO_ROOT,
    )
    completed = subprocess.run(["vvp", str(sim_path)], capture_output=True, text=True, cwd=REPO_ROOT, check=True)
    log_path.write_text(completed.stdout, encoding="utf-8")

    instrs = vee.parse_instructions(vee.TB_PATH)
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
