#!/usr/bin/env python3
"""Batch-run all .asm programs in examples/ through the Thiele CPU VM.

For each program:
  1. Assemble with thielecpu.assembler
  2. Run in the debugger VM
  3. Report final state (halted, registers, mu, cycles)
"""
from __future__ import annotations
import sys
from pathlib import Path

# Allow running from project root
sys.path.insert(0, str(Path(__file__).parent.parent))

from thielecpu.assembler import Assembler
from thielecpu.debugger import ThieleVM

EXAMPLES_DIR = Path(__file__).parent

PASS = "\033[32mPASS\033[0m"
FAIL = "\033[31mFAIL\033[0m"
WARN = "\033[33mWARN\033[0m"


def run_program(asm_file: Path, max_cycles: int = 100_000) -> dict:
    """Assemble and run a program, return result dict."""
    src = asm_file.read_text()
    asm = Assembler()
    try:
        instr_hex, data_hex = asm.assemble(src, str(asm_file))
    except Exception as e:
        return {"status": "asm_error", "error": str(e)}

    if asm.errors:
        return {"status": "asm_error", "errors": asm.errors}

    instr_words = [int(h, 16) for h in instr_hex]
    data_words = [int(h, 16) for h in data_hex]

    vm = ThieleVM()
    vm.load_program(instr_words, data_words)

    for _ in range(max_cycles):
        if vm.halted or vm.err:
            break
        vm.step()

    return {
        "status": "ok",
        "halted": vm.halted,
        "err": vm.err,
        "error_code": vm.error_code,
        "cycles": vm.cycle,
        "mu": vm.mu,
        "regs": list(vm.regs[:8]),  # first 8 regs for display
        "instructions": len(instr_words) - instr_words.count(0),
        "timeout": not (vm.halted or vm.err),
    }


def main() -> int:
    asm_files = sorted(EXAMPLES_DIR.glob("*.asm"))
    if not asm_files:
        print("No .asm files found in", EXAMPLES_DIR)
        return 1

    failures = 0
    warnings = 0
    print(f"{'Program':<30} {'Result':<6} {'Cycles':>7}  {'Mu':>10}  Notes")
    print("-" * 75)

    for f in asm_files:
        r = run_program(f)
        name = f.stem

        if r["status"] == "asm_error":
            tag = FAIL
            note = f"ASM ERROR: {r.get('errors', r.get('error', ''))}"
            failures += 1
        elif r["timeout"]:
            tag = WARN
            note = f"timeout after {r['cycles']} cycles"
            warnings += 1
        elif r["err"]:
            # Bianchi halts are expected for bianchi_violation
            if "bianchi" in name or "violation" in name:
                tag = PASS
                note = f"expected halt  err_code=0x{r['error_code']:08x}"
            else:
                tag = WARN
                note = f"unexpected err  err_code=0x{r['error_code']:08x}"
                warnings += 1
        elif r["halted"]:
            tag = PASS
            note = ""
        else:
            tag = WARN
            note = "did not halt"
            warnings += 1

        mu_str = str(r.get("mu", "-"))
        cycles_str = str(r.get("cycles", "-"))
        print(f"  {name:<28} {tag}  {cycles_str:>7}  {mu_str:>10}  {note}")

    print("-" * 75)
    total = len(asm_files)
    ok = total - failures - warnings
    print(f"  {ok}/{total} PASS   {warnings} WARN   {failures} FAIL")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
