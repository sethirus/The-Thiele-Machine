#!/usr/bin/env python3
"""Batch-run example .asm programs through the current extracted VM API.

For each program:
1. Assemble with scripts/thiele_asm.py machinery
2. Execute via build/thiele_vm.run_vm_trace
3. Print final state summary (pc, mu, err, selected registers)
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Dict, List

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from build.thiele_vm import _run_python
from scripts.thiele_asm import AssemblerError, _preprocess_source, assemble

EXAMPLES_DIR = Path(__file__).resolve().parent
PROGRAMS_DIR = EXAMPLES_DIR / "programs"
EXPECTATIONS_PATH = EXAMPLES_DIR / "run_all_expectations.json"

PASS = "\033[32mPASS\033[0m"
FAIL = "\033[31mFAIL\033[0m"
WARN = "\033[33mWARN\033[0m"


def _trace_lines(source_text: str, fuel_default: int = 256) -> List[str]:
    preprocessed, _ = _preprocess_source(source_text)
    fuel = fuel_default
    for raw in source_text.splitlines():
        line = raw.strip()
        if not line:
            continue
        for c in ("#", ";", "//"):
            idx = line.find(c)
            if idx >= 0:
                line = line[:idx].strip()
        if not line:
            continue
        parts = line.split()
        if parts and parts[0].upper() == "FUEL" and len(parts) > 1:
            try:
                fuel = int(parts[1], 0)
            except ValueError:
                pass
            break
    return [f"FUEL {fuel}"] + preprocessed


def _instruction_count(lines: List[str]) -> int:
    return len([ln for ln in lines if not ln.startswith("INIT_") and not ln.startswith("FUEL")])


def run_program(asm_file: Path) -> Dict[str, Any]:
    src = asm_file.read_text(encoding="utf-8")
    try:
        instructions, data_memory, metadata = assemble(src)
    except AssemblerError as exc:
        return {"status": "asm_error", "error": str(exc)}
    except Exception as exc:  # pragma: no cover - defensive
        return {"status": "asm_error", "error": f"unexpected assembler failure: {exc}"}

    lines = _trace_lines(src, fuel_default=int(metadata.get("fuel", 256)))
    fuel = int(metadata.get("fuel", 256))

    try:
        final = _run_python(lines, fuel=fuel)
    except Exception as exc:
        return {
            "status": "run_error",
            "error": str(exc),
            "instructions": _instruction_count(lines),
            "fuel": fuel,
        }

    instr_count = _instruction_count(lines)
    expects_halt = any(ln.split()[0].upper() == "HALT" for ln in lines if not ln.startswith("INIT_") and not ln.startswith("FUEL"))
    halted_heuristic = expects_halt and final.pc in {max(instr_count - 1, 0), instr_count}

    return {
        "status": "ok",
        "err": bool(final.err),
        "pc": int(final.pc),
        "mu": int(final.mu),
        "halted": bool(halted_heuristic),
        "instructions": instr_count,
        "fuel": fuel,
        "regs": list(final.regs[:8]),
    }


def _discover_programs() -> List[Path]:
    files = []
    if PROGRAMS_DIR.exists():
        files.extend(sorted(PROGRAMS_DIR.glob("*.asm")))
    files.extend(sorted(EXAMPLES_DIR.glob("*.asm")))
    # Preserve order while deduplicating
    seen = set()
    ordered: List[Path] = []
    for path in files:
        if path not in seen:
            ordered.append(path)
            seen.add(path)
    return ordered


def _program_label(path: Path) -> str:
    return path.relative_to(EXAMPLES_DIR).as_posix()


def _expectation_for(path: Path, expectations: Dict[str, str]) -> str | None:
    label = _program_label(path)
    if label in expectations:
        return expectations[label]
    return expectations.get(path.stem)


def main() -> int:
    expectations: Dict[str, str] = {}
    if EXPECTATIONS_PATH.exists():
        try:
            raw = json.loads(EXPECTATIONS_PATH.read_text(encoding="utf-8"))
            if isinstance(raw, dict):
                expectations = {str(k): str(v) for k, v in raw.items()}
        except Exception:
            expectations = {}

    asm_files = _discover_programs()
    if not asm_files:
        print(f"No .asm files found under {PROGRAMS_DIR} or {EXAMPLES_DIR}")
        return 1

    failures = 0
    warnings = 0
    expected = 0
    print(f"{'Program':<30} {'Result':<6} {'PC':>5} {'Mu':>10}  Notes")
    print("-" * 80)

    for asm_file in asm_files:
        result = run_program(asm_file)
        name = _program_label(asm_file)
        expected_status = _expectation_for(asm_file, expectations)

        pc = str(result.get("pc", "-"))
        mu = str(result.get("mu", "-"))

        if result["status"] == "asm_error":
            tag = FAIL
            note = f"ASM ERROR: {result.get('error', '')}"
            failures += 1
        elif result["status"] == "run_error":
            tag = FAIL
            note = f"RUN ERROR: {result.get('error', '')}"
            failures += 1
        elif result["err"]:
            warning_code = "vm_err"
            if "bianchi" in asm_file.stem or "violation" in asm_file.stem:
                tag = PASS
                note = "expected VM error pattern"
            elif expected_status == warning_code:
                tag = PASS
                note = f"expected warning ({warning_code})"
                expected += 1
            else:
                tag = WARN
                note = "unexpected vm_err=true"
                warnings += 1
        elif result["halted"]:
            tag = PASS
            note = ""
        else:
            warning_code = "no_halt_heuristic"
            if expected_status == warning_code:
                tag = PASS
                note = f"expected warning ({warning_code})"
                expected += 1
            else:
                tag = WARN
                note = f"did not reach halt-pc heuristic (fuel={result.get('fuel')})"
                warnings += 1

        print(f"  {name:<28} {tag}  {pc:>5} {mu:>10}  {note}")

    print("-" * 80)
    total = len(asm_files)
    ok = total - failures - warnings
    print(f"  {ok}/{total} PASS   {expected} EXPECTED   {warnings} WARN   {failures} FAIL")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
