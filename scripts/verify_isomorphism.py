#!/usr/bin/env python3
"""Three-layer isomorphism verifier (Python, Coq extraction, Verilog RTL)."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.state import ModuleId, State
from tests.test_three_layer_isomorphism import Instruction, ProgramTrace, execute_python

BUILD_DIR = REPO_ROOT / "build"
COQ_DIR = REPO_ROOT / "coq"
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"
RTL_DIR = HARDWARE_DIR / "rtl"
TB_DIR = HARDWARE_DIR / "testbench"


@dataclass
class VerificationResult:
    program_length: int
    layers_tested: list[str]
    python_trace: dict[str, Any]
    coq_trace: dict[str, Any] | None
    verilog_trace: dict[str, Any] | None
    isomorphic: bool
    discrepancies: list[str]




def _predicate_matches(pred_byte: int, x: int) -> bool:
    predicate = pred_byte & 0xFF
    pred_mode = (predicate >> 6) & 0x3
    pred_param = predicate & 0x3F
    element_value = int(x) & 0xFFFFFFFF

    if pred_mode == 0b00:
        return (element_value & 1) == (pred_param & 1)
    if pred_mode == 0b01:
        return element_value >= pred_param
    if pred_mode == 0b10:
        return (element_value & (1 << pred_param)) != 0
    divisor = pred_param + 1
    if (divisor & pred_param) != 0:
        return False
    return (element_value & pred_param) == 0


def _split_regions(state: State, module: ModuleId, pred_operand: Any) -> tuple[set[int], set[int]]:
    region = state.regions.modules[int(module)]
    if callable(pred_operand):
        pred = pred_operand
    elif isinstance(pred_operand, int):
        pred = lambda x, pb=pred_operand: _predicate_matches(pb, x)
    else:
        raise ValueError(f"Unsupported PSPLIT predicate operand: {pred_operand!r}")

    left = {x for x in region if pred(x)}
    right = set(region) - left
    return left, right
def _trace_to_dict(trace: ProgramTrace) -> dict[str, Any]:
    return {
        "final_mu": trace.final_mu,
        "final_modules": trace.final_modules,
        "step_mu": trace.step_mu,
        "final_regions": trace.final_regions,
    }


def load_program(program_file: Path) -> list[Instruction]:
    data = json.loads(program_file.read_text())
    instructions: list[Instruction] = []
    for instr_data in data["instructions"]:
        opcode = instr_data["opcode"]
        operands = tuple(instr_data.get("operands", []))
        cost = int(instr_data.get("cost", 0))

        if opcode == "PNEW":
            operands = (set(operands[0]),)
        elif opcode in {"PSPLIT", "PMERGE"}:
            operands = tuple(ModuleId(int(x)) if isinstance(x, int) else x for x in operands)
        instructions.append(Instruction(opcode, operands, cost))
    return instructions


def _ensure_coq_runner() -> Path:
    runner = BUILD_DIR / "extracted_vm_runner"
    if runner.exists():
        return runner

    subprocess.run(["make", "-C", str(COQ_DIR), "Extraction.vo"], check=True)
    subprocess.run(
        [
            "ocamlc",
            "-I",
            str(BUILD_DIR),
            "-o",
            str(runner),
            str(BUILD_DIR / "thiele_core.mli"),
            str(BUILD_DIR / "thiele_core.ml"),
            str(REPO_ROOT / "tools" / "extracted_vm_runner.ml"),
        ],
        check=True,
    )
    return runner


def _region_token(indices: set[int]) -> str:
    return "{" + ",".join(str(i) for i in sorted(indices)) + "}"


def _program_to_coq_trace_lines(program: list[Instruction]) -> list[str]:
    lines: list[str] = []
    state = State()

    for instr in program:
        if instr.opcode == "PNEW":
            region = instr.operands[0]
            if not isinstance(region, set):
                raise ValueError("Coq runner PNEW expects set operand")
            lines.append(f"PNEW {_region_token(region)} {instr.cost}")
            state.pnew(region, charge_discovery=True)
        elif instr.opcode == "PSPLIT":
            module, pred_operand = instr.operands
            left, right = _split_regions(state, module, pred_operand)
            lines.append(
                f"PSPLIT {int(module)} {_region_token(left)} {_region_token(right)} {instr.cost}"
            )
            state.psplit(module, lambda x, p=pred_operand: p(x) if callable(p) else _predicate_matches(int(p), x), cost=instr.cost)
        elif instr.opcode == "PMERGE":
            m1, m2 = instr.operands
            lines.append(f"PMERGE {int(m1)} {int(m2)} {instr.cost}")
            state.pmerge(m1, m2, cost=instr.cost)
        elif instr.opcode == "HALT":
            lines.append(f"HALT {instr.cost}")
        else:
            raise ValueError(f"Coq runner unsupported opcode: {instr.opcode}")
    if not lines or not lines[-1].startswith("HALT"):
        lines.append("HALT 0")
    return lines


def execute_coq(program: list[Instruction]) -> ProgramTrace:
    runner = _ensure_coq_runner()
    trace_lines = _program_to_coq_trace_lines(program)
    with tempfile.TemporaryDirectory() as td:
        trace_path = Path(td) / "trace.txt"
        trace_path.write_text("\n".join(trace_lines) + "\n")
        result = subprocess.run(
            [str(runner), str(trace_path)], capture_output=True, text=True, check=True,
            env={**os.environ, "OCAMLRUNPARAM": os.environ.get("OCAMLRUNPARAM", "l=64M")},
        )
    payload = json.loads(result.stdout[result.stdout.find("{"):])
    modules = payload["graph"]["modules"]
    regions = {int(m["id"]): sorted(int(x) for x in m["region"]) for m in modules}
    return ProgramTrace(program=program, final_mu=int(payload["mu"]), final_modules=len(regions), final_regions=regions, step_mu=[])


def _encode_word(op: int, a: int = 0, b: int = 0, cost: int = 0) -> int:
    return ((op & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (cost & 0xFF)


def _program_to_words(program: list[Instruction]) -> list[int]:
    words: list[int] = []
    for instr in program:
        if instr.opcode == "PNEW":
            region = instr.operands[0]
            if not isinstance(region, set) or len(region) != 1:
                raise ValueError("Verilog path supports singleton PNEW regions only")
            words.append(_encode_word(0x00, next(iter(region)), 0, instr.cost))
        elif instr.opcode == "PSPLIT":
            module, pred_operand = instr.operands
            if not isinstance(pred_operand, int):
                raise ValueError("Verilog PSPLIT requires integer predicate-byte operand")
            words.append(_encode_word(0x01, int(module), int(pred_operand), instr.cost))
        elif instr.opcode == "PMERGE":
            m1, m2 = instr.operands
            words.append(_encode_word(0x02, int(m1), int(m2), instr.cost))
        elif instr.opcode == "HALT":
            words.append(_encode_word(0xFF, 0, 0, instr.cost))
        else:
            raise ValueError(f"Verilog path currently supports PNEW/PMERGE/HALT only, got {instr.opcode}")
    if not words or ((words[-1] >> 24) & 0xFF) != 0xFF:
        words.append(_encode_word(0xFF, 0, 0, 0))
    return words


def execute_verilog(program: list[Instruction]) -> ProgramTrace:
    words = _program_to_words(program)
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        sim_out = td_path / "tb.out"
        prog_hex = td_path / "prog.hex"
        data_hex = td_path / "data.hex"

        prog_hex.write_text("\n".join(f"{w:08x}" for w in words) + "\n")
        data_hex.write_text(("00000000\n") * 256)

        subprocess.run(
            [
                "iverilog", "-g2012", "-Irtl", "-o", str(sim_out),
                str(RTL_DIR / "thiele_cpu_unified.v"),
                str(TB_DIR / "thiele_cpu_tb.v"),
            ],
            cwd=HARDWARE_DIR,
            capture_output=True,
            text=True,
            check=True,
        )
        run = subprocess.run(
            ["vvp", str(sim_out), f"+PROGRAM={prog_hex}", f"+DATA={data_hex}"],
            cwd=td_path,
            capture_output=True,
            text=True,
            check=True,
        )

    out = run.stdout
    start = out.find('{\n  "status":')
    if start == -1:
        start = out.find('{"status":')
    if start == -1:
        raise RuntimeError(f"No JSON payload found in Verilog output:\n{out[:1000]}")
    decoder = json.JSONDecoder()
    payload, _ = decoder.raw_decode(out[start:])

    regions: dict[int, list[int]] = {}
    for module in payload.get("modules", []):
        mid = int(module.get("id", -1))
        region = sorted(int(x) for x in module.get("region", []))
        # Include ALL modules, even those with empty regions (matches Coq semantics)
        if mid >= 0:
            regions[mid] = region

    return ProgramTrace(
        program=program,
        final_mu=int(payload.get("mu", 0)),
        final_modules=len(regions),
        final_regions=regions,
        step_mu=[],
    )


def verify_layers(program: list[Instruction], layers: list[str], verbose: bool = False) -> VerificationResult:
    discrepancies: list[str] = []
    py_trace = execute_python(program)

    coq_trace = None
    verilog_trace = None

    if "coq" in layers:
        coq_trace = execute_coq(program)
        if py_trace.final_mu != coq_trace.final_mu:
            discrepancies.append(f"μ mismatch Python={py_trace.final_mu}, Coq={coq_trace.final_mu}")
        if py_trace.final_modules != coq_trace.final_modules:
            discrepancies.append(f"module mismatch Python={py_trace.final_modules}, Coq={coq_trace.final_modules}")
        if py_trace.final_regions != coq_trace.final_regions:
            discrepancies.append("final region map mismatch between Python and Coq")

    if "verilog" in layers:
        verilog_trace = execute_verilog(program)
        if py_trace.final_mu != verilog_trace.final_mu:
            discrepancies.append(f"μ mismatch Python={py_trace.final_mu}, Verilog={verilog_trace.final_mu}")
        if py_trace.final_modules != verilog_trace.final_modules:
            discrepancies.append(f"module mismatch Python={py_trace.final_modules}, Verilog={verilog_trace.final_modules}")
        if py_trace.final_regions != verilog_trace.final_regions:
            discrepancies.append("final region map mismatch between Python and Verilog")

    if verbose:
        print("Python:", _trace_to_dict(py_trace))
        if coq_trace:
            print("Coq:", _trace_to_dict(coq_trace))
        if verilog_trace:
            print("Verilog:", _trace_to_dict(verilog_trace))

    return VerificationResult(
        program_length=len(program),
        layers_tested=layers,
        python_trace=_trace_to_dict(py_trace),
        coq_trace=_trace_to_dict(coq_trace) if coq_trace else None,
        verilog_trace=_trace_to_dict(verilog_trace) if verilog_trace else None,
        isomorphic=not discrepancies,
        discrepancies=discrepancies,
    )


def generate_report(result: VerificationResult, output_file: Path | None = None) -> str:
    lines = [
        "=" * 80,
        "THREE-LAYER ISOMORPHISM VERIFICATION REPORT",
        "=" * 80,
        f"Program Length: {result.program_length} instructions",
        f"Layers Tested: {', '.join(result.layers_tested)}",
        "",
        f"Python μ={result.python_trace['final_mu']}, modules={result.python_trace['final_modules']}",
    ]
    if result.coq_trace:
        lines.append(f"Coq μ={result.coq_trace['final_mu']}, modules={result.coq_trace['final_modules']}")
    if result.verilog_trace:
        lines.append(f"Verilog μ={result.verilog_trace['final_mu']}, modules={result.verilog_trace['final_modules']}")
    lines.append("")
    if result.isomorphic:
        lines.extend(["✅ STATUS: ISOMORPHIC", "All tested layers produce equivalent final states."])
    else:
        lines.append("❌ STATUS: DISCREPANCIES FOUND")
        lines.extend([f"  - {d}" for d in result.discrepancies])
    lines.append("=" * 80)
    report = "\n".join(lines)

    if output_file:
        output_file.write_text(report)
    else:
        print(report)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify three-layer isomorphism")
    parser.add_argument("--program", type=Path, help="Program file (JSON format)")
    parser.add_argument("--layers", default="python,coq,verilog", help="Layers to test (comma-separated)")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.program:
        program = load_program(args.program)
    else:
        print("No program specified, using default cross-layer-safe program")
        program = [
            Instruction("PNEW", ({0},), cost=1),
            Instruction("PNEW", ({1},), cost=1),
            Instruction("PMERGE", (ModuleId(1), ModuleId(2)), cost=4),
            Instruction("HALT", tuple(), cost=0),
        ]

    layers = [x.strip() for x in args.layers.split(",") if x.strip()]
    print(f"Verifying isomorphism across layers: {', '.join(layers)}")
    result = verify_layers(program, layers, verbose=args.verbose)
    generate_report(result, args.output)
    raise SystemExit(0 if result.isomorphic else 1)


if __name__ == "__main__":
    main()
