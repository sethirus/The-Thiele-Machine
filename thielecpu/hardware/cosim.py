"""Verilog co-simulation harness for 3-way bisimulation testing.

Compiles and runs the Thiele CPU RTL, parses the JSON output, and returns a
canonical VMState that can be compared against the Coq-extracted OCaml runner
and the Python VM.

Supported simulators:
    - iverilog + vvp (default)
    - verilator (optional)

The harness converts a text-format program (same format as the OCaml runner)
into a hex instruction memory image, runs the testbench, and scrapes the
structured JSON output from $display statements.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

# Canonical opcode encoding — MUST match generated_opcodes.vh / isa.py / Coq
OPCODES: Dict[str, int] = {
    "PNEW": 0x00,
    "PSPLIT": 0x01,
    "PMERGE": 0x02,
    "LASSERT": 0x03,
    "LJOIN": 0x04,
    "MDLACC": 0x05,
    "PDISCOVER": 0x06,
    "XFER": 0x07,
    "PYEXEC": 0x08,
    "CHSH_TRIAL": 0x09,
    "XOR_LOAD": 0x0A,
    "XOR_ADD": 0x0B,
    "XOR_SWAP": 0x0C,
    "XOR_RANK": 0x0D,
    "EMIT": 0x0E,
    "REVEAL": 0x0F,
    "ORACLE_HALTS": 0x10,
    "HALT": 0xFF,
}

RTL_DIR = Path(__file__).resolve().parent / "rtl"
TB_DIR = Path(__file__).resolve().parent / "testbench"


def _command_available(cmd: str) -> bool:
    try:
        subprocess.run([cmd, "--version"], capture_output=True, timeout=5)
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False
    return True


def _parse_brace_list(s: str) -> List[int]:
    """Parse {1,2,3} format into a list of ints."""
    s = s.strip()
    if s.startswith("{") and s.endswith("}"):
        inner = s[1:-1].strip()
        if not inner:
            return []
        return [int(x.strip()) for x in inner.split(",") if x.strip()]
    raise ValueError(f"Invalid brace list: {s}")


def _encode_instruction(op: str, operand_a: int = 0, operand_b: int = 0,
                        cost: int = 0) -> int:
    """Encode a 32-bit instruction word: [opcode:8][a:8][b:8][cost:8]."""
    opcode = OPCODES.get(op.upper())
    if opcode is None:
        raise ValueError(f"Unknown opcode: {op}")
    return ((opcode & 0xFF) << 24) | ((operand_a & 0xFF) << 16) | \
           ((operand_b & 0xFF) << 8) | (cost & 0xFF)


def program_to_hex(program: str) -> Tuple[List[str], List[str]]:
    """Convert text program to hex instruction and data memory images.

    Returns (instr_hex_lines, data_hex_lines) suitable for $readmemh.
    """
    instrs: List[int] = []
    data_mem: Dict[int, int] = {}

    for line in program.strip().split("\n"):
        line = line.strip()
        if not line or line.startswith("#") or line.startswith(";"):
            continue
        if line.startswith("FUEL"):
            continue

        parts = line.split(maxsplit=1)
        op = parts[0].upper()
        arg = parts[1] if len(parts) > 1 else ""

        if op == "INIT_MEM":
            mem_parts = arg.split()
            if len(mem_parts) >= 2:
                data_mem[int(mem_parts[0])] = int(mem_parts[1])
            continue
        if op == "INIT_REG":
            # Verilog testbench doesn't support INIT_REG via hex file.
            # Registers are zero-initialized and set via XFER/XOR_LOAD.
            continue

        if op == "PNEW":
            # PNEW {region} cost
            m = re.match(r"\{([^}]*)\}\s+(\d+)", arg)
            if m:
                region = [int(x.strip()) for x in m.group(1).split(",") if x.strip()]
                cost = int(m.group(2))
                # Encode: operand_a = first region element, operand_b = region size
                a = region[0] if region else 0
                b = len(region)
                instrs.append(_encode_instruction("PNEW", a, b, cost))
            else:
                instrs.append(_encode_instruction("PNEW", 0, 0, 0))
        elif op == "PSPLIT":
            # PSPLIT mid {left} {right} cost
            m = re.match(r"(\d+)\s+\{[^}]*\}\s+\{[^}]*\}\s+(\d+)", arg)
            if m:
                mid = int(m.group(1))
                cost = int(m.group(2))
                instrs.append(_encode_instruction("PSPLIT", mid, 0, cost))
            else:
                instrs.append(_encode_instruction("PSPLIT", 0, 0, 0))
        elif op == "PMERGE":
            # PMERGE m1 m2 cost
            merge_parts = arg.split()
            m1 = int(merge_parts[0]) if len(merge_parts) > 0 else 0
            m2 = int(merge_parts[1]) if len(merge_parts) > 1 else 0
            cost = int(merge_parts[2]) if len(merge_parts) > 2 else 0
            instrs.append(_encode_instruction("PMERGE", m1, m2, cost))
        elif op == "MDLACC":
            mdl_parts = arg.split()
            mid = int(mdl_parts[0]) if len(mdl_parts) > 0 else 0
            cost = int(mdl_parts[1]) if len(mdl_parts) > 1 else 0
            instrs.append(_encode_instruction("MDLACC", mid, 0, cost))
        elif op == "XOR_LOAD":
            xor_parts = arg.split()
            dst = int(xor_parts[0]) if len(xor_parts) > 0 else 0
            addr = int(xor_parts[1]) if len(xor_parts) > 1 else 0
            cost = int(xor_parts[2]) if len(xor_parts) > 2 else 0
            instrs.append(_encode_instruction("XOR_LOAD", dst, addr, cost))
        elif op == "XOR_ADD":
            xor_parts = arg.split()
            dst = int(xor_parts[0]) if len(xor_parts) > 0 else 0
            src = int(xor_parts[1]) if len(xor_parts) > 1 else 0
            cost = int(xor_parts[2]) if len(xor_parts) > 2 else 0
            instrs.append(_encode_instruction("XOR_ADD", dst, src, cost))
        elif op == "XOR_SWAP":
            xor_parts = arg.split()
            a = int(xor_parts[0]) if len(xor_parts) > 0 else 0
            b = int(xor_parts[1]) if len(xor_parts) > 1 else 0
            cost = int(xor_parts[2]) if len(xor_parts) > 2 else 0
            instrs.append(_encode_instruction("XOR_SWAP", a, b, cost))
        elif op == "XOR_RANK":
            xor_parts = arg.split()
            dst = int(xor_parts[0]) if len(xor_parts) > 0 else 0
            src = int(xor_parts[1]) if len(xor_parts) > 1 else 0
            cost = int(xor_parts[2]) if len(xor_parts) > 2 else 0
            instrs.append(_encode_instruction("XOR_RANK", dst, src, cost))
        elif op == "XFER":
            xfer_parts = arg.split()
            dst = int(xfer_parts[0]) if len(xfer_parts) > 0 else 0
            src = int(xfer_parts[1]) if len(xfer_parts) > 1 else 0
            cost = int(xfer_parts[2]) if len(xfer_parts) > 2 else 0
            instrs.append(_encode_instruction("XFER", dst, src, cost))
        elif op == "LASSERT":
            la_parts = arg.split()
            a = int(la_parts[0]) if len(la_parts) > 0 else 0
            b = int(la_parts[1]) if len(la_parts) > 1 else 0
            cost = int(la_parts[2]) if len(la_parts) > 2 else 0
            instrs.append(_encode_instruction("LASSERT", a, b, cost))
        elif op == "LJOIN":
            lj_parts = arg.split()
            a = int(lj_parts[0]) if len(lj_parts) > 0 else 0
            b = int(lj_parts[1]) if len(lj_parts) > 1 else 0
            cost = int(lj_parts[2]) if len(lj_parts) > 2 else 0
            instrs.append(_encode_instruction("LJOIN", a, b, cost))
        elif op == "PDISCOVER":
            pd_parts = arg.split()
            a = int(pd_parts[0]) if len(pd_parts) > 0 else 0
            b = int(pd_parts[1]) if len(pd_parts) > 1 else 0
            cost = int(pd_parts[2]) if len(pd_parts) > 2 else 0
            instrs.append(_encode_instruction("PDISCOVER", a, b, cost))
        elif op == "ORACLE_HALTS":
            oh_parts = arg.split()
            a = int(oh_parts[0]) if len(oh_parts) > 0 else 0
            b = int(oh_parts[1]) if len(oh_parts) > 1 else 0
            cost = int(oh_parts[2]) if len(oh_parts) > 2 else 0
            instrs.append(_encode_instruction("ORACLE_HALTS", a, b, cost))
        elif op == "EMIT":
            emit_parts = arg.split()
            a = int(emit_parts[0]) if len(emit_parts) > 0 else 0
            b = int(emit_parts[1]) if len(emit_parts) > 1 else 0
            cost = int(emit_parts[2]) if len(emit_parts) > 2 else 0
            instrs.append(_encode_instruction("EMIT", a, b, cost))
        elif op == "REVEAL":
            rev_parts = arg.split()
            a = int(rev_parts[0]) if len(rev_parts) > 0 else 0
            b = int(rev_parts[1]) if len(rev_parts) > 1 else 0
            cost = int(rev_parts[2]) if len(rev_parts) > 2 else 0
            instrs.append(_encode_instruction("REVEAL", a, b, cost))
        elif op == "CHSH_TRIAL":
            ch_parts = arg.split()
            a = int(ch_parts[0]) if len(ch_parts) > 0 else 0
            b = int(ch_parts[1]) if len(ch_parts) > 1 else 0
            cost = int(ch_parts[2]) if len(ch_parts) > 2 else 0
            instrs.append(_encode_instruction("CHSH_TRIAL", a, b, cost))
        elif op == "HALT":
            h_parts = arg.split()
            cost = int(h_parts[0]) if len(h_parts) > 0 else 0
            instrs.append(_encode_instruction("HALT", 0, 0, cost))
        else:
            # Generic: try to parse "a b cost"
            gen_parts = arg.split()
            a = int(gen_parts[0]) if len(gen_parts) > 0 else 0
            b = int(gen_parts[1]) if len(gen_parts) > 1 else 0
            cost = int(gen_parts[2]) if len(gen_parts) > 2 else 0
            instrs.append(_encode_instruction(op, a, b, cost))

    # Convert to hex lines
    instr_hex = [f"{w:08X}" for w in instrs]
    # Pad to 256 entries
    while len(instr_hex) < 256:
        instr_hex.append("00000000")

    data_hex: List[str] = []
    for i in range(256):
        data_hex.append(f"{data_mem.get(i, 0):08X}")

    return instr_hex, data_hex


def compile_testbench_iverilog(work_dir: Path) -> Path:
    """Compile the thiele_cpu testbench with iverilog.

    Returns the path to the compiled vvp binary.
    """
    # Single unified RTL file contains all modules:
    #   thiele_cpu, mu_alu, mu_core, receipt_integrity_checker, clz8
    rtl_files = [
        RTL_DIR / "thiele_cpu_unified.v",
        TB_DIR / "thiele_cpu_tb.v",
    ]

    for f in rtl_files:
        if not f.exists():
            raise FileNotFoundError(f"RTL file missing: {f}")

    output = work_dir / "thiele_cpu_tb.vvp"
    cmd = [
        "iverilog",
        "-g2012",  # Enable SystemVerilog support
        "-o", str(output),
        "-I", str(RTL_DIR),
        "-DYOSYS_LITE",  # Use small module tables for fast simulation
    ] + [str(f) for f in rtl_files]

    result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    if result.returncode != 0:
        raise RuntimeError(f"iverilog compilation failed:\n{result.stderr}")
    return output


def compile_testbench_verilator(work_dir: Path) -> Path:
    """Compile the thiele_cpu testbench with Verilator.

    Returns the path to the compiled executable.
    """
    rtl_files = [
        RTL_DIR / "thiele_cpu_unified.v",
        TB_DIR / "thiele_cpu_tb.v",
    ]

    for f in rtl_files:
        if not f.exists():
            raise FileNotFoundError(f"RTL file missing: {f}")

    cmd = [
        "verilator",
        "--binary",
        "--timing",
        "-Wno-fatal",
        "-I" + str(RTL_DIR),
        "-DYOSYS_LITE",
        "--top-module", "thiele_cpu_tb",
    ] + [str(f) for f in rtl_files]

    result = subprocess.run(cmd, cwd=work_dir, capture_output=True, text=True, timeout=120)
    if result.returncode != 0:
        raise RuntimeError(f"verilator compilation failed:\n{result.stderr}")

    binary = work_dir / "obj_dir" / "Vthiele_cpu_tb"
    if not binary.exists():
        raise RuntimeError("verilator compilation did not produce obj_dir/Vthiele_cpu_tb")
    return binary


def run_simulation_iverilog(vvp_binary: Path, program_hex: Path,
                            data_hex: Optional[Path] = None,
                            timeout: int = 30) -> str:
    """Run the compiled testbench and return stdout."""
    cmd = ["vvp", str(vvp_binary)]
    plusargs = [f"+PROGRAM={program_hex}"]
    if data_hex:
        plusargs.append(f"+DATA={data_hex}")
    cmd.extend(plusargs)

    result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if result.returncode != 0 and "timed out" not in result.stdout.lower():
        # Some simulations finish with non-zero exit; check output
        pass
    return result.stdout


def run_simulation_verilator(binary: Path, program_hex: Path,
                             data_hex: Optional[Path] = None,
                             timeout: int = 30) -> str:
    """Run the Verilator-built executable and return stdout."""
    cmd = [str(binary), f"+PROGRAM={program_hex}"]
    if data_hex:
        cmd.append(f"+DATA={data_hex}")
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if result.returncode != 0 and "timed out" not in result.stdout.lower():
        pass
    return result.stdout


def parse_verilog_output(stdout: str) -> Dict[str, Any]:
    """Parse the JSON-like output from the testbench's $display statements.

    The testbench emits a structured block starting with '{' and ending with '}'.
    """
    # Find the JSON block in the output
    lines = stdout.split("\n")
    json_lines: List[str] = []
    in_json = False
    brace_depth = 0

    for line in lines:
        stripped = line.strip()
        if stripped == "{" and not in_json:
            in_json = True
            brace_depth = 1
            json_lines.append(stripped)
            continue
        if in_json:
            json_lines.append(stripped)
            brace_depth += stripped.count("{") - stripped.count("}")
            if brace_depth <= 0:
                break

    if not json_lines:
        raise ValueError(f"No JSON output found in Verilog simulation.\n"
                         f"Full output:\n{stdout[:2000]}")

    json_text = "\n".join(json_lines)

    # The testbench output has trailing commas which aren't valid JSON.
    # Also, module output has a sentinel {id: -1} we need to handle.
    # Clean up trailing commas before ] and }
    json_text = re.sub(r",\s*\]", "]", json_text)
    json_text = re.sub(r",\s*\}", "}", json_text)

    try:
        return json.loads(json_text)
    except json.JSONDecodeError as e:
        raise ValueError(f"Failed to parse Verilog JSON output: {e}\n"
                         f"Cleaned JSON:\n{json_text[:2000]}") from e


def run_verilog(
    program: str,
    timeout: int = 30,
    backend: Optional[str] = None,
) -> Optional[Dict[str, Any]]:
    """Run a program through Verilog simulation and return parsed state.

    Args:
        program: Text-format program (same as OCaml runner input).
        timeout: Simulation timeout in seconds.
        backend: `iverilog` or `verilator`. Defaults to env `THIELE_RTL_SIM`
             or `iverilog` when unset.

    Returns:
        Dict with keys: mu, regs, mem, modules, status, etc.
        None if selected backend is unavailable.
    """
    selected_backend = (backend or os.getenv("THIELE_RTL_SIM", "iverilog")).strip().lower()
    if selected_backend not in {"iverilog", "verilator"}:
        raise ValueError(f"Unsupported RTL backend: {selected_backend}")

    if selected_backend == "iverilog" and not _command_available("iverilog"):
        return None
    if selected_backend == "verilator" and not _command_available("verilator"):
        return None

    instr_hex, data_hex = program_to_hex(program)

    with tempfile.TemporaryDirectory(prefix="thiele_cosim_") as tmpdir:
        work_dir = Path(tmpdir)

        # Write hex files
        prog_hex_path = work_dir / "program.hex"
        data_hex_path = work_dir / "data.hex"
        prog_hex_path.write_text("\n".join(instr_hex) + "\n")
        data_hex_path.write_text("\n".join(data_hex) + "\n")

        if selected_backend == "iverilog":
            compiled = compile_testbench_iverilog(work_dir)
            stdout = run_simulation_iverilog(compiled, prog_hex_path, data_hex_path, timeout=timeout)
        else:
            compiled = compile_testbench_verilator(work_dir)
            stdout = run_simulation_verilator(compiled, prog_hex_path, data_hex_path, timeout=timeout)

        # Parse
        return parse_verilog_output(stdout)


__all__ = ["run_verilog", "program_to_hex", "OPCODES"]
