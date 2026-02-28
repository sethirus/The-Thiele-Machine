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
    "LOAD_IMM": 0x08,
    "CHSH_TRIAL": 0x09,
    "XOR_LOAD": 0x0A,
    "XOR_ADD": 0x0B,
    "XOR_SWAP": 0x0C,
    "XOR_RANK": 0x0D,
    "EMIT": 0x0E,
    "REVEAL": 0x0F,
    "ORACLE_HALTS": 0x10,
    "LOAD": 0x11,
    "STORE": 0x12,
    "ADD": 0x13,
    "SUB": 0x14,
    "JUMP": 0x15,
    "JNEZ": 0x16,
    "CALL": 0x17,
    "RET": 0x18,
    "HALT": 0xFF,
}

RTL_DIR = Path(__file__).resolve().parent / "rtl"
TB_DIR = Path(__file__).resolve().parent / "testbench"

# Persistent cached binaries — live in build/ and are reused across test sessions.
# Recompiled only when thiele_cpu_kami.v or the testbench is newer.
_REPO_ROOT = Path(__file__).resolve().parent.parent.parent
_CACHED_VVP = _REPO_ROOT / "build" / "thiele_kami_test.vvp"
_CACHED_BATCH_VVP = _REPO_ROOT / "build" / "thiele_kami_batch.vvp"
# Verilator native binary (~320× faster than Icarus): cached in build/verilator/
_CACHED_VERILATOR_BIN = _REPO_ROOT / "build" / "verilator" / "Vthiele_cpu_kami_tb"

# Process-level in-memory flags: True once we've confirmed the binary is current.
_vvp_ready: bool = False
_batch_vvp_ready: bool = False
_verilator_ready: bool = False


def _ensure_vvp_current() -> Path:
    """Return path to the compiled iverilog VVP, (re)compiling only if stale."""
    global _vvp_ready
    if _vvp_ready and _CACHED_VVP.exists():
        return _CACHED_VVP

    rtl = RTL_DIR / "thiele_cpu_kami.v"
    tb  = TB_DIR  / "thiele_cpu_kami_tb.v"
    sim_main = TB_DIR / "sim_main.cpp"

    for f in (rtl, tb, sim_main):
        if not f.exists():
            raise FileNotFoundError(f"RTL source missing: {f}")

    needs_compile = (
        not _CACHED_VVP.exists()
        or rtl.stat().st_mtime > _CACHED_VVP.stat().st_mtime
        or tb.stat().st_mtime  > _CACHED_VVP.stat().st_mtime
    )

    if needs_compile:
        _CACHED_VVP.parent.mkdir(parents=True, exist_ok=True)
        cmd = [
            "iverilog", "-g2012",
            "-o", str(_CACHED_VVP),
            "-I", str(RTL_DIR),
            str(rtl), str(tb),
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        if result.returncode != 0:
            raise RuntimeError(
                f"iverilog compilation failed:\n{result.stderr}")

    _vvp_ready = True
    return _CACHED_VVP


def _ensure_batch_vvp_current() -> Path:
    """Return path to the compiled batch iverilog VVP, (re)compiling only if stale."""
    global _batch_vvp_ready
    if _batch_vvp_ready and _CACHED_BATCH_VVP.exists():
        return _CACHED_BATCH_VVP

    rtl = RTL_DIR / "thiele_cpu_kami.v"
    tb  = TB_DIR  / "thiele_cpu_kami_batch_tb.v"

    for f in (rtl, tb, sim_main):
        if not f.exists():
            raise FileNotFoundError(f"Batch RTL source missing: {f}")

    needs_compile = (
        not _CACHED_BATCH_VVP.exists()
        or rtl.stat().st_mtime > _CACHED_BATCH_VVP.stat().st_mtime
        or tb.stat().st_mtime  > _CACHED_BATCH_VVP.stat().st_mtime
    )

    if needs_compile:
        _CACHED_BATCH_VVP.parent.mkdir(parents=True, exist_ok=True)
        cmd = [
            "iverilog", "-g2012",
            "-o", str(_CACHED_BATCH_VVP),
            "-I", str(RTL_DIR),
            str(rtl), str(tb),
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        if result.returncode != 0:
            raise RuntimeError(
                f"iverilog batch compilation failed:\n{result.stderr}")

    _batch_vvp_ready = True
    return _CACHED_BATCH_VVP


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
            # PNEW {region} cost  OR  PNEW a b cost (numeric format)
            m = re.match(r"\{([^}]*)\}\s+(\d+)", arg)
            if m:
                region = [int(x.strip()) for x in m.group(1).split(",") if x.strip()]
                cost = int(m.group(2))
                # Encode: operand_a = first region element, operand_b = region size
                a = region[0] if region else 0
                b = len(region)
                instrs.append(_encode_instruction("PNEW", a, b, cost))
            else:
                # Fallback: numeric format "PNEW a b cost"
                pnew_parts = arg.split()
                a = int(pnew_parts[0]) if len(pnew_parts) > 0 else 0
                b = int(pnew_parts[1]) if len(pnew_parts) > 1 else 0
                cost = int(pnew_parts[2]) if len(pnew_parts) > 2 else 0
                instrs.append(_encode_instruction("PNEW", a, b, cost))
        elif op == "PSPLIT":
            # PSPLIT mid {left} {right} cost  OR  PSPLIT mid a b cost (numeric)
            m = re.match(r"(\d+)\s+\{[^}]*\}\s+\{[^}]*\}\s+(\d+)", arg)
            if m:
                mid = int(m.group(1))
                cost = int(m.group(2))
                instrs.append(_encode_instruction("PSPLIT", mid, 0, cost))
            else:
                # Fallback: numeric format "PSPLIT mid a b cost"
                psplit_parts = arg.split()
                mid = int(psplit_parts[0]) if len(psplit_parts) > 0 else 0
                cost = int(psplit_parts[3]) if len(psplit_parts) > 3 else 0
                instrs.append(_encode_instruction("PSPLIT", mid, 0, cost))
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
            # Preferred form: CHSH_TRIAL x y a b [cost]
            # RTL packs settings into operand_a[1:0]={x,y} and outcomes into
            # operand_b[1:0]={a,b}. Keep legacy CHSH_TRIAL a b [cost] support.
            ch_parts = arg.split()
            if len(ch_parts) >= 4:
                x = int(ch_parts[0])
                y = int(ch_parts[1])
                a = int(ch_parts[2])
                b = int(ch_parts[3])
                cost = int(ch_parts[4]) if len(ch_parts) > 4 else 0
                op_a = ((x & 0x1) << 1) | (y & 0x1)
                op_b = ((a & 0x1) << 1) | (b & 0x1)
                instrs.append(_encode_instruction("CHSH_TRIAL", op_a, op_b, cost))
            else:
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
    """Compile the Kami-extracted thiele_cpu testbench with iverilog.

    Returns the path to the compiled vvp binary.
    """
    rtl_files = [
        RTL_DIR / "thiele_cpu_kami.v",
        TB_DIR / "thiele_cpu_kami_tb.v",
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
    ] + [str(f) for f in rtl_files]

    result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    if result.returncode != 0:
        raise RuntimeError(f"iverilog compilation failed:\n{result.stderr}")
    return output


def compile_testbench_verilator(work_dir: Path) -> Path:
    """Compile the Kami-extracted thiele_cpu testbench with Verilator.

    Returns the path to the compiled executable.
    """
    rtl_files = [
        RTL_DIR / "thiele_cpu_kami.v",
        TB_DIR / "thiele_cpu_kami_tb.v",
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
        "--top-module", "thiele_cpu_kami_tb",
    ] + [str(f) for f in rtl_files]

    result = subprocess.run(cmd, cwd=work_dir, capture_output=True, text=True, timeout=120)
    if result.returncode != 0:
        raise RuntimeError(f"verilator compilation failed:\n{result.stderr}")

    binary = work_dir / "obj_dir" / "Vthiele_cpu_tb"
    if not binary.exists():
        raise RuntimeError("verilator compilation did not produce obj_dir/Vthiele_cpu_tb")
    return binary


def _ensure_verilator_current() -> Path:
    """Return path to the compiled Verilator binary, rebuilding only if stale."""
    global _verilator_ready
    if _verilator_ready and _CACHED_VERILATOR_BIN.exists():
        return _CACHED_VERILATOR_BIN

    rtl = RTL_DIR / "thiele_cpu_kami.v"
    tb  = TB_DIR  / "thiele_cpu_kami_tb.v"
    sim_main = TB_DIR / "sim_main.cpp"

    for f in (rtl, tb, sim_main):
        if not f.exists():
            raise FileNotFoundError(f"RTL source missing: {f}")

    needs_compile = (
        not _CACHED_VERILATOR_BIN.exists()
        or rtl.stat().st_mtime > _CACHED_VERILATOR_BIN.stat().st_mtime
        or tb.stat().st_mtime  > _CACHED_VERILATOR_BIN.stat().st_mtime
        or sim_main.stat().st_mtime > _CACHED_VERILATOR_BIN.stat().st_mtime
    )

    if needs_compile:
        out_dir = _CACHED_VERILATOR_BIN.parent
        out_dir.mkdir(parents=True, exist_ok=True)
        cmd = [
            "verilator", "--cc", "--timing", "-Wno-fatal", "--build",
            f"-I{RTL_DIR}",
            "--top-module", "thiele_cpu_kami_tb",
            "--Mdir", str(out_dir),
            "--exe", str(sim_main),
            str(rtl), str(tb),
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=240)
        if result.returncode != 0:
            raise RuntimeError(f"verilator compilation failed:\n{result.stderr}")
        if not _CACHED_VERILATOR_BIN.exists():
            raise RuntimeError("verilator did not produce expected binary")

    _verilator_ready = True
    return _CACHED_VERILATOR_BIN


def run_simulation_iverilog(vvp_binary: Path, program_hex: Path,
                            data_hex: Optional[Path] = None,
                            timeout: int = 30,
                            n_instrs: Optional[int] = None,
                            logic_z3_bridge: bool = False) -> str:
    """Run the compiled testbench and return stdout."""
    cmd = ["vvp", str(vvp_binary)]
    plusargs = [f"+PROGRAM={program_hex}"]
    if data_hex:
        plusargs.append(f"+DATA={data_hex}")
    if n_instrs is not None:
        plusargs.append(f"+N_INSTRS={n_instrs}")
    if logic_z3_bridge:
        plusargs.append("+LOGIC_Z3_BRIDGE=1")
    cmd.extend(plusargs)

    result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if result.returncode != 0 and "timed out" not in result.stdout.lower():
        # Some simulations finish with non-zero exit; check output
        pass
    return result.stdout


def run_simulation_verilator(binary: Path, program_hex: Path,
                             data_hex: Optional[Path] = None,
                             timeout: int = 30,
                             n_instrs: Optional[int] = None,
                             logic_z3_bridge: bool = False) -> str:
    """Run the Verilator-built executable and return stdout."""
    cmd = [str(binary), f"+PROGRAM={program_hex}"]
    if data_hex:
        cmd.append(f"+DATA={data_hex}")
    if n_instrs is not None:
        cmd.append(f"+N_INSTRS={n_instrs}")
    if logic_z3_bridge:
        cmd.append("+LOGIC_Z3_BRIDGE=1")
        cmd.append("+LOGIC_BRIDGE_EXTERNAL=1")
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
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
    logic_z3_bridge: bool = False,
) -> Optional[Dict[str, Any]]:
    """Run a program through Verilog simulation and return parsed state.

    Args:
        program: Text-format program (same as OCaml runner input).
        timeout: Simulation timeout in seconds.
        backend: `iverilog` or `verilator`. Defaults to env `THIELE_RTL_SIM`
             or `verilator` when available, else `iverilog`.

    Returns:
        Dict with keys: mu, regs, mem, modules, status, etc.
        None if selected backend is unavailable.
    """
    _default = "verilator" if _command_available("verilator") else "iverilog"
    selected_backend = (backend or os.getenv("THIELE_RTL_SIM", _default)).strip().lower()
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

        # Count actual instruction slots to load (huge speedup: only load N not 256).
        last_nonzero = 0
        for idx, h in enumerate(instr_hex):
            if h != "00000000":
                last_nonzero = idx
        n_instrs_to_load = last_nonzero + 1  # inclusive of HALT

        if selected_backend == "iverilog":
            compiled = _ensure_vvp_current()  # cached; compiles once per session
            stdout = run_simulation_iverilog(
                compiled, prog_hex_path, data_hex_path,
                timeout=timeout, n_instrs=n_instrs_to_load,
                logic_z3_bridge=logic_z3_bridge)
        else:
            compiled = _ensure_verilator_current()  # cached; recompiles only when stale
            stdout = run_simulation_verilator(
                compiled, prog_hex_path, data_hex_path,
                timeout=timeout, n_instrs=n_instrs_to_load,
                logic_z3_bridge=logic_z3_bridge)

        # Parse
        return parse_verilog_output(stdout)


def run_verilog_batch(
    programs: List[str],
    timeout: int = 300,
) -> List[Optional[Dict[str, Any]]]:
    """Run multiple programs through simulation, preferring Verilator.

    When Verilator is available (default), runs each program via the cached
    native binary (~14 ms/program).  When only Icarus is available, batches all
    programs into a single ``vvp`` invocation to avoid repeated process-startup
    overhead.

    Args:
        programs: List of text-format programs (same format as run_verilog).
        timeout:  Total wall-clock timeout for the entire batch in seconds.

    Returns:
        List of result dicts (same schema as run_verilog), one per program.
        Individual entries are None if that program produced no parseable output.
    """
    if _command_available("verilator"):
        per_timeout = max(5, timeout // max(1, len(programs)))
        return [run_verilog(p, timeout=per_timeout, backend="verilator") for p in programs]

    if not _command_available("iverilog") or not _command_available("vvp"):
        return [None] * len(programs)

    # --- Icarus fallback: batch all programs into one vvp invocation ---
    batch_vvp = _ensure_batch_vvp_current()

    with tempfile.TemporaryDirectory(prefix="thiele_batch_") as tmpdir:
        work_dir = Path(tmpdir)
        manifest_lines: List[str] = []

        for idx, program in enumerate(programs):
            instr_hex, data_hex_list = program_to_hex(program)

            # Compute actual instruction count (up to last HALT / non-zero entry)
            last_nonzero = 0
            for i, h in enumerate(instr_hex):
                if h != "00000000":
                    last_nonzero = i
            n_instrs = last_nonzero + 1

            prog_path = work_dir / f"prog_{idx:04d}.hex"
            data_path = work_dir / f"data_{idx:04d}.hex"
            prog_path.write_text("\n".join(instr_hex) + "\n")
            data_path.write_text("\n".join(data_hex_list) + "\n")
            manifest_lines.append(f"{n_instrs} {prog_path} {data_path}")

        manifest_path = work_dir / "manifest.txt"
        manifest_path.write_text("\n".join(manifest_lines) + "\n")

        result = subprocess.run(
            ["vvp", str(batch_vvp), f"+MANIFEST={manifest_path}"],
            capture_output=True, text=True, timeout=timeout,
        )
        stdout = result.stdout

    # Parse: each program emits one JSON block. Collect all of them.
    results: List[Optional[Dict[str, Any]]] = []
    lines = stdout.split("\n")
    json_lines: List[str] = []
    in_json = False
    brace_depth = 0

    for line in lines:
        stripped = line.strip()
        if stripped == "{" and not in_json:
            in_json = True
            brace_depth = 1
            json_lines = [stripped]
            continue
        if in_json:
            json_lines.append(stripped)
            brace_depth += stripped.count("{") - stripped.count("}")
            if brace_depth <= 0:
                # End of one JSON block — parse it
                json_text = "\n".join(json_lines)
                json_text = re.sub(r",\s*\]", "]", json_text)
                json_text = re.sub(r",\s*\}", "}", json_text)
                try:
                    results.append(json.loads(json_text))
                except json.JSONDecodeError:
                    results.append(None)
                in_json = False
                json_lines = []

    # Pad to len(programs) if fewer blocks were emitted
    while len(results) < len(programs):
        results.append(None)

    return results[:len(programs)]


__all__ = ["run_verilog", "run_verilog_batch", "program_to_hex", "OPCODES"]
