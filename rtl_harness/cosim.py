from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

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
    "CHECKPOINT": 0x19,
    "READ_PORT": 0x1A,
    "WRITE_PORT": 0x1B,
    "HEAP_LOAD": 0x1C,
    "HEAP_STORE": 0x1D,
    "CERTIFY": 0x1E,
    "AND": 0x1F,
    "OR": 0x20,
    "SHL": 0x21,
    "SHR": 0x22,
    "MUL": 0x23,
    "LUI": 0x24,
    "HALT": 0xFF,
}

REPO_ROOT = Path(__file__).resolve().parent.parent
RTL_DIR = REPO_ROOT / "thielecpu" / "hardware" / "rtl"
BSC_VERILOG_DIR = Path("/usr/local/lib/Verilog")
TB_DIR = Path(__file__).resolve().parent / "testbench"
CACHED_VVP = REPO_ROOT / "build" / "thiele_kami_test.vvp"
CACHED_VERILATOR_BIN = REPO_ROOT / "build" / "verilator" / "Vthiele_cpu_kami_tb"

_vvp_ready = False
_verilator_ready = False


_command_cache: Dict[str, bool] = {}

def _command_available(command: str) -> bool:
    if command not in _command_cache:
        try:
            subprocess.run([command, "--version"], capture_output=True, timeout=5)
            _command_cache[command] = True
        except (FileNotFoundError, subprocess.TimeoutExpired):
            _command_cache[command] = False
    return _command_cache[command]


def _encode_instruction(opcode_name: str, operand_a: int = 0, operand_b: int = 0, cost: int = 0) -> int:
    opcode = OPCODES.get(opcode_name.upper())
    if opcode is None:
        raise ValueError(f"Unknown opcode: {opcode_name}")
    return ((opcode & 0xFF) << 24) | ((operand_a & 0xFF) << 16) | ((operand_b & 0xFF) << 8) | (cost & 0xFF)


def program_to_hex(program, **_kwargs) -> Tuple[List[str], List[str], Dict[str, int]]:
    if isinstance(program, (list, tuple)):
        program = "\n".join(str(line) for line in program)

    instructions: List[int] = []
    data_memory: Dict[int, int] = {}
    init_state: Dict[str, int] = {}

    for raw_line in str(program).strip().splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or line.startswith(";") or line.startswith("FUEL"):
            continue

        parts = line.split(maxsplit=1)
        op = parts[0].upper()
        arg = parts[1] if len(parts) > 1 else ""

        if op == "INIT_MEM":
            mem_parts = arg.split()
            if len(mem_parts) >= 2:
                data_memory[int(mem_parts[0], 0)] = int(mem_parts[1], 0)
            continue
        if op == "INIT_MU":
            init_state["INIT_MU"] = int(arg.split()[0], 0) & 0xFFFFFFFF
            continue
        if op == "INIT_ACTIVE_MODULE":
            init_state["INIT_ACTIVE_MODULE"] = int(arg.split()[0], 0) & 0x3F
            continue
        if op == "INIT_PT":
            init_parts = arg.split()
            if len(init_parts) >= 2:
                init_state["INIT_PT_IDX"] = int(init_parts[0], 0) & 0xF
                init_state["INIT_PT_VAL"] = int(init_parts[1], 0) & 0xFFFFFFFF
            continue
        if op == "INIT_TENSOR":
            init_parts = arg.split()
            if len(init_parts) >= 2:
                init_state["INIT_TENSOR_IDX"] = int(init_parts[0], 0) & 0xF
                init_state["INIT_TENSOR_VAL"] = int(init_parts[1], 0) & 0xFFFFFFFF
            continue
        if op == "INIT_LOGIC_STALL":
            init_state["INIT_LOGIC_STALL"] = int(arg.split()[0], 0) & 0x1
            continue
        if op == "INIT_LOGIC_REQ_VALID":
            init_state["INIT_LOGIC_REQ_VALID"] = int(arg.split()[0], 0) & 0x1
            continue
        if op == "INIT_LOGIC_ACC":
            init_state["INIT_LOGIC_ACC"] = int(arg.split()[0], 0) & 0xFFFFFFFF
            continue
        if op == "INIT_REG":
            continue

        if op == "PNEW":
            match = re.match(r"\{([^}]*)\}\s+(\d+)", arg)
            if match:
                region = [int(token.strip(), 0) for token in match.group(1).split(",") if token.strip()]
                cost = int(match.group(2), 0)
                instructions.append(_encode_instruction("PNEW", region[0] if region else 0, len(region), cost))
            else:
                pnew_parts = arg.split()
                instructions.append(_encode_instruction("PNEW", int(pnew_parts[0], 0), int(pnew_parts[1], 0), int(pnew_parts[2], 0)))
            continue

        if op == "PSPLIT":
            match = re.match(r"(\d+)\s+\{[^}]*\}\s+\{[^}]*\}\s+(\d+)", arg)
            if match:
                instructions.append(_encode_instruction("PSPLIT", int(match.group(1), 0), 0, int(match.group(2), 0)))
            else:
                psplit_parts = arg.split()
                cost = int(psplit_parts[3], 0) if len(psplit_parts) > 3 else 0
                instructions.append(_encode_instruction("PSPLIT", int(psplit_parts[0], 0), 0, cost))
            continue

        if op == "PMERGE":
            merge_parts = arg.split()
            instructions.append(_encode_instruction("PMERGE", int(merge_parts[0], 0), int(merge_parts[1], 0), int(merge_parts[2], 0)))
            continue

        # JUMP/CALL: target is {op_a, op_b} = 16-bit address; cost in cost field.
        # Syntax: "JUMP target cost" or "CALL target cost"
        if op in {"JUMP", "CALL"}:
            jc_parts = arg.split()
            target = int(jc_parts[0], 0) if len(jc_parts) > 0 else 0
            cost = int(jc_parts[1], 0) if len(jc_parts) > 1 else 0
            op_a = (target >> 8) & 0xFF
            op_b = target & 0xFF
            instructions.append(_encode_instruction(op, op_a, op_b, cost))
            continue

        # JNEZ: op_a = register to test, op_b = target address (8-bit), cost in cost field.
        # Syntax: "JNEZ reg target cost"
        if op == "JNEZ":
            jnez_parts = arg.split()
            reg = int(jnez_parts[0], 0) if len(jnez_parts) > 0 else 0
            target = int(jnez_parts[1], 0) if len(jnez_parts) > 1 else 0
            cost = int(jnez_parts[2], 0) if len(jnez_parts) > 2 else 0
            instructions.append(_encode_instruction(op, reg, target, cost))
            continue

        # RET: no address operands, cost in cost field. Syntax: "RET cost"
        if op == "RET":
            ret_parts = arg.split()
            cost = int(ret_parts[0], 0) if len(ret_parts) > 0 else 0
            instructions.append(_encode_instruction(op, 0, 0, cost))
            continue

        # Register-indirect LOAD/STORE: op_a=dst/rs_addr_reg, op_b=rs_addr_reg/src_reg
        # LOAD dst rs_addr cost  — loads mem[regs[rs_addr]] into regs[dst]
        # STORE rs_addr src cost — stores regs[src] into mem[regs[rs_addr]]
        # HEAP_LOAD/HEAP_STORE follow the same register-indirect convention.
        if op in {"LOAD", "HEAP_LOAD"}:
            ld_parts = arg.split()
            dst = int(ld_parts[0], 0) if len(ld_parts) > 0 else 0
            rs_addr = int(ld_parts[1], 0) if len(ld_parts) > 1 else 0
            cost = int(ld_parts[2], 0) if len(ld_parts) > 2 else 0
            instructions.append(_encode_instruction(op, dst, rs_addr, cost))
            continue

        if op in {"STORE", "HEAP_STORE"}:
            st_parts = arg.split()
            rs_addr = int(st_parts[0], 0) if len(st_parts) > 0 else 0
            src = int(st_parts[1], 0) if len(st_parts) > 1 else 0
            cost = int(st_parts[2], 0) if len(st_parts) > 2 else 0
            instructions.append(_encode_instruction(op, rs_addr, src, cost))
            continue

        if op in {"MDLACC", "XOR_LOAD", "XOR_ADD", "XOR_SWAP", "XOR_RANK", "XFER", "LASSERT", "LJOIN", "PDISCOVER", "ORACLE_HALTS", "EMIT", "REVEAL", "CHECKPOINT", "READ_PORT", "WRITE_PORT", "CERTIFY"}:
            generic_parts = arg.split()
            operand_a = int(generic_parts[0], 0) if len(generic_parts) > 0 else 0
            operand_b = int(generic_parts[1], 0) if len(generic_parts) > 1 else 0
            cost = int(generic_parts[2], 0) if len(generic_parts) > 2 else 0
            instructions.append(_encode_instruction(op, operand_a, operand_b, cost))
            continue

        if op == "LOAD_IMM":
            imm_parts = arg.split()
            instructions.append(_encode_instruction("LOAD_IMM", int(imm_parts[0], 0), int(imm_parts[1], 0), int(imm_parts[2], 0) if len(imm_parts) > 2 else 0))
            continue

        if op == "CHSH_TRIAL":
            chsh_parts = arg.split()
            if len(chsh_parts) >= 4:
                x = int(chsh_parts[0], 0)
                y = int(chsh_parts[1], 0)
                a = int(chsh_parts[2], 0)
                b = int(chsh_parts[3], 0)
                cost = int(chsh_parts[4], 0) if len(chsh_parts) > 4 else 0
                operand_a = ((x & 0x1) << 1) | (y & 0x1)
                operand_b = ((a & 0x1) << 1) | (b & 0x1)
                instructions.append(_encode_instruction("CHSH_TRIAL", operand_a, operand_b, cost))
            else:
                legacy = [int(token, 0) for token in chsh_parts]
                operand_a = legacy[0] if len(legacy) > 0 else 0
                operand_b = legacy[1] if len(legacy) > 1 else 0
                cost = legacy[2] if len(legacy) > 2 else 0
                instructions.append(_encode_instruction("CHSH_TRIAL", operand_a, operand_b, cost))
            continue

        if op in {"ADD", "SUB", "AND", "OR", "SHL", "SHR", "MUL"}:
            alu_parts = arg.split()
            dst = int(alu_parts[0], 0) if len(alu_parts) > 0 else 0
            rs1 = int(alu_parts[1], 0) if len(alu_parts) > 1 else 0
            rs2 = int(alu_parts[2], 0) if len(alu_parts) > 2 else 0
            cost = int(alu_parts[3], 0) if len(alu_parts) > 3 else 0
            packed = ((rs1 & 0xF) << 4) | (rs2 & 0xF)
            instructions.append(_encode_instruction(op, dst, packed, cost))
            continue

        # LUI: load upper immediate — LUI dst imm cost
        if op == "LUI":
            lui_parts = arg.split()
            dst = int(lui_parts[0], 0) if len(lui_parts) > 0 else 0
            imm = int(lui_parts[1], 0) if len(lui_parts) > 1 else 0
            cost = int(lui_parts[2], 0) if len(lui_parts) > 2 else 0
            instructions.append(_encode_instruction(op, dst, imm, cost))
            continue

        if op == "HALT":
            halt_parts = arg.split()
            instructions.append(_encode_instruction("HALT", 0, 0, int(halt_parts[0], 0) if halt_parts else 0))
            continue

        generic = arg.split()
        instructions.append(_encode_instruction(op, int(generic[0], 0) if len(generic) > 0 else 0, int(generic[1], 0) if len(generic) > 1 else 0, int(generic[2], 0) if len(generic) > 2 else 0))

    instruction_hex = [f"{word:08X}" for word in instructions]
    while len(instruction_hex) < 256:
        instruction_hex.append("00000000")

    data_hex = [f"{data_memory.get(index, 0):08X}" for index in range(256)]
    return instruction_hex, data_hex, init_state


def _ensure_vvp_current() -> Path:
    global _vvp_ready
    if _vvp_ready and CACHED_VVP.exists():
        return CACHED_VVP

    rtl = RTL_DIR / "thiele_cpu_kami.v"
    tb = TB_DIR / "thiele_cpu_kami_tb.v"
    for path in (rtl, tb):
        if not path.exists():
            raise FileNotFoundError(f"RTL source missing: {path}")

    needs_compile = (
        not CACHED_VVP.exists()
        or rtl.stat().st_mtime > CACHED_VVP.stat().st_mtime
        or tb.stat().st_mtime > CACHED_VVP.stat().st_mtime
    )
    if needs_compile:
        CACHED_VVP.parent.mkdir(parents=True, exist_ok=True)
        bsc_regfile = BSC_VERILOG_DIR / "RegFile.v"
        extra_srcs = [str(bsc_regfile)] if bsc_regfile.exists() else []
        cmd = ["iverilog", "-g2012", "-o", str(CACHED_VVP), "-I", str(RTL_DIR), "-I", str(BSC_VERILOG_DIR), str(rtl), str(tb)] + extra_srcs
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        if result.returncode != 0:
            raise RuntimeError(f"iverilog compilation failed:\n{result.stderr}")

    _vvp_ready = True
    return CACHED_VVP


def _ensure_verilator_current() -> Path:
    global _verilator_ready
    if _verilator_ready and CACHED_VERILATOR_BIN.exists():
        return CACHED_VERILATOR_BIN

    rtl = RTL_DIR / "thiele_cpu_kami.v"
    tb = TB_DIR / "thiele_cpu_kami_tb.v"
    sim_main = TB_DIR / "sim_main.cpp"
    bsc_regfile = BSC_VERILOG_DIR / "RegFile.v"
    for path in (rtl, tb, sim_main):
        if not path.exists():
            raise FileNotFoundError(f"RTL source missing: {path}")

    needs_compile = (
        not CACHED_VERILATOR_BIN.exists()
        or rtl.stat().st_mtime > CACHED_VERILATOR_BIN.stat().st_mtime
        or tb.stat().st_mtime > CACHED_VERILATOR_BIN.stat().st_mtime
        or sim_main.stat().st_mtime > CACHED_VERILATOR_BIN.stat().st_mtime
    )
    if needs_compile:
        out_dir = CACHED_VERILATOR_BIN.parent
        out_dir.mkdir(parents=True, exist_ok=True)
        extra_srcs = [str(bsc_regfile)] if bsc_regfile.exists() else []
        cmd = [
            "verilator", "--cc", "--timing", "--trace", "-Wno-fatal", "--build",
            f"-I{RTL_DIR}", f"-I{BSC_VERILOG_DIR}",
            "--top-module", "thiele_cpu_kami_tb",
            "--Mdir", str(out_dir),
            "--exe", str(sim_main),
            str(rtl), str(tb),
        ] + extra_srcs
        env = dict(os.environ)
        env.setdefault("THIELE_LOGIC_BRIDGE_SCRIPT", str(REPO_ROOT / "rtl_harness" / "logic_z3_bridge.py"))
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=300, env=env)
        if result.returncode != 0:
            raise RuntimeError(f"verilator compilation failed:\n{result.stderr}")
        if not CACHED_VERILATOR_BIN.exists():
            raise RuntimeError("verilator did not produce expected binary")

    _verilator_ready = True
    return CACHED_VERILATOR_BIN


def compile_testbench_iverilog(work_dir: Path) -> Path:
    rtl = RTL_DIR / "thiele_cpu_kami.v"
    tb = TB_DIR / "thiele_cpu_kami_tb.v"
    bsc_regfile = BSC_VERILOG_DIR / "RegFile.v"
    output = work_dir / "thiele_cpu_tb.vvp"
    extra_srcs = [str(bsc_regfile)] if bsc_regfile.exists() else []
    cmd = ["iverilog", "-g2012", "-o", str(output), "-I", str(RTL_DIR), "-I", str(BSC_VERILOG_DIR), str(rtl), str(tb)] + extra_srcs
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    if result.returncode != 0:
        raise RuntimeError(f"iverilog compilation failed:\n{result.stderr}")
    return output


def run_simulation_iverilog(vvp_binary: Path, program_hex: Path, data_hex: Optional[Path] = None, timeout: int = 30, n_instrs: Optional[int] = None, logic_z3_bridge: bool = False, init_state: Optional[Dict[str, int]] = None, trace_file: Optional[Path] = None, force_logic_error: bool = False) -> str:
    cmd = ["vvp", str(vvp_binary)]
    plusargs = [f"+PROGRAM={program_hex}"]
    if data_hex is not None:
        plusargs.append(f"+DATA={data_hex}")
    if n_instrs is not None:
        plusargs.append(f"+N_INSTRS={n_instrs}")
    if logic_z3_bridge:
        plusargs.append("+LOGIC_Z3_BRIDGE=1")
    if init_state:
        for key, value in init_state.items():
            plusargs.append(f"+{key}={int(value)}")
    if trace_file is not None:
        plusargs.append(f"+TRACE_FILE={trace_file}")
    if force_logic_error:
        plusargs.append("+LOGIC_FORCE_ERROR=1")
    result = subprocess.run(cmd + plusargs, capture_output=True, text=True, timeout=timeout)
    return result.stdout


def run_simulation_verilator(binary: Path, program_hex: Path, data_hex: Optional[Path] = None, timeout: int = 30, n_instrs: Optional[int] = None, logic_z3_bridge: bool = False, init_state: Optional[Dict[str, int]] = None, trace_file: Optional[Path] = None, force_logic_error: bool = False) -> str:
    cmd = [str(binary), f"+PROGRAM={program_hex}"]
    if data_hex is not None:
        cmd.append(f"+DATA={data_hex}")
    if n_instrs is not None:
        cmd.append(f"+N_INSTRS={n_instrs}")
    if logic_z3_bridge:
        cmd.append("+LOGIC_Z3_BRIDGE=1")
        cmd.append("+LOGIC_BRIDGE_EXTERNAL=1")
    if init_state:
        for key, value in init_state.items():
            cmd.append(f"+{key}={int(value)}")
    if trace_file is not None:
        cmd.append(f"+TRACE_FILE={trace_file}")
    if force_logic_error:
        cmd.append("+LOGIC_FORCE_ERROR=1")
    env = dict(os.environ)
    env.setdefault("THIELE_LOGIC_BRIDGE_SCRIPT", str(REPO_ROOT / "rtl_harness" / "logic_z3_bridge.py"))
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
    return result.stdout


def parse_verilog_output(stdout: str) -> Dict[str, Any]:
    lines = stdout.splitlines()
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
        raise ValueError(f"No JSON output found in Verilog simulation.\nFull output:\n{stdout[:2000]}")
    json_text = "\n".join(json_lines)
    json_text = re.sub(r",\s*\]", "]", json_text)
    json_text = re.sub(r",\s*\}", "}", json_text)
    result = json.loads(json_text)
    if "err" in result and not isinstance(result["err"], bool):
        result["err"] = bool(result["err"])
    return result


def run_verilog(program, timeout: int = 30, backend: Optional[str] = None, logic_z3_bridge: bool = False, trace_file: Optional[Path] = None, force_logic_error: bool = False) -> Optional[Dict[str, Any]]:
    default_backend = "verilator" if _command_available("verilator") else "iverilog"
    selected_backend = (backend or os.getenv("THIELE_RTL_SIM", default_backend)).strip().lower()
    if selected_backend not in {"iverilog", "verilator"}:
        raise ValueError(f"Unsupported RTL backend: {selected_backend}")
    if selected_backend == "iverilog" and not _command_available("iverilog"):
        return None
    if selected_backend == "verilator" and not _command_available("verilator"):
        return None

    instruction_hex, data_hex, init_state = program_to_hex(program)
    with tempfile.TemporaryDirectory(prefix="thiele_cosim_") as tmpdir:
        work_dir = Path(tmpdir)
        program_hex = work_dir / "program.hex"
        data_hex_path = work_dir / "data.hex"
        program_hex.write_text("\n".join(instruction_hex) + "\n", encoding="utf-8")
        data_hex_path.write_text("\n".join(data_hex) + "\n", encoding="utf-8")

        last_nonzero = 0
        for index, text in enumerate(instruction_hex):
            if text != "00000000":
                last_nonzero = index
        n_instrs_to_load = last_nonzero + 1

        if selected_backend == "iverilog":
            stdout = run_simulation_iverilog(_ensure_vvp_current(), program_hex, data_hex_path, timeout=timeout, n_instrs=n_instrs_to_load, logic_z3_bridge=logic_z3_bridge, init_state=init_state, trace_file=trace_file, force_logic_error=force_logic_error)
        else:
            stdout = run_simulation_verilator(_ensure_verilator_current(), program_hex, data_hex_path, timeout=timeout, n_instrs=n_instrs_to_load, logic_z3_bridge=logic_z3_bridge, init_state=init_state, trace_file=trace_file, force_logic_error=force_logic_error)
        return parse_verilog_output(stdout)


def run_verilog_batch(programs: List[str], timeout: int = 300) -> List[Optional[Dict[str, Any]]]:
    backend = "verilator" if _command_available("verilator") else "iverilog"
    per_timeout = max(5, timeout // max(1, len(programs)))
    return [run_verilog(program, timeout=per_timeout, backend=backend) for program in programs]


__all__ = ["OPCODES", "REPO_ROOT", "compile_testbench_iverilog", "program_to_hex", "run_verilog", "run_verilog_batch"]
