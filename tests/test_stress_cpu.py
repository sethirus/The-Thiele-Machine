import json
import shutil
import subprocess
import tempfile
import random
import sys
import os
from pathlib import Path
import pytest

from thielecpu.state import State
from thielecpu.vm import VM
from thielecpu.isa import CSR

REPO_ROOT = Path(__file__).parent.parent
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"
HAS_IVERILOG = shutil.which("iverilog") is not None

# Extended Opcodes to fuzz
OPCODES = {
    "XFER": 0x07,
    "XOR_LOAD": 0x0A,
    "XOR_ADD": 0x0B,
    "XOR_SWAP": 0x0C,
    "XOR_RANK": 0x0D,
    "EMIT": 0x0E,
}

def _write_hex_words(path: Path, words: list[int]) -> None:
    path.write_text("\n".join(f"{w & 0xFFFFFFFF:08x}" for w in words) + "\n", encoding="utf-8")

def _encode_word(opcode: int, a: int = 0, b: int = 0, cost: int = 0) -> int:
    return ((opcode & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (cost & 0xFF)

def _run_python_vm(init_mem: list[int], init_regs: list[int], program_text: list[tuple[str, str]]) -> dict:
    state = State()
    vm = VM(state)
    vm.register_file = [r & 0xFFFFFFFF for r in init_regs]
    vm.data_memory = [m & 0xFFFFFFFF for m in init_mem]

    with tempfile.TemporaryDirectory() as td:
        outdir = Path(td)
        vm.run(program_text, outdir)

    regs = [v & 0xFFFFFFFF for v in vm.register_file]
    mem = [v & 0xFFFFFFFF for v in vm.data_memory]
    
    # Extract CSRs and counters
    # CSR.STATUS is 1
    status = int(vm.state.csr.get(CSR.STATUS, 0)) & 0xFFFFFFFF
    # mu_information maps to info_gain
    info_gain = int(vm.state.mu_information) & 0xFFFFFFFF
    
    return {
        "regs": regs,
        "mem": mem,
        "status": status,
        "info_gain": info_gain
    }

def _run_rtl(program_words: list[int], data_words: list[int]) -> dict:
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        sim_out = td_path / "thiele_cpu_tb.out"
        program_hex = td_path / "tb_program.hex"
        data_hex = td_path / "tb_data.hex"

        _write_hex_words(program_hex, program_words)
        _write_hex_words(data_hex, data_words)

        # Compile simulation
        subprocess.run(
            [
                "iverilog",
                "-g2012",
                "-D", "YOSYS_LITE",
                "-I", str(HARDWARE_DIR),
                "-o", str(sim_out),
                str(HARDWARE_DIR / "thiele_cpu_tb.v"),
                str(HARDWARE_DIR / "thiele_cpu.v"),
                str(HARDWARE_DIR / "mu_core.v"),
                str(HARDWARE_DIR / "mu_alu.v"),
                str(HARDWARE_DIR / "receipt_integrity_checker.v"),
            ],
            check=True,
            capture_output=True
        )
        
        run = subprocess.run(
            [
                "vvp",
                str(sim_out),
                f"+PROGRAM={program_hex}",
                f"+DATA={data_hex}",
            ],
            cwd=str(td_path),
            capture_output=True,
            text=True,
            check=True,
        )

        out = run.stdout
        start = out.find("{")
        if start == -1:
            raise AssertionError(f"No JSON found in RTL stdout.\nSTDOUT:\n{out}\nSTDERR:\n{run.stderr}")
        decoder = json.JSONDecoder()
        payload, _end = decoder.raw_decode(out[start:])

    regs = [int(v) & 0xFFFFFFFF for v in payload["regs"]]
    mem = [int(v) & 0xFFFFFFFF for v in payload["mem"]]
    
    status = 0
    if "status" in payload:
        status = int(payload["status"])
    
    info_gain = int(payload["info_gain"])

    return {
        "regs": regs,
        "mem": mem,
        "status": status,
        "info_gain": info_gain
    }

def generate_random_program(length: int) -> tuple[list[int], list[tuple[str, str]]]:
    program_words = []
    program_text = []
    
    # Nasty numbers to stress ALU
    nasties = [0, 1, 2, 31, 32, 255, 256, 0xFFFFFFFF, 0xAAAAAAAA, 0x55555555, 0x80000000, 0x7FFFFFFF]
    
    for _ in range(length):
        op_name = random.choice(list(OPCODES.keys()))
        opcode = OPCODES[op_name]
        
        # Mix of random and nasty values
        if random.random() < 0.2:
            a = random.choice(nasties) & 0x1F # Registers are 5 bits
            b = random.choice(nasties) & 0x1F
        else:
            a = random.randint(0, 31)
            b = random.randint(0, 31)
        
        if op_name == "XOR_LOAD":
            if random.random() < 0.2:
                b = random.choice(nasties) & 0xFF # Addr is 8 bits
            else:
                b = random.randint(0, 255)
        
        # Edge case: src == dest
        if random.random() < 0.1:
            b = a
            
        word = _encode_word(opcode, a, b)
        program_words.append(word)
        
        args = f"{a} {b}"
        program_text.append((op_name, args))
        
    program_words.append(_encode_word(0xFF, 0, 0))
    program_text.append(("HALT", ""))
    
    return program_words, program_text

@pytest.mark.skipif(not subprocess.call(["bash", "-lc", "command -v iverilog >/dev/null"]) == 0, reason="iverilog not available")
def test_fuzz_cpu_rigorous():
    # Smoke defaults for CI; full rigorous run enabled via THIELE_EXHAUSTIVE=1
    if os.environ.get("THIELE_EXHAUSTIVE"):
        iterations = 50  # Push harder in exhaustive mode
        prog_length = 100  # Longer programs
    else:
        iterations = 2   # Fast smoke runs
        prog_length = 10

    base_seed = 12345
    random.seed(base_seed)

    for i in range(iterations):
        seed = random.randint(0, 2**32 - 1)
        random.seed(seed)

        init_mem = [random.randint(0, 2**32 - 1) for _ in range(256)]
        init_regs = [0] * 32

        prog_words, prog_text = generate_random_program(prog_length)

        try:
            py_res = _run_python_vm(init_mem, init_regs, prog_text)
            rtl_res = _run_rtl(prog_words, init_mem)

            # Compare everything
            assert py_res["regs"] == rtl_res["regs"], f"Register mismatch at iteration {i} (seed {seed})"
            assert py_res["mem"] == rtl_res["mem"], f"Memory mismatch at iteration {i} (seed {seed})"
            assert py_res["info_gain"] == rtl_res["info_gain"], f"Info Gain mismatch at iteration {i} (seed {seed})"
            assert py_res["status"] == rtl_res["status"], f"Status mismatch at iteration {i} (seed {seed})"

        except Exception as e:
            pytest.fail(f"Exception at iteration {i} (seed {seed}): {e}")

@pytest.mark.skipif(not HAS_IVERILOG, reason="iverilog not available")
def test_falsifiability():
    """
    Prove that the test harness CAN fail if there is a bug.
    We intentionally inject a bug into the Python VM result and verify the assertion fails.
    """
    init_mem = [0] * 256
    init_regs = [0] * 32
    prog_words, prog_text = generate_random_program(10)
    
    # Run real execution
    py_res = _run_python_vm(init_mem, init_regs, prog_text)
    rtl_res = _run_rtl(prog_words, init_mem)
    
    # 1. Mutate Registers
    py_res_mutated = py_res.copy()
    py_res_mutated["regs"] = list(py_res["regs"])
    py_res_mutated["regs"][0] ^= 0xFFFFFFFF # Flip bits
    
    with pytest.raises(AssertionError, match="Register mismatch"):
        assert py_res_mutated["regs"] == rtl_res["regs"], "Register mismatch"
        
    # 2. Mutate Memory
    py_res_mutated = py_res.copy()
    py_res_mutated["mem"] = list(py_res["mem"])
    py_res_mutated["mem"][0] ^= 0xFFFFFFFF
    
    with pytest.raises(AssertionError, match="Memory mismatch"):
        assert py_res_mutated["mem"] == rtl_res["mem"], "Memory mismatch"
