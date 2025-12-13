import json
import subprocess
import tempfile
from pathlib import Path

import pytest

from thielecpu.state import State
from thielecpu.vm import VM


REPO_ROOT = Path(__file__).parent.parent
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"
BUILD_DIR = REPO_ROOT / "build"


def _write_hex_words(path: Path, words: list[int]) -> None:
    path.write_text("\n".join(f"{w & 0xFFFFFFFF:08x}" for w in words) + "\n", encoding="utf-8")


def _encode_word(opcode: int, a: int = 0, b: int = 0, cost: int = 0) -> int:
    return ((opcode & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (cost & 0xFF)


def _run_python_vm(init_mem: list[int], init_regs: list[int], program_text: list[tuple[str, str]]) -> tuple[list[int], list[int]]:
    state = State()
    vm = VM(state)
    vm.register_file = [r & 0xFFFFFFFF for r in init_regs]
    vm.data_memory = [m & 0xFFFFFFFF for m in init_mem]

    with tempfile.TemporaryDirectory() as td:
        outdir = Path(td)
        vm.run(program_text, outdir)

    regs = [v & 0xFFFFFFFF for v in vm.register_file]
    mem = [v & 0xFFFFFFFF for v in vm.data_memory]
    return regs, mem


def _run_extracted(init_mem: list[int], init_regs: list[int], trace_lines: list[str]) -> tuple[list[int], list[int]]:
    runner = BUILD_DIR / "extracted_vm_runner"
    if not runner.exists():
        raise RuntimeError("missing extracted runner; run scripts/forge_artifact.sh")

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        trace_path = td_path / "trace.txt"
        prefix = []
        for r, v in enumerate(init_regs):
            prefix.append(f"INIT_REG {r} {v & 0xFFFFFFFF}")
        for a, v in enumerate(init_mem):
            prefix.append(f"INIT_MEM {a} {v & 0xFFFFFFFF}")
        trace_path.write_text("\n".join(prefix + trace_lines) + "\n", encoding="utf-8")

        result = subprocess.run([str(runner), str(trace_path)], capture_output=True, text=True, check=True)
        payload = json.loads(result.stdout)

    regs = [int(v) & 0xFFFFFFFF for v in payload["regs"]]
    mem = [int(v) & 0xFFFFFFFF for v in payload["mem"]]
    return regs, mem


def _run_rtl(program_words: list[int], data_words: list[int]) -> tuple[list[int], list[int]]:
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        sim_out = td_path / "thiele_cpu_tb.out"
        program_hex = td_path / "tb_program.hex"
        data_hex = td_path / "tb_data.hex"

        _write_hex_words(program_hex, program_words)
        _write_hex_words(data_hex, data_words)

        subprocess.run(
            [
                "iverilog",
                "-g2012",
                "-o",
                str(sim_out),
                "thiele_cpu.v",
                "thiele_cpu_tb.v",
                "mu_alu.v",
                "mu_core.v",
            ],
            cwd=str(HARDWARE_DIR),
            capture_output=True,
            text=True,
            check=True,
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

        # The tb prints a JSON object at the end.
        out = run.stdout
        start = out.find("{")
        if start == -1:
            raise AssertionError(f"No JSON found in RTL stdout.\nSTDOUT:\n{out}\nSTDERR:\n{run.stderr}")
        decoder = json.JSONDecoder()
        payload, _end = decoder.raw_decode(out[start:])

    regs = [int(v) & 0xFFFFFFFF for v in payload["regs"]]
    mem = [int(v) & 0xFFFFFFFF for v in payload["mem"]]
    return regs, mem


@pytest.mark.skipif(not subprocess.call(["bash", "-lc", "command -v iverilog >/dev/null"]) == 0, reason="iverilog not available")
def test_rtl_python_coq_compute_isomorphism() -> None:
    # Small, deterministic compute program.
    # Semantics must match across:
    #   - Python VM (thielecpu/vm.py)
    #   - extracted Coq semantics runner (build/extracted_vm_runner)
    #   - RTL sim (thielecpu/hardware/thiele_cpu.v + thiele_cpu_tb.v)

    init_regs = [0] * 32
    init_mem = [0] * 256
    init_mem[0] = 0x29
    init_mem[1] = 0x12
    init_mem[2] = 0x22
    init_mem[3] = 0x03

    # Opcodes from generated header:
    # XFER=0x07, XOR_LOAD=0x0A, XOR_ADD=0x0B, XOR_SWAP=0x0C, XOR_RANK=0x0D, HALT=0xFF
    program_words = [
        _encode_word(0x0A, 0, 0),  # XOR_LOAD r0 <= mem[0]
        _encode_word(0x0A, 1, 1),  # XOR_LOAD r1 <= mem[1]
        _encode_word(0x0A, 2, 2),  # XOR_LOAD r2 <= mem[2]
        _encode_word(0x0A, 3, 3),  # XOR_LOAD r3 <= mem[3]
        _encode_word(0x0B, 3, 0),  # XOR_ADD r3 ^= r0
        _encode_word(0x0B, 3, 1),  # XOR_ADD r3 ^= r1
        _encode_word(0x0C, 0, 3),  # XOR_SWAP r0 <-> r3
        _encode_word(0x07, 2, 4),  # XFER r4 <- r2
        _encode_word(0x0D, 5, 4),  # XOR_RANK r5 := popcount(r4)
        _encode_word(0xFF, 0, 0),  # HALT
    ]

    # Python program uses text ISA.
    program_text = [
        ("XOR_LOAD", "0 0"),
        ("XOR_LOAD", "1 1"),
        ("XOR_LOAD", "2 2"),
        ("XOR_LOAD", "3 3"),
        ("XOR_ADD", "3 0"),
        ("XOR_ADD", "3 1"),
        ("XOR_SWAP", "0 3"),
        ("XFER", "4 2"),
        ("XOR_RANK", "5 4"),
        ("HALT", ""),
    ]

    trace_lines = [
        "XOR_LOAD 0 0 0",
        "XOR_LOAD 1 1 0",
        "XOR_LOAD 2 2 0",
        "XOR_LOAD 3 3 0",
        "XOR_ADD 3 0 0",
        "XOR_ADD 3 1 0",
        "XOR_SWAP 0 3 0",
        "XFER 4 2 0",
        "XOR_RANK 5 4 0",
    ]

    py_regs, py_mem = _run_python_vm(init_mem, init_regs, program_text)
    coq_regs, coq_mem = _run_extracted(init_mem, init_regs, trace_lines)
    rtl_regs, rtl_mem = _run_rtl(program_words, init_mem)

    assert py_regs == coq_regs == rtl_regs
    assert py_mem == coq_mem == rtl_mem
