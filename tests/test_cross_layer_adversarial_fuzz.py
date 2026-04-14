"""Adversarial three-layer fuzzing across OCaml, Python, and RTL.

This compares full observable state on every prefix of random traces so drift
cannot hide behind a matching final result.
"""

from __future__ import annotations

import random
import shutil
from typing import Any, cast

import pytest

from build import thiele_vm as text_vm
from thielecpu.hardware.cosim import run_verilog_batch


def _rtl_available() -> bool:
    return shutil.which("iverilog") is not None or shutil.which("verilator") is not None


pytestmark = [
    pytest.mark.integration,
    pytest.mark.strict_rtl,
    pytest.mark.skipif(not _rtl_available(), reason="RTL backend unavailable"),
    pytest.mark.skipif(not text_vm._runner_available(), reason="OCaml extracted runner unavailable"),
]


def _normalize_vm_state(state: text_vm.VMState) -> dict[str, object]:
    return {
        "pc": int(state.pc),
        "mu": int(state.mu),
        "err": bool(state.err),
        "regs": [int(value) for value in state.regs[:32]],
        "mem": [int(value) for value in state.mem[:64]],
    }


def _normalize_rtl_state(state: dict[str, object]) -> dict[str, object]:
    regs_obj = cast(list[Any], state.get("regs", []))
    mem_obj = cast(list[Any], state.get("mem", []))
    regs = [int(value) for value in regs_obj[:32]]
    mem = [int(value) for value in mem_obj[:64]]
    return {
        "pc": int(cast(int, state.get("pc", 0))),
        "mu": int(cast(int, state.get("mu", 0))),
        "err": bool(state.get("err", False)),
        "regs": regs,
        "mem": mem,
    }


def _executable_lines(program: list[str]) -> list[str]:
    return [line for line in program if line and not line.startswith("INIT_")]


def _normalize_halt_pc(state: dict[str, object], program: list[str]) -> dict[str, object]:
    executable = _executable_lines(program)
    if not executable or executable[-1].split()[0].upper() != "HALT" or bool(state["err"]):
        return state

    normalized = dict(state)
    halt_pc = max(len(executable) - 1, 0)
    if int(normalized["pc"]) in {halt_pc, halt_pc + 1}:
        normalized["pc"] = halt_pc
    return normalized


def _random_instruction(rng: random.Random) -> str:
    opcode = rng.choice([
        "LOAD_IMM",
        "ADD",
        "SUB",
        "XFER",
        "STORE",
        "LOAD",
        "XOR_LOAD",
        "XOR_ADD",
        "XOR_SWAP",
        "XOR_RANK",
    ])
    if opcode == "LOAD_IMM":
        return f"LOAD_IMM {rng.randint(0, 7)} {rng.randint(0, 255)} {rng.randint(0, 7)}"
    if opcode == "ADD":
        return f"ADD {rng.randint(0, 7)} {rng.randint(0, 7)} {rng.randint(0, 7)} {rng.randint(0, 7)}"
    if opcode == "SUB":
        return f"SUB {rng.randint(0, 7)} {rng.randint(0, 7)} {rng.randint(0, 7)} {rng.randint(0, 7)}"
    if opcode == "XFER":
        return f"XFER {rng.randint(0, 7)} {rng.randint(0, 7)} {rng.randint(0, 7)}"
    if opcode == "STORE":
        return f"STORE {rng.randint(0, 15)} {rng.randint(0, 7)} {rng.randint(0, 7)}"
    if opcode == "LOAD":
        return f"LOAD {rng.randint(0, 7)} {rng.randint(0, 15)} {rng.randint(0, 7)}"
    if opcode == "XOR_LOAD":
        return f"XOR_LOAD {rng.randint(0, 7)} {rng.randint(0, 3)} {rng.randint(0, 7)}"
    if opcode == "XOR_ADD":
        return f"XOR_ADD {rng.randint(0, 7)} {rng.randint(0, 7)} {rng.randint(0, 7)}"
    if opcode == "XOR_SWAP":
        left = rng.randint(0, 7)
        right = rng.randint(0, 7)
        while right == left:
            right = rng.randint(0, 7)
        return f"XOR_SWAP {left} {right} {rng.randint(0, 7)}"
    return f"XOR_RANK {rng.randint(0, 7)} {rng.randint(0, 7)} {rng.randint(0, 7)}"


def _program_prefixes(seed: int) -> list[list[str]]:
    rng = random.Random(seed)
    preamble = [
        "INIT_PT 0 256",
        "INIT_ACTIVE_MODULE 0",
        "INIT_MEM 0 11",
        "INIT_MEM 1 22",
        "INIT_MEM 2 33",
        "INIT_MEM 3 44",
    ]
    body = [_random_instruction(rng) for _ in range(5)]
    prefixes: list[list[str]] = []
    for end in range(len(body) + 1):
        prefixes.append(preamble + body[:end] + ["HALT 0"])
    return prefixes


@pytest.mark.parametrize("seed", range(8))
def test_cross_layer_prefix_lockstep(seed: int) -> None:
    prefixes = _program_prefixes(seed)
    rtl_results = run_verilog_batch(["\n".join(program) for program in prefixes], timeout=300)

    for index, (program, rtl_state) in enumerate(zip(prefixes, rtl_results)):
        assert rtl_state is not None, f"RTL produced no result for seed={seed}, prefix={index}"

        ocaml_state = text_vm.run_vm(program)
        python_state = text_vm._run_extracted_py(program, fuel=200)

        normalized_ocaml = _normalize_halt_pc(_normalize_vm_state(ocaml_state), program)
        normalized_python = _normalize_halt_pc(_normalize_vm_state(python_state), program)
        normalized_rtl = _normalize_halt_pc(_normalize_rtl_state(rtl_state), program)

        assert normalized_ocaml == normalized_python, (
            f"OCaml/Python mismatch for seed={seed}, prefix={index}\n"
            f"program={program}\n"
            f"ocaml={normalized_ocaml}\npython={normalized_python}"
        )
        assert normalized_ocaml == normalized_rtl, (
            f"OCaml/RTL mismatch for seed={seed}, prefix={index}\n"
            f"program={program}\n"
            f"ocaml={normalized_ocaml}\nrtl={normalized_rtl}"
        )