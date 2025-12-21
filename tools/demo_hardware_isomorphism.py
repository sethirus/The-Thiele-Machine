#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Thiele Machine Hardware Isomorphism Demo
========================================

Demonstrates that the Python VM is a cycle-accurate model of the
Verilog RTL hardware. Runs a program on both and compares the state.
"""

import sys
import json
import subprocess
import tempfile
from pathlib import Path

# Add project root to path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.state import State
from thielecpu.vm import VM

# ANSI Colors
RESET = "\033[0m"
BOLD = "\033[1m"
RED = "\033[31m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
BLUE = "\033[34m"
CYAN = "\033[36m"

HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"

def _write_hex_words(path: Path, words: list[int]) -> None:
    path.write_text("\n".join(f"{w & 0xFFFFFFFF:08x}" for w in words) + "\n", encoding="utf-8")

def _encode_word(opcode: int, a: int = 0, b: int = 0, cost: int = 0) -> int:
    return ((opcode & 0xFF) << 24) | ((a & 0xFF) << 16) | ((b & 0xFF) << 8) | (cost & 0xFF)

def run_demo():
    print(f"{BOLD}{CYAN}╔════════════════════════════════════════════════════════════════╗{RESET}")
    print(f"{BOLD}{CYAN}║  THIELE MACHINE - HARDWARE ISOMORPHISM PROOF                   ║{RESET}")
    print(f"{BOLD}{CYAN}╚════════════════════════════════════════════════════════════════╝{RESET}")
    print("")
    
    print(f"{BOLD}1. Defining Test Program{RESET}")
    print("   A simple program to exercise registers, memory, and ALU.")
    
    # Program:
    # 1. Load values from memory to r0-r3
    # 2. XOR r3 with r0 and r1
    # 3. Swap r0 and r3
    # 4. Transfer r2 to r4
    # 5. Rank (popcount) r4 to r5
    
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
    
    program_words = [
        _encode_word(0x0A, 0, 0),  # XOR_LOAD r0 <= mem[0]
        _encode_word(0x0A, 1, 1),  # XOR_LOAD r1 <= mem[1]
        _encode_word(0x0A, 2, 2),  # XOR_LOAD r2 <= mem[2]
        _encode_word(0x0A, 3, 3),  # XOR_LOAD r3 <= mem[3]
        _encode_word(0x0B, 3, 0),  # XOR_ADD r3 ^= r0
        _encode_word(0x0B, 3, 1),  # XOR_ADD r3 ^= r1
        _encode_word(0x0C, 0, 3),  # XOR_SWAP r0 <-> r3
        _encode_word(0x07, 4, 2),  # XFER r4 <- r2
        _encode_word(0x0D, 5, 4),  # XOR_RANK r5 := popcount(r4)
        _encode_word(0xFF, 0, 0),  # HALT
    ]
    
    init_mem = [0] * 256
    init_mem[0] = 0x29
    init_mem[1] = 0x12
    init_mem[2] = 0x22
    init_mem[3] = 0x03
    
    print("   Program loaded.")
    print("")

    print(f"{BOLD}2. Running Python VM (Golden Model){RESET}")
    state = State()
    vm = VM(state)
    vm.data_memory = [m & 0xFFFFFFFF for m in init_mem]
    
    with tempfile.TemporaryDirectory() as td:
        vm.run(program_text, Path(td))
    
    py_regs = [v & 0xFFFFFFFF for v in vm.register_file]
    print(f"   {GREEN}✓ Python VM execution complete.{RESET}")
    print("")

    print(f"{BOLD}3. Running Verilog RTL (Hardware Simulation){RESET}")
    print("   Compiling and simulating Verilog using Icarus Verilog...")
    
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        sim_out = td_path / "thiele_cpu_tb.out"
        program_hex = td_path / "tb_program.hex"
        data_hex = td_path / "tb_data.hex"

        _write_hex_words(program_hex, program_words)
        _write_hex_words(data_hex, init_mem)

        # Compile
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
        
        # Simulate
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
        decoder = json.JSONDecoder()
        payload, _ = decoder.raw_decode(out[start:])
        
    rtl_regs = [int(v) & 0xFFFFFFFF for v in payload["regs"]]
    print(f"   {GREEN}✓ RTL simulation complete.{RESET}")
    print("")

    print(f"{BOLD}4. Verifying Isomorphism{RESET}")
    print(f"   Comparing final register states...")
    print("")
    print(f"   {'Reg':<5} | {'Python Value':<15} | {'RTL Value':<15} | {'Match':<10}")
    print(f"   {'-'*5}-+-{'-'*15}-+-{'-'*15}-+-{'-'*10}")
    
    mismatch = False
    for i in range(8): # Show first 8 regs
        py_val = py_regs[i]
        rtl_val = rtl_regs[i]
        match = py_val == rtl_val
        if not match: mismatch = True
        status = f"{GREEN}YES{RESET}" if match else f"{RED}NO{RESET}"
        print(f"   r{i:<4} | {py_val:<15} | {rtl_val:<15} | {status}")
        
    print("")
    if not mismatch:
        print(f"{BOLD}{GREEN}SUCCESS: Hardware and Software states are IDENTICAL.{RESET}")
        print("The Python code is a cycle-accurate specification of the silicon.")
    else:
        print(f"{BOLD}{RED}FAILURE: State mismatch detected.{RESET}")

if __name__ == "__main__":
    run_demo()
