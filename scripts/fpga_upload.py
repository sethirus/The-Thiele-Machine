#!/usr/bin/env python3
"""fpga_upload.py — Upload a program to the Thiele CPU FPGA and read debug output.

Usage:
    python3 scripts/fpga_upload.py --port /dev/ttyUSB0 program.asm
    python3 scripts/fpga_upload.py --port /dev/ttyUSB0 program.bin --binary

The assembler format is the same text format used by the cosim:
    LOAD_IMM 1 42 1
    ADD 3 1 2 1
    HALT 0

Binary format is raw 32-bit little-endian instructions.

Protocol:
    1. Send 2-byte LE instruction count
    2. Send N × 4 bytes (each instruction, LE)
    3. Wait for 15-byte debug dump packet
    4. Print results
"""
from __future__ import annotations

import argparse
import struct
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))


def assemble_program(lines: list[str]) -> list[int]:
    """Convert text assembly lines to 32-bit instruction words."""
    from rtl_harness.cosim import OPCODES
    instructions = []
    for line in lines:
        line = line.strip()
        if not line or line.startswith("#") or line.startswith("//"):
            continue
        # Skip INIT directives (handled differently on FPGA)
        if line.startswith("INIT_"):
            continue
        parts = line.split()
        mnemonic = parts[0]
        if mnemonic not in OPCODES:
            raise ValueError(f"Unknown opcode: {mnemonic}")
        opcode = OPCODES[mnemonic]
        args = [int(x, 0) for x in parts[1:]]
        # Pack: [31:24] opcode | [23:16] op_a | [15:8] op_b | [7:0] cost_or_arg
        op_a = args[0] if len(args) > 0 else 0
        op_b = args[1] if len(args) > 1 else 0
        op_c = args[2] if len(args) > 2 else 0
        word = ((opcode & 0xFF) << 24) | ((op_a & 0xFF) << 16) | ((op_b & 0xFF) << 8) | (op_c & 0xFF)
        instructions.append(word)
    return instructions


def upload_program(port: str, instructions: list[int], baud: int = 115200) -> dict:
    """Send program to FPGA and wait for debug dump."""
    try:
        import serial
    except ImportError:
        print("ERROR: pyserial not installed. Run: pip install pyserial", file=sys.stderr)
        sys.exit(1)

    n = len(instructions)
    print(f"Uploading {n} instructions to {port} at {baud} baud...")

    with serial.Serial(port, baud, timeout=10) as ser:
        # Send instruction count (2 bytes, LE)
        ser.write(struct.pack("<H", n))

        # Send instructions (4 bytes each, LE)
        for word in instructions:
            ser.write(struct.pack("<I", word))

        ser.flush()
        print(f"Upload complete. Waiting for CPU to halt...")

        # Wait for 15-byte debug dump
        raw = ser.read(15)
        if len(raw) < 15:
            print(f"WARNING: Only received {len(raw)} bytes (expected 15)", file=sys.stderr)
            if len(raw) == 0:
                print("No response from FPGA. Check:", file=sys.stderr)
                print("  - Is the bitstream programmed?", file=sys.stderr)
                print("  - Is the correct port selected?", file=sys.stderr)
                print("  - Is RST_N released (button not held)?", file=sys.stderr)
            return {}

        # Parse debug dump
        if raw[0] != 0xDE:
            print(f"WARNING: Bad sync byte: 0x{raw[0]:02X} (expected 0xDE)", file=sys.stderr)
            return {}

        status = raw[1]
        pc = struct.unpack_from("<I", raw, 2)[0]
        mu = struct.unpack_from("<I", raw, 6)[0]
        error_code = struct.unpack_from("<I", raw, 10)[0]

        if raw[14] != 0xAD:
            print(f"WARNING: Bad end marker: 0x{raw[14]:02X} (expected 0xAD)", file=sys.stderr)

        result = {
            "halted": bool(status & 1),
            "err": bool(status & 2),
            "certified": bool(status & 4),
            "pc": pc,
            "mu": mu,
            "error_code": error_code,
        }

        print()
        print("=== Thiele CPU Debug Dump ===")
        print(f"  Halted:     {result['halted']}")
        print(f"  Error:      {result['err']}")
        print(f"  Certified:  {result['certified']}")
        print(f"  PC:         0x{pc:08X} ({pc})")
        print(f"  Mu:         0x{mu:08X} ({mu})")
        if result["err"]:
            print(f"  Error Code: 0x{error_code:08X}")
        print()

        return result


def main():
    parser = argparse.ArgumentParser(description="Upload program to Thiele CPU FPGA")
    parser.add_argument("program", help="Assembly (.asm) or binary (.bin) file")
    parser.add_argument("--port", required=True, help="Serial port (e.g., /dev/ttyUSB0)")
    parser.add_argument("--baud", type=int, default=115200, help="Baud rate (default: 115200)")
    parser.add_argument("--binary", action="store_true", help="Input is raw binary (not assembly)")
    args = parser.parse_args()

    program_path = Path(args.program)
    if not program_path.exists():
        print(f"ERROR: File not found: {program_path}", file=sys.stderr)
        sys.exit(1)

    if args.binary:
        raw = program_path.read_bytes()
        if len(raw) % 4 != 0:
            print(f"ERROR: Binary file size ({len(raw)}) not a multiple of 4", file=sys.stderr)
            sys.exit(1)
        instructions = [struct.unpack_from("<I", raw, i)[0] for i in range(0, len(raw), 4)]
    else:
        lines = program_path.read_text().splitlines()
        instructions = assemble_program(lines)

    if not instructions:
        print("ERROR: No instructions to upload", file=sys.stderr)
        sys.exit(1)

    result = upload_program(args.port, instructions, args.baud)
    sys.exit(0 if result.get("halted") and not result.get("err") else 1)


if __name__ == "__main__":
    main()
