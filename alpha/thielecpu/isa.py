# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Instruction set architecture definitions."""

from enum import Enum, unique


@unique
class CSR(Enum):
    """Control and status register identifiers."""

    CERT_ADDR = 0x00
    STATUS = 0x01
    ERR = 0x02


@unique
class Opcode(Enum):
    """Enumeration of Thiele CPU opcodes.

    The encoding assigns a unique 8-bit value to each mnemonic. The remaining
    24 bits of the 32-bit instruction word are currently used as generic
    operands and are interpreted by each instruction individually.

    IMPORTANT: These values must match the Verilog hardware implementation
    in alpha/thielecpu/hardware/thiele_cpu.v exactly for isomorphism.
    """

    PNEW = 0x00
    PSPLIT = 0x01
    PMERGE = 0x02
    LASSERT = 0x03
    LJOIN = 0x04
    MDLACC = 0x05
    EMIT = 0x0E  # Fixed: was 0x06, must match Verilog
    XFER = 0x07
    PYEXEC = 0x08  # Added: missing opcode that Verilog has
    XOR_LOAD = 0x0A  # Fixed: was 0x08, must match Verilog
    XOR_ADD = 0x0B  # Fixed: was 0x09, must match Verilog
    XOR_SWAP = 0x0C  # Fixed: was 0x0A, must match Verilog
    XOR_RANK = 0x0D  # Fixed: was 0x0B, must match Verilog


def encode(op: Opcode, a: int = 0, b: int = 0) -> bytes:
    """Encode an instruction into a 4-byte little-endian word.

    Parameters
    ----------
    op:
        The opcode to encode.
    a, b:
        Optional 8-bit operands which populate the second and third bytes of
        the instruction word. The final byte is currently reserved and must be
        zero.
    """

    return bytes([op.value & 0xFF, a & 0xFF, b & 0xFF, 0])


def decode(word: bytes) -> tuple[Opcode, int, int]:
    """Decode a 4-byte instruction word into its components.

    Raises ``ValueError`` if the word does not map to a known opcode, is not
    four bytes long, or if the reserved byte is non-zero.
    """

    if len(word) != 4:
        raise ValueError("instruction must be 4 bytes")
    opcode_byte, a, b, reserved = word
    if reserved != 0:
        raise ValueError("reserved byte must be zero")
    try:
        op = Opcode(opcode_byte)
    except ValueError as exc:  # pragma: no cover - re-raise for clarity
        raise ValueError(f"unknown opcode: {opcode_byte}") from exc
    return op, a, b


__all__ = ["Opcode", "CSR", "encode", "decode"]
