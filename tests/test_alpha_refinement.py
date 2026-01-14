# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""Refined Monte Carlo probe that requires executing CSR reads."""

from __future__ import annotations

import random
from typing import Tuple

import pytest

from thielecpu.isa import CSR, Opcode, decode


INSTRUCTION_COSTS = {
    Opcode.XOR_SWAP: 0.0,
    Opcode.XOR_ADD: 0.0,
    Opcode.EMIT: 1.0,
    Opcode.MDLACC: 0.0,
    Opcode.HALT: 0.0,
}


class TinyVM:
    """Minimal sequential VM: executes one instruction per step."""

    def __init__(self, program: list[Tuple[Opcode, int, int]]):
        self.program = program
        self.pc = 0
        self.mu = 0.0
        self.halted = False
        self.cert_value = 0  # Certificate value injected externally
        self.registers = [0] * 256  # Minimal register file

    def step(self) -> Tuple[bool, bool]:
        """Execute a single instruction.

        Returns (executed_cert_read, halted_after_step).
        """

        if self.halted or not self.program:
            return False, True

        op, a, b = self.program[self.pc % len(self.program)]
        self.pc += 1

        # µ accounting mirrors the gravity sandbox: EMIT pays one irreversible
        # bit, reversible ops are free.
        self.mu += INSTRUCTION_COSTS.get(op, 0.0)

        saw_cert = False
        if op is Opcode.MDLACC:
            if a == CSR.CERT_ADDR.value:
                # Load certificate into register b
                self.registers[b] = self.cert_value & 0xFF
                saw_cert = True
            elif b == CSR.CERT_ADDR.value:
                # Load certificate into register a
                self.registers[a] = self.cert_value & 0xFF
                saw_cert = True
        elif op is Opcode.EMIT:
            # Emit from register a - this is our output
            pass
        elif op is Opcode.HALT:
            self.halted = True

        return saw_cert, self.halted


def _decode_program(data: bytes) -> list[Tuple[Opcode, int, int]] | None:
    if len(data) % 4 != 0:
        return None
    decoded: list[Tuple[Opcode, int, int]] = []
    try:
        for idx in range(0, len(data), 4):
            decoded.append(decode(data[idx : idx + 4]))
    except ValueError:
        return None
    return decoded


def sample_certificate_density(
    n_bits: int, samples: int = 4000, step_budget: int = 50, seed: int = 20251202
) -> tuple[int, int, float]:
    """WRONG METRIC: Just measures programs that read certificate.
    
    For α-convergence, use sample_self_referential_density() instead.
    """
    rng = random.Random(seed + n_bits)
    valid = 0
    readers = 0
    byte_len = n_bits // 8

    if byte_len == 0 or byte_len % 4 != 0:
        return 0, 0, 0.0

    opcode_values = [op.value for op in Opcode]
    instr_count = byte_len // 4

    for _ in range(samples):
        payload = bytearray()
        for _ in range(instr_count):
            op_byte = rng.choice(opcode_values)
            a = rng.randrange(256)
            b = rng.randrange(256)
            payload.extend(bytes([op_byte, a, b, 0]))

        decoded = _decode_program(payload)
        if decoded is None:
            continue

        valid += 1
        vm = TinyVM(decoded)
        saw_cert = False

        for _ in range(step_budget):
            executed_cert, halted = vm.step()
            if executed_cert:
                saw_cert = True
            if halted:
                break

        if saw_cert:
            readers += 1

    ratio = readers / valid if valid else 0.0
    return valid, readers, ratio


def sample_self_referential_density(
    n_bits: int, samples: int = 4000, step_budget: int = 50, seed: int = 20251202
) -> tuple[int, int, float]:
    """CORRECT METRIC: Programs where output depends on their own hash.
    
    Self-referential = program reads certificate AND emits different output
    when certificate changes.
    """
    import hashlib
    
    rng = random.Random(seed + n_bits)
    valid = 0
    self_referential = 0
    byte_len = n_bits // 8

    if byte_len == 0 or byte_len % 4 != 0:
        return 0, 0, 0.0

    opcode_values = [op.value for op in Opcode]
    instr_count = byte_len // 4

    for _ in range(samples):
        payload = bytearray()
        for _ in range(instr_count):
            op_byte = rng.choice(opcode_values)
            a = rng.randrange(256)
            b = rng.randrange(256)
            payload.extend(bytes([op_byte, a, b, 0]))

        decoded = _decode_program(payload)
        if decoded is None:
            continue

        valid += 1
        
        # Run with two different certificate values
        cert_hash = hashlib.sha256(bytes(payload)).digest()
        cert_value = int.from_bytes(cert_hash[:8], 'little')
        
        outputs = []
        for fake_cert in [cert_value, cert_value ^ 0xFFFFFFFFFFFFFFFF]:
            vm = TinyVM(decoded)
            vm.cert_value = fake_cert
            emitted = []
            saw_cert = False
            
            for _ in range(step_budget):
                if vm.halted:
                    break
                
                # Check if about to emit
                op, a, b = vm.program[vm.pc % len(vm.program)]
                if op is Opcode.EMIT:
                    emitted.append(vm.registers[a])
                
                executed_cert, halted = vm.step()
                if executed_cert:
                    saw_cert = True
            
            if saw_cert:
                outputs.append(tuple(emitted))
        
        # Self-referential = read certificate AND outputs differ
        if len(outputs) == 2 and len(outputs[0]) > 0 and outputs[0] != outputs[1]:
            self_referential += 1

    ratio = self_referential / valid if valid else 0.0
    return valid, self_referential, ratio


@pytest.mark.parametrize("n_bits", [32, 64, 128])
def test_certificate_reader_density_is_small(n_bits: int) -> None:
    valid, readers, ratio = sample_certificate_density(n_bits)

    if valid == 0:
        pytest.skip(f"no valid programs encountered at length {n_bits} bits")

    # Certificate reading should be rare in random programs
    # Allow for zero readers at small bit sizes (probabilistic test)
    if readers == 0:
        # Zero readers is acceptable - just means no random program read certs
        # This is expected behavior for random programs
        pass
    else:
        # If we do find readers, density should be low
        assert ratio < 0.02, f"unexpected high density {ratio} for {n_bits} bits"
