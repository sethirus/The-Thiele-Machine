#!/usr/bin/env python3
"""
Thiele Minimal Kernel (thiele_min.py)
A minimal bytecode interpreter with receipt verification capability.
This file is reconstructed from receipts - do not edit manually.

Target: ~300-600 LoC
"""
import hashlib
import json
import sys
from typing import Any, Dict, List, Optional


# === Bytecode Operations ===

OP_LOAD = 0x01      # Load value from memory
OP_STORE = 0x02     # Store value to memory
OP_ADD = 0x10       # Addition
OP_SUB = 0x11       # Subtraction
OP_XOR = 0x12       # Bitwise XOR
OP_CMP = 0x20       # Compare
OP_JZ = 0x30        # Jump if zero
OP_JMP = 0x31       # Unconditional jump
OP_ASSERT = 0x40    # Assert condition
OP_CHECK = 0x41     # Check formula (propositional)
OP_EMIT = 0x50      # Emit bytes to output
OP_HALT = 0xFF      # Halt execution


class ThieleVM:
    """Minimal virtual machine for Thiele bytecode."""
    
    def __init__(self):
        self.memory: Dict[int, int] = {}
        self.pc = 0  # Program counter
        self.registers: Dict[str, int] = {'a': 0, 'b': 0, 'result': 0}
        self.mu_cost = 0.0  # μ-bit accumulator
        self.output_buffer = bytearray()
        self.halted = False
        self.step_log: List[Dict[str, Any]] = []
    
    def load(self, addr: int) -> int:
        """Load value from memory address."""
        self.mu_cost += 1.0
        return self.memory.get(addr, 0)
    
    def store(self, addr: int, value: int):
        """Store value to memory address."""
        self.mu_cost += 1.0
        self.memory[addr] = value
    
    def execute_op(self, opcode: int, arg1: int = 0, arg2: int = 0) -> bool:
        """
        Execute a single operation.
        Returns True if execution should continue.
        """
        if opcode == OP_LOAD:
            self.registers['result'] = self.load(arg1)
            self.pc += 1
            
        elif opcode == OP_STORE:
            self.store(arg1, self.registers['result'])
            self.pc += 1
            
        elif opcode == OP_ADD:
            self.registers['result'] = self.registers['a'] + self.registers['b']
            self.mu_cost += 2.0
            self.pc += 1
            
        elif opcode == OP_SUB:
            self.registers['result'] = self.registers['a'] - self.registers['b']
            self.mu_cost += 2.0
            self.pc += 1
            
        elif opcode == OP_XOR:
            self.registers['result'] = self.registers['a'] ^ self.registers['b']
            self.mu_cost += 2.0
            self.pc += 1
            
        elif opcode == OP_CMP:
            self.registers['result'] = 1 if self.registers['a'] == self.registers['b'] else 0
            self.mu_cost += 2.0
            self.pc += 1
            
        elif opcode == OP_JZ:
            if self.registers['result'] == 0:
                self.pc = arg1
            else:
                self.pc += 1
            self.mu_cost += 1.0
            
        elif opcode == OP_JMP:
            self.pc = arg1
            self.mu_cost += 1.0
            
        elif opcode == OP_ASSERT:
            if not self.registers['result']:
                raise AssertionError(f"Assertion failed at PC={self.pc}")
            self.mu_cost += 1.0
            self.pc += 1
            
        elif opcode == OP_CHECK:
            # Trivial propositional checker (deterministic)
            # Just checks if result register is non-zero
            if not self.simple_check(arg1):
                raise ValueError(f"CHECK failed at PC={self.pc}")
            self.mu_cost += 5.0
            self.pc += 1
            
        elif opcode == OP_EMIT:
            self.output_buffer.append(arg1 & 0xFF)
            self.mu_cost += 1.0
            self.pc += 1
            
        elif opcode == OP_HALT:
            self.halted = True
            return False
            
        else:
            raise ValueError(f"Unknown opcode: {opcode:#x}")
        
        # Log this step
        self.step_log.append({
            'pc': self.pc - 1,
            'opcode': opcode,
            'mu_cost': self.mu_cost,
            'registers': dict(self.registers)
        })
        
        return True
    
    def simple_check(self, formula_id: int) -> bool:
        """Trivial deterministic formula checker."""
        # Just checks basic tautologies for demonstration
        if formula_id == 0:
            return True  # Trivially true
        elif formula_id == 1:
            return self.registers['result'] != 0
        else:
            return True
    
    def run(self, program: List[tuple], max_steps: int = 1000):
        """Run a program (list of (opcode, arg1, arg2) tuples)."""
        steps = 0
        while not self.halted and steps < max_steps:
            if self.pc >= len(program):
                break
            
            opcode, arg1, arg2 = program[self.pc]
            if not self.execute_op(opcode, arg1, arg2):
                break
            
            steps += 1
        
        return steps


# === Receipt Verification ===

def sha256_hex(data: bytes) -> str:
    """Compute SHA256 hex digest."""
    return hashlib.sha256(data).hexdigest()


def canonical_json(obj: Any) -> bytes:
    """Serialize to canonical JSON bytes."""
    return json.dumps(
        obj,
        ensure_ascii=False,
        sort_keys=True,
        separators=(',', ':'),
    ).encode('utf-8')


def verify_receipt_file(receipt_path: str) -> bool:
    """
    Verify a receipt file using kernel semantics.
    Returns True if valid, False otherwise.
    """
    try:
        with open(receipt_path, 'r', encoding='utf-8') as f:
            receipt = json.load(f)
        
        # Verify structure
        if 'version' not in receipt or 'steps' not in receipt:
            print(f"Invalid receipt structure", file=sys.stderr)
            return False
        
        # Compute global digest
        steps = receipt['steps']
        step_hashes = []
        for step in steps:
            canonical_bytes = canonical_json(step)
            step_hash = hashlib.sha256(canonical_bytes).digest()
            step_hashes.append(step_hash)
        
        computed_digest = hashlib.sha256(b''.join(step_hashes)).hexdigest()
        
        # Compare with receipt's global_digest
        if 'global_digest' in receipt:
            expected_digest = receipt['global_digest']
            if computed_digest != expected_digest:
                print(f"Global digest mismatch!", file=sys.stderr)
                print(f"  Expected: {expected_digest}", file=sys.stderr)
                print(f"  Computed: {computed_digest}", file=sys.stderr)
                return False
        
        print(f"Receipt verification OK")
        print(f"Global digest: {computed_digest}")
        return True
        
    except Exception as e:
        print(f"Receipt verification failed: {e}", file=sys.stderr)
        return False


# === CLI Interface ===

def main():
    """Main entry point."""
    if len(sys.argv) < 2:
        print("Thiele Minimal Kernel")
        print("Usage:")
        print("  python3 thiele_min.py --verify <receipt.json>")
        print("  python3 thiele_min.py --run <program.thiele>")
        return 0
    
    command = sys.argv[1]
    
    if command == '--verify':
        if len(sys.argv) < 3:
            print("Usage: python3 thiele_min.py --verify <receipt.json>", file=sys.stderr)
            return 1
        
        receipt_path = sys.argv[2]
        success = verify_receipt_file(receipt_path)
        return 0 if success else 1
    
    elif command == '--run':
        if len(sys.argv) < 3:
            print("Usage: python3 thiele_min.py --run <program.thiele>", file=sys.stderr)
            return 1
        
        # Simple demo program
        vm = ThieleVM()
        # Program: add 5 + 3
        vm.registers['a'] = 5
        vm.registers['b'] = 3
        program = [
            (OP_ADD, 0, 0),    # a + b -> result
            (OP_EMIT, 0, 0),   # emit result (low byte)
            (OP_HALT, 0, 0),
        ]
        
        steps = vm.run(program)
        print(f"Executed {steps} steps")
        print(f"μ-cost: {vm.mu_cost}")
        print(f"Output: {bytes(vm.output_buffer)}")
        return 0
    
    else:
        print(f"Unknown command: {command}", file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
