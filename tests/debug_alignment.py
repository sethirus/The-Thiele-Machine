#!/usr/bin/env python3
"""
Debug script to identify exact differences between Python and Verilog serialization.

This runs a simple program ([PNEW(1), HALT]) in both Python and Verilog, then
compares the raw byte output to identify where they differ.
"""

import subprocess
import tempfile
from pathlib import Path
import sys

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from thielecpu.state import State
from thielecpu.vm import VM
from thielecpu.crypto import serialize_state, compute_state_hash_hex
from thielecpu.isa import Opcode, encode
from thielecpu.assemble import Instruction

REPO_ROOT = Path(__file__).parent.parent
HARDWARE_DIR = REPO_ROOT / "thielecpu" / "hardware"

def execute_python_simple():
    """Execute simple program in Python and capture serialization."""
    # Create simple program: PNEW {1}, HALT
    instructions = [("PNEW", "{1}"), ("HALT", "")]
    
    state = State()
    vm = VM(state)
    
    with tempfile.TemporaryDirectory() as tmpdir:
        vm.run(instructions, Path(tmpdir))
        
    # Serialize state
    serialized = serialize_state(state)
    state_hash = compute_state_hash_hex(state)
    
    return {
        'serialized': serialized,
        'serialized_hex': serialized.hex(),
        'state_hash': state_hash,
        'mu_total': state.mu_ledger.total,
        'num_modules': state.num_modules,
        'partition_masks': dict(state.partition_masks),
        'next_id': state._next_id,
        'step_count': state.step_count
    }

def main():
    print("=" * 80)
    print("PYTHON ↔ VERILOG ALIGNMENT DEBUG")
    print("=" * 80)
    print()
    
    # Execute in Python
    print("1. Executing in Python VM...")
    python_result = execute_python_simple()
    
    print(f"   ✓ Execution complete")
    print(f"   - num_modules: {python_result['num_modules']}")
    print(f"   - partition_masks: {python_result['partition_masks']}")
    print(f"   - next_id: {python_result['next_id']}")
    print(f"   - μ_total: {python_result['mu_total']}")
    print(f"   - step_count: {python_result['step_count']}")
    print()
    
    # Show serialization
    print("2. Python Serialization:")
    print(f"   Length: {len(python_result['serialized'])} bytes")
    print(f"   Hex (first 64 bytes):")
    serialized_hex = python_result['serialized_hex']
    for i in range(0, min(128, len(serialized_hex)), 32):
        byte_offset = i // 2
        print(f"     [{byte_offset:3d}] {serialized_hex[i:i+32]}")
    print()
    
    # Show hash
    print("3. Python State Hash:")
    print(f"   {python_result['state_hash']}")
    print()
    
    # Breakdown of serialization format
    print("4. Serialization Breakdown (per CSF spec):")
    data = python_result['serialized']
    offset = 0
    
    # Parse partition section
    print(f"   Partition section:")
    num_modules = int.from_bytes(data[offset:offset+4], 'little')
    print(f"     num_modules (u32le): {num_modules} = {data[offset:offset+4].hex()}")
    offset += 4
    
    for i in range(num_modules):
        module_id = int.from_bytes(data[offset:offset+4], 'little')
        offset += 4
        var_count = int.from_bytes(data[offset:offset+4], 'little')
        offset += 4
        print(f"     module {module_id}: var_count={var_count}")
        vars_list = []
        for j in range(var_count):
            var_idx = int.from_bytes(data[offset:offset+4], 'little')
            offset += 4
            vars_list.append(var_idx)
        if vars_list:
            print(f"       vars: {vars_list}")
    
    print(f"   μ-ledger total:")
    mu_len = data[offset]
    offset += 1
    if mu_len > 0:
        mu_value = int.from_bytes(data[offset:offset+mu_len], 'big')
        print(f"     length: {mu_len}, value: {mu_value}")
        offset += mu_len
    
    print(f"   step_count (u32le): {int.from_bytes(data[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"   next_id (u32le): {int.from_bytes(data[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"   program_hash (32 bytes): {data[offset:offset+32].hex()[:32]}...")
    offset += 32
    
    print(f"   axioms_count (u32le): {int.from_bytes(data[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"   csr_status (u32le): {int.from_bytes(data[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"   csr_err (u32le): {int.from_bytes(data[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"   Total offset: {offset} bytes")
    print()
    
    print("=" * 80)
    print("NEXT STEPS:")
    print("=" * 80)
    print("1. Integrate crypto_receipt_controller into fuzz_harness.v")
    print("2. Run Verilog simulation and compare serialization byte-by-byte")
    print("3. Fix any endianness or padding differences")
    print("4. Verify hashes match exactly")
    print()

if __name__ == "__main__":
    main()
