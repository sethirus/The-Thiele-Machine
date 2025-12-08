#!/usr/bin/env python3
"""Generate genesis hash for Verilog testbench validation.

This creates a simple test state and outputs its serialized form
and SHA-256 hash for Verilog verification.
"""

import sys
import hashlib
import struct

def serialize_u32(value: int) -> bytes:
    """Serialize uint32 little-endian."""
    return struct.pack('<I', value)

def serialize_u64(value: int) -> bytes:
    """Serialize uint64 little-endian."""
    return struct.pack('<Q', value)

def serialize_z(value: int) -> bytes:
    """Serialize arbitrary-precision integer."""
    if value == 0:
        return b'\x00'
    elif value > 0:
        bit_length = value.bit_length()
        byte_length = (bit_length + 7) // 8
        return b'\x01' + value.to_bytes(byte_length, byteorder='big')
    else:
        bit_length = (-value).bit_length()
        byte_length = (bit_length + 7) // 8
        return b'\xFF' + (-value).to_bytes(byte_length, byteorder='big')

def serialize_simple_state() -> bytes:
    """Serialize a simple test state.
    
    Test state:
    - num_modules = 2
    - module 0: vars []
    - module 1: vars [5, 10]
    - μ = 42
    - pc = 0
    - halted = 0
    - result = 0
    - program_hash = 0x00000000
    """
    buffer = bytearray()
    
    # 1. Partition: num_modules = 2
    buffer.extend(serialize_u32(2))
    
    # Module 0: id=0, var_count=0
    buffer.extend(serialize_u32(0))
    buffer.extend(serialize_u32(0))
    
    # Module 1: id=1, var_count=2, vars=[5, 10]
    buffer.extend(serialize_u32(1))
    buffer.extend(serialize_u32(2))
    buffer.extend(serialize_u32(5))
    buffer.extend(serialize_u32(10))
    
    # 2. μ-ledger = 42
    buffer.extend(serialize_z(42))
    
    # 3. PC = 0
    buffer.extend(serialize_u32(0))
    
    # 4. halted = 0
    buffer.extend(serialize_u32(0))
    
    # 5. result = 0
    buffer.extend(serialize_u32(0))
    
    # 6. program_hash = 0x00000000
    buffer.extend(serialize_u32(0))
    
    return bytes(buffer)

def main():
    # Generate serialized state
    serialized = serialize_simple_state()
    
    # Compute SHA-256 hash
    hash_obj = hashlib.sha256(serialized)
    hash_digest = hash_obj.digest()
    
    print("=" * 70)
    print("GENESIS HASH TEST VECTOR")
    print("=" * 70)
    print()
    
    print("Test State:")
    print("  num_modules = 2")
    print("  module 0: vars = []")
    print("  module 1: vars = [5, 10]")
    print("  μ = 42")
    print("  pc = 0")
    print("  halted = 0")
    print("  result = 0")
    print("  program_hash = 0x00000000")
    print()
    
    print(f"Serialized State ({len(serialized)} bytes):")
    print("  Hex:", serialized.hex())
    print()
    
    # Print byte-by-byte breakdown
    print("Byte-by-byte breakdown:")
    offset = 0
    
    print(f"  [{offset:2d}-{offset+3:2d}] num_modules = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"  [{offset:2d}-{offset+3:2d}] module_0_id = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"  [{offset:2d}-{offset+3:2d}] module_0_var_count = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"  [{offset:2d}-{offset+3:2d}] module_1_id = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"  [{offset:2d}-{offset+3:2d}] module_1_var_count = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"  [{offset:2d}-{offset+3:2d}] module_1_var[0] = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"  [{offset:2d}-{offset+3:2d}] module_1_var[1] = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    mu_bytes = 2  # 0x01 0x2A
    print(f"  [{offset:2d}-{offset+mu_bytes-1:2d}] μ = 42 (0x01, 0x2A)")
    offset += mu_bytes
    
    print(f"  [{offset:2d}-{offset+3:2d}] pc = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"  [{offset:2d}-{offset+3:2d}] halted = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"  [{offset:2d}-{offset+3:2d}] result = {int.from_bytes(serialized[offset:offset+4], 'little')}")
    offset += 4
    
    print(f"  [{offset:2d}-{offset+3:2d}] program_hash = 0x{int.from_bytes(serialized[offset:offset+4], 'little'):08X}")
    offset += 4
    
    print()
    print(f"SHA-256 Hash ({len(hash_digest)} bytes):")
    print("  Hex:", hash_digest.hex())
    print()
    
    # Print hash in 32-bit chunks (big-endian for readability)
    print("  As 8x u32 (for Verilog):")
    for i in range(0, 32, 4):
        chunk = int.from_bytes(hash_digest[i:i+4], 'big')
        print(f"    hash[{i//4}] = 32'h{chunk:08X}")
    print()
    
    print("=" * 70)
    print("Copy the SHA-256 hash above into test_serializer.v")
    print("=" * 70)
    
    return 0

if __name__ == '__main__':
    sys.exit(main())
