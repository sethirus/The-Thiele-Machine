#!/usr/bin/env python3
"""Cross-layer cryptographic hash isomorphism tests.

This module verifies that:
    Python_Hash(S) == Verilog_Hash(S)

Per user execution plan (comment 3628859175) Step 5: Verification.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
Copyright 2025 Devon Thiele
See the LICENSE file in the repository root for full terms.
"""

import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from thielecpu.crypto import (
    StateHasher,
    serialize_u32,
    serialize_u64,
    serialize_z,
    serialize_partition,
    serialize_state,
    MU_HASH_COST,
)
from thielecpu.state import State, MuLedger
from thielecpu._types import ModuleId


def test_serialize_u32():
    """Test uint32 little-endian serialization."""
    # Example from CSF spec
    result = serialize_u32(0x01234567)
    expected = bytes([0x67, 0x45, 0x23, 0x01])
    assert result == expected, f"Expected {expected.hex()}, got {result.hex()}"
    
    # Edge cases
    assert serialize_u32(0) == bytes([0, 0, 0, 0])
    assert serialize_u32(0xFFFFFFFF) == bytes([0xFF, 0xFF, 0xFF, 0xFF])
    
    print("✓ test_serialize_u32 passed")


def test_serialize_u64():
    """Test uint64 little-endian serialization."""
    result = serialize_u64(0x0123456789ABCDEF)
    expected = bytes([0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01])
    assert result == expected, f"Expected {expected.hex()}, got {result.hex()}"
    
    # Edge cases
    assert serialize_u64(0) == bytes([0] * 8)
    assert serialize_u64(0xFFFFFFFFFFFFFFFF) == bytes([0xFF] * 8)
    
    print("✓ test_serialize_u64 passed")


def test_serialize_z():
    """Test arbitrary-precision Z serialization."""
    # Positive numbers
    assert serialize_z(0) == b'\x00'
    assert serialize_z(1000) == bytes([0x03, 0xE8])
    
    # Negative numbers (two's complement)
    assert serialize_z(-500) == bytes([0xFE, 0x0C])
    
    # Large number
    large = 2**128 - 1
    result = serialize_z(large)
    assert len(result) > 0
    # Verify round-trip
    recovered = int.from_bytes(result, byteorder='big', signed=False)
    assert recovered == large
    
    print("✓ test_serialize_z passed")


def test_serialize_partition():
    """Test canonical partition serialization."""
    # Simple partition: module 1 has variables [0, 1, 2]
    partition = {
        ModuleId(1): [2, 0, 1],  # Unsorted input
    }
    
    result = serialize_partition(partition)
    
    # Expected: [num_modules:1] [module_id:1] [var_count:3] [vars:0,1,2 sorted]
    expected = bytearray()
    expected.extend(serialize_u32(1))  # 1 module
    expected.extend(serialize_u32(1))  # module ID 1
    expected.extend(serialize_u32(3))  # 3 variables
    expected.extend(serialize_u32(0))  # var 0 (sorted)
    expected.extend(serialize_u32(1))  # var 1
    expected.extend(serialize_u32(2))  # var 2
    
    assert result == bytes(expected), f"Partition serialization mismatch"
    
    print("✓ test_serialize_partition passed")


def test_state_hash_determinism():
    """Test that same state produces same hash."""
    # Create a simple state
    state1 = State()
    state1.partition_masks = {ModuleId(1): 0b111}  # variables 0,1,2 as bitmask
    state1.mu_ledger = MuLedger(mu_discovery=100, mu_execution=50)
    state1.step_count = 5
    state1.program = ["PNEW {0}", "HALT"]
    
    hasher = StateHasher()
    hash1 = hasher.hash_state(state1)
    hash2 = hasher.hash_state(state1)
    
    assert hash1 == hash2, "Same state should produce same hash"
    assert len(hash1) == 32, "SHA-256 should produce 32-byte digest"
    
    print(f"✓ test_state_hash_determinism passed")
    print(f"  State hash: {hash1.hex()}")


def test_state_hash_sensitivity():
    """Test that different states produce different hashes."""
    hasher = StateHasher()
    
    # Base state
    state1 = State()
    state1.partition_masks = {ModuleId(1): 0b111}  # variables 0,1,2
    state1.mu_ledger = MuLedger(mu_discovery=100, mu_execution=50)
    state1.step_count = 5
    state1.program = ["PNEW {0}", "HALT"]
    
    # Modified state (different step_count)
    state2 = State()
    state2.partition_masks = {ModuleId(1): 0b111}  # variables 0,1,2
    state2.mu_ledger = MuLedger(mu_discovery=100, mu_execution=50)
    state2.step_count = 6  # Different!
    state2.program = ["PNEW {0}", "HALT"]
    
    hash1 = hasher.hash_state(state1)
    hash2 = hasher.hash_state(state2)
    
    assert hash1 != hash2, "Different states should produce different hashes"
    
    print("✓ test_state_hash_sensitivity passed")


def test_mu_hash_cost():
    """Verify MU_HASH_COST is set per user guidance."""
    assert MU_HASH_COST == 100, f"MU_HASH_COST should be 100, got {MU_HASH_COST}"
    print(f"✓ test_mu_hash_cost passed (MU_HASH_COST = {MU_HASH_COST})")


def test_cross_layer_hash_placeholder():
    """Placeholder for future Verilog cross-layer verification.
    
    This test will be completed in Phase 5 when Verilog state_serializer
    is implemented. It will:
    1. Generate a random state S
    2. Compute Python_Hash(S)
    3. Simulate Verilog state_hasher with S
    4. Verify Python_Hash(S) == Verilog_Hash(S)
    """
    print("⚠ test_cross_layer_hash_placeholder - awaiting Verilog implementation")
    print("  Will verify: Python_Hash(S) == Verilog_Hash(S)")


def main():
    """Run all crypto isomorphism tests."""
    print("=" * 70)
    print("Cryptographic Isomorphism Tests")
    print("Per user plan (comment 3628859175) Step 5: Verification")
    print("=" * 70)
    print()
    
    test_serialize_u32()
    test_serialize_u64()
    test_serialize_z()
    test_serialize_partition()
    test_state_hash_determinism()
    test_state_hash_sensitivity()
    test_mu_hash_cost()
    test_cross_layer_hash_placeholder()
    
    print()
    print("=" * 70)
    print("✓ All Python crypto tests passed!")
    print("=" * 70)
    print()
    print("Next steps:")
    print("  1. Phase 5: Implement Verilog state_serializer.v")
    print("  2. Update test_cross_layer_hash to verify Python ≡ Verilog")
    print("  3. Phase 6: Run receipt_forgery_redux.py")


if __name__ == "__main__":
    main()
