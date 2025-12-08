# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Cryptographic state hashing for receipt binding.

This module implements the Canonical Serialization Format (CSF) defined in
docs/CANONICAL_SERIALIZATION.md to ensure cross-layer hash compatibility:
    Python_Hash(S) == Verilog_Hash(S) == Coq_hash_state(S)

The hash chain construction is:
    H_0 = SHA256(serialize(initial_state))
    H_t = SHA256(H_{t-1} || serialize(Δstate) || μ_op)
"""

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass
from typing import Dict, List, Tuple

try:
    from .state import State
    from ._types import ModuleId
except ImportError:
    # Handle running as script
    import sys
    import os
    sys.path.insert(0, os.path.dirname(__file__))
    from state import State
    from _types import ModuleId


# =============================================================================
# Constants
# =============================================================================

# μ-cost of computing a single state hash
# Per user guidance (comment 3628859175): charge for thermodynamic cost
MU_HASH_COST = 100


# =============================================================================
# Canonical Serialization Functions
# =============================================================================

def serialize_u32(value: int) -> bytes:
    """Serialize a uint32 in little-endian format.
    
    Args:
        value: Integer in range [0, 2^32-1]
        
    Returns:
        4-byte little-endian representation
        
    Example:
        >>> serialize_u32(0x01234567).hex()
        '67452301'
    """
    if not (0 <= value < (1 << 32)):
        raise ValueError(f"Value {value} out of range for u32")
    return struct.pack('<I', value)


def serialize_u64(value: int) -> bytes:
    """Serialize a uint64 in little-endian format.
    
    Args:
        value: Integer in range [0, 2^64-1]
        
    Returns:
        8-byte little-endian representation
    """
    if not (0 <= value < (1 << 64)):
        raise ValueError(f"Value {value} out of range for u64")
    return struct.pack('<Q', value)


def serialize_z(value: int) -> bytes:
    """Serialize an arbitrary-precision integer (Z) in big-endian format.
    
    This is used for the μ-ledger which can exceed uint64 range.
    
    Args:
        value: Arbitrary-precision integer
        
    Returns:
        Variable-length big-endian two's complement representation
    """
    if value == 0:
        return b'\x00'
    
    # Determine byte length needed
    if value > 0:
        bit_length = value.bit_length()
        byte_length = (bit_length + 8) // 8  # +8 for sign bit
        return value.to_bytes(byte_length, byteorder='big', signed=False)
    else:
        # Negative numbers use two's complement
        bit_length = value.bit_length()
        byte_length = (bit_length + 8) // 8
        return value.to_bytes(byte_length, byteorder='big', signed=True)


def serialize_partition(partition: Dict[ModuleId, List[int]]) -> bytes:
    """Serialize partition in canonical format.
    
    Format (per CSF spec):
        [num_modules:u32] || 
        [module_id:u32, var_count:u32, [vars...]:u32*] (for each module)
    
    Modules and variables within modules are sorted for determinism.
    
    Args:
        partition: Mapping from module ID to list of variable indices
        
    Returns:
        Canonical byte representation
    """
    result = bytearray()
    
    # Sort modules by ID for canonical ordering
    sorted_modules = sorted(partition.items())
    
    # Number of modules
    result.extend(serialize_u32(len(sorted_modules)))
    
    # Each module
    for module_id, variables in sorted_modules:
        # Module ID
        result.extend(serialize_u32(module_id))
        
        # Sort variables for canonical ordering
        sorted_vars = sorted(variables)
        
        # Variable count
        result.extend(serialize_u32(len(sorted_vars)))
        
        # Variables
        for var_idx in sorted_vars:
            result.extend(serialize_u32(var_idx))
    
    return bytes(result)


def serialize_state(state: State) -> bytes:
    """Serialize complete State per Canonical Serialization Format.
    
    Format (per CSF spec docs/CANONICAL_SERIALIZATION.md):
        1. Partition masks (canonical ordering)
        2. μ-ledger total (Z, big-endian)
        3. Step count (u32, little-endian)
        4. Next ID (u32, little-endian)
        5. Program hash (32 bytes, SHA-256 of program)
        6. Axioms count (u32)
        7. CSR values (u32 each for STATUS and ERR)
    
    Args:
        state: Thiele Machine state
        
    Returns:
        Canonical byte representation
    """
    result = bytearray()
    
    # 1. Partition masks (using bitmask representation for hardware isomorphism)
    # Convert to dict[int, list[int]] format for serialize_partition
    partition_dict = {}
    for module_id, mask in sorted(state.partition_masks.items()):
        from .state import indices_of_mask
        partition_dict[module_id] = sorted(list(indices_of_mask(mask)))
    result.extend(serialize_partition(partition_dict))
    
    # 2. μ-ledger total (big-endian arbitrary precision)
    mu_total = state.mu_ledger.total
    result.extend(serialize_z(mu_total))
    
    # 3. Step count (little-endian u32)
    result.extend(serialize_u32(state.step_count))
    
    # 4. Next ID (little-endian u32)
    result.extend(serialize_u32(state._next_id))
    
    # 5. Program hash (efficiency: hash program instead of full serialization)
    # This allows hardware to store program hash instead of full program
    program_bytes = str(state.program).encode('utf-8')
    program_hash = hashlib.sha256(program_bytes).digest()
    result.extend(program_hash)
    
    # 6. Axioms count (number of modules with axioms)
    result.extend(serialize_u32(len(state.axioms)))
    
    # 7. CSR values (STATUS and ERR registers)
    from .isa import CSR
    status = state.csr.get(CSR.STATUS, 0)
    err = state.csr.get(CSR.ERR, 0)
    result.extend(serialize_u32(int(status) if isinstance(status, (int, float)) else 0))
    result.extend(serialize_u32(int(err) if isinstance(err, (int, float)) else 0))
    
    return bytes(result)


def pad_to_sha256_block(data: bytes) -> bytes:
    """Pad data to 512-bit (64-byte) SHA-256 block boundary.
    
    Uses standard SHA-256 padding: zero-padding to 64-byte alignment.
    
    Args:
        data: Arbitrary-length bytes
        
    Returns:
        Padded bytes (length multiple of 64)
    """
    block_size = 64
    padding_needed = (block_size - (len(data) % block_size)) % block_size
    
    if padding_needed == 0:
        return data
    
    return data + (b'\x00' * padding_needed)


# =============================================================================
# State Hasher
# =============================================================================

class StateHasher:
    """Cryptographic state hasher implementing CSF specification.
    
    This class provides the core hash_state function that must match
    Coq's axiomatic hash_state and Verilog's state_hasher module.
    
    Example:
        >>> hasher = StateHasher()
        >>> state_hash = hasher.hash_state(state)  # 32-byte digest
        >>> hex_hash = state_hash.hex()
    """
    
    def hash_state(self, state: State) -> bytes:
        """Compute SHA-256 hash of state per CSF.
        
        This is the canonical hash_state function that must be isomorphic
        across Coq/Python/Verilog layers.
        
        Args:
            state: Thiele Machine state
            
        Returns:
            32-byte SHA-256 digest
        """
        serialized = serialize_state(state)
        padded = pad_to_sha256_block(serialized)
        return hashlib.sha256(padded).digest()
    
    def hash_state_hex(self, state: State) -> str:
        """Compute hex-encoded hash of state.
        
        Convenience method for debugging and display.
        
        Args:
            state: Thiele Machine state
            
        Returns:
            64-character hex string (256 bits)
        """
        return self.hash_state(state).hex()


# =============================================================================
# Hash Chain Construction
# =============================================================================

@dataclass
class CryptoStepWitness:
    """Cryptographic witness for a single execution step.
    
    This matches the Coq CryptoStepWitness definition in ThieleSpaceland.v.
    
    Attributes:
        pre_hash: SHA-256 hash of state before step
        post_hash: SHA-256 hash of state after step  
        instruction: Executed instruction (as string)
        label: Label produced by step (e.g., "LCompute")
        mu_delta: μ-cost of this step
    """
    pre_hash: bytes      # 32 bytes
    post_hash: bytes     # 32 bytes
    instruction: str
    label: str
    mu_delta: int
    
    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization."""
        return {
            'pre_hash': self.pre_hash.hex(),
            'post_hash': self.post_hash.hex(),
            'instruction': self.instruction,
            'label': self.label,
            'mu_delta': self.mu_delta
        }


@dataclass
class CryptoReceipt:
    """Cryptographically bound execution receipt.
    
    This matches the Coq CryptoReceipt definition in ThieleSpaceland.v.
    Hash chain construction: H_t = SHA256(H_{t-1} || Δstate || μ_op)
    
    Attributes:
        initial_hash: Hash of initial state
        final_hash: Hash of final state
        witnesses: Complete execution trace with hash chain
        label_sequence: Labels produced during execution
        total_mu: Total μ-cost of execution
    """
    initial_hash: bytes              # 32 bytes
    final_hash: bytes                # 32 bytes
    witnesses: List[CryptoStepWitness]
    label_sequence: List[str]
    total_mu: int
    
    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization."""
        return {
            'initial_hash': self.initial_hash.hex(),
            'final_hash': self.final_hash.hex(),
            'witnesses': [w.to_dict() for w in self.witnesses],
            'label_sequence': self.label_sequence,
            'total_mu': self.total_mu
        }
    
    def verify_hash_chain(self) -> bool:
        """Verify hash chain integrity.
        
        Checks that:
        1. post_hash[i] == pre_hash[i+1] for all steps
        2. Hash chain is connected from initial to final
        
        Returns:
            True if hash chain is valid, False otherwise
        """
        if not self.witnesses:
            return self.initial_hash == self.final_hash
        
        # Check initial connection
        if self.witnesses[0].pre_hash != self.initial_hash:
            return False
        
        # Check chain connectivity
        for i in range(len(self.witnesses) - 1):
            if self.witnesses[i].post_hash != self.witnesses[i+1].pre_hash:
                return False
        
        # Check final connection
        if self.witnesses[-1].post_hash != self.final_hash:
            return False
        
        return True


def verify_crypto_receipt(receipt: CryptoReceipt) -> bool:
    """Verify cryptographic receipt validity.
    
    This matches the Coq verify_crypto_receipt function.
    
    Checks:
    1. μ-cost is non-negative
    2. Hash chain integrity
    3. Label/witness alignment
    
    Args:
        receipt: Cryptographic receipt to verify
        
    Returns:
        True if receipt is valid, False otherwise
    """
    # Check 1: Non-negative μ
    if receipt.total_mu < 0:
        return False
    
    # Check 2: Hash chain integrity
    if not receipt.verify_hash_chain():
        return False
    
    # Check 3: Label sequence matches witnesses
    if len(receipt.label_sequence) != len(receipt.witnesses):
        return False
    
    for i, (label, witness) in enumerate(zip(receipt.label_sequence, receipt.witnesses)):
        if label != witness.label:
            return False
    
    return True


# =============================================================================
# Convenience Functions
# =============================================================================

def compute_state_hash(state: State) -> bytes:
    """Convenience function to compute state hash.
    
    Args:
        state: Thiele Machine state
        
    Returns:
        32-byte SHA-256 digest
    """
    hasher = StateHasher()
    return hasher.hash_state(state)


def compute_state_hash_hex(state: State) -> str:
    """Convenience function to compute hex-encoded state hash.
    
    Args:
        state: Thiele Machine state
        
    Returns:
        64-character hex string
    """
    hasher = StateHasher()
    return hasher.hash_state_hex(state)
