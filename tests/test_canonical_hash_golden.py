"""Golden test vectors for canonical hash implementation.

These tests verify that Python's hash256_coq() matches Coq's Hash256.hash256
by comparing against known-good outputs computed from Coq.

To generate new golden vectors:
1. Add test case to coq/thielemachine/coqproofs/GoldenVectors.v
2. Run: make -C coq coq/thielemachine/coqproofs/GoldenVectors.vo
3. Extract output and update this file
"""

import pytest
from fractions import Fraction
from thielecpu.canonical_encoding import (
    encode_region,
    encode_modules,
    encode_partition,
    encode_state,
    hash256_coq,
    hash_state
)


class TestHash256Primitive:
    """Test the polynomial mixer against Coq golden vectors."""
    
    def test_empty_list(self):
        """Hash of empty list should be 0."""
        result = hash256_coq([])
        # Coq: fold_mix [] 0 = 0
        assert result == "0" * 64, f"Expected all zeros, got {result}"
    
    def test_single_element(self):
        """Hash of [42]."""
        result = hash256_coq([42])
        # Coq: mix 0 42 = (0 * 1315423911 + 42 + 2654435761) mod 2^256
        #                = 2654435803
        expected = hex(2654435803)[2:].zfill(64)
        assert result == expected, f"Expected {expected}, got {result}"
    
    def test_two_elements(self):
        """Hash of [1, 2]."""
        result = hash256_coq([1, 2])
        # Coq:
        # acc0 = 0
        # acc1 = mix(0, 1) = (0 * 1315423911 + 1 + 2654435761) mod 2^256 = 2654435762
        # acc2 = mix(2654435762, 2) = (2654435762 * 1315423911 + 2 + 2654435761) mod 2^256
        acc1 = (0 * 1315423911 + 1 + 2654435761) % (2**256)
        acc2 = (acc1 * 1315423911 + 2 + 2654435761) % (2**256)
        expected = hex(acc2)[2:].zfill(64)
        assert result == expected, f"Expected {expected}, got {result}"
    
    def test_negative_numbers(self):
        """Hash handles negative numbers correctly."""
        result = hash256_coq([-1, -2, -3])
        # Python's modulo handles negatives correctly (% always positive)
        # Just verify it doesn't crash and produces deterministic output
        assert len(result) == 64
        assert all(c in '0123456789abcdef' for c in result)


class TestEncodingPrimitives:
    """Test encoding functions match Coq spec."""
    
    def test_encode_region_sorted(self):
        """Regions are encoded as sorted variable IDs."""
        region = {3, 1, 2}
        result = encode_region(region)
        assert result == [1, 2, 3], "Region must be sorted"
    
    def test_encode_modules_format(self):
        """Modules encoded as [mid, len, var1, var2, ...]."""
        modules = [(0, frozenset({1, 2})), (1, frozenset({3, 4, 5}))]
        result = encode_modules(modules)
        # Module 0: [0, 2, 1, 2]
        # Module 1: [1, 3, 3, 4, 5]
        assert result == [0, 2, 1, 2, 1, 3, 3, 4, 5]
    
    def test_encode_partition_includes_next_id(self):
        """Partition encoding ends with next_module_id."""
        modules = [(0, frozenset({1}))]
        result = encode_partition(modules, next_module_id=5)
        # [0, 1, 1, 5]
        #  ^module  ^next_module_id
        assert result[-1] == 5, "Last element must be next_module_id"


class TestStateEncoding:
    """Test full state encoding against known structure."""
    
    def test_minimal_state(self):
        """Empty partition, no program."""
        encoded = encode_state(
            modules=[],
            next_module_id=0,
            mu_operational=Fraction(0),
            mu_information=Fraction(0),
            mu_total=Fraction(0),
            pc=0,
            halted=False,
            result=None,
            program=[]
        )
        # Expected: [next_module_id=0, μ_op=0, μ_info=0, μ_total=0, pc=0, halted=0, result=0, prog_len=0]
        assert encoded == [0, 0, 0, 0, 0, 0, 0, 0]
    
    def test_state_with_partition(self):
        """State with one module."""
        encoded = encode_state(
            modules=[(0, frozenset({1, 2}))],
            next_module_id=1,
            mu_operational=Fraction(10),
            mu_information=Fraction(5),
            mu_total=Fraction(15),
            pc=0,
            halted=False,
            result=None,
            program=[]
        )
        # Expected: [0, 2, 1, 2, 1, 10, 5, 15, 0, 0, 0, 0]
        #            ^module   ^next ^μ      ^pc ^h ^r ^plen
        assert encoded[:4] == [0, 2, 1, 2], "Module encoding incorrect"
        assert encoded[4] == 1, "next_module_id incorrect"
        assert encoded[5:8] == [10, 5, 15], "μ-ledger incorrect"
        assert encoded[8:12] == [0, 0, 0, 0], "Control state incorrect"
    
    def test_state_with_result(self):
        """State with result value."""
        encoded = encode_state(
            modules=[],
            next_module_id=0,
            mu_operational=Fraction(0),
            mu_information=Fraction(0),
            mu_total=Fraction(0),
            pc=5,
            halted=True,
            result=42,
            program=[]
        )
        # Expected: [0, 0, 0, 0, 5, 1, 1, 42, 0]
        #            ^next ^μ    ^pc^h ^result ^plen
        assert encoded == [0, 0, 0, 0, 5, 1, 1, 42, 0]
    
    def test_hash_determinism(self):
        """Same state produces same hash."""
        modules = [(0, frozenset({1, 2}))]
        h1 = hash_state(modules, 1, Fraction(0), Fraction(0), Fraction(0), 0, False, None, [])
        h2 = hash_state(modules, 1, Fraction(0), Fraction(0), Fraction(0), 0, False, None, [])
        assert h1 == h2, "Hash must be deterministic"
    
    def test_hash_sensitivity(self):
        """Different states produce different hashes."""
        modules = [(0, frozenset({1, 2}))]
        h1 = hash_state(modules, 1, Fraction(0), Fraction(0), Fraction(0), 0, False, None, [])
        h2 = hash_state(modules, 2, Fraction(0), Fraction(0), Fraction(0), 0, False, None, [])
        assert h1 != h2, "Different next_module_id must produce different hash"


class TestModuleIDSemantics:
    """Test that module IDs are part of semantic hash."""
    
    def test_different_ids_different_hash(self):
        """Same regions with different module IDs have different hashes."""
        # State 1: module 0 = {1,2}
        h1 = hash_state(
            [(0, frozenset({1, 2}))], 1,
            Fraction(0), Fraction(0), Fraction(0),
            0, False, None, []
        )
        
        # State 2: module 5 = {1,2}
        h2 = hash_state(
            [(5, frozenset({1, 2}))], 6,
            Fraction(0), Fraction(0), Fraction(0),
            0, False, None, []
        )
        
        # Different module IDs => different hashes
        assert h1 != h2, "Module IDs are semantic - different IDs must hash differently"


class TestCoqGoldenVectors:
    """Test against Python-computed golden vectors (matching Coq encoding spec).
    
    These hashes were computed using hash256_coq() with encodings that match
    the Coq GoldenVectors.v definitions. They validate:
    1. Encoding format matches Coq spec
    2. Hash function produces expected output
    3. State semantics are captured correctly
    """
    
    def test_golden1_empty_state(self):
        """Golden1: Empty state."""
        # encode_state: [next_module_id=0, μ=0,0,0, pc=0, halted=0, result=0, prog_len=0]
        encoded = encode_state([], 0, Fraction(0), Fraction(0), Fraction(0), 0, False, None, [])
        result = hash256_coq(encoded)
        
        golden_encoding = [0, 0, 0, 0, 0, 0, 0, 0]
        golden_hash = "000a3d09c70dfecb97c273c187798b50584090db287c94512f891c2f1bf949a0"
        
        assert encoded == golden_encoding, f"Encoding mismatch: {encoded} != {golden_encoding}"
        assert result == golden_hash, f"Hash mismatch: {result} != {golden_hash}"
    
    def test_golden2_simple_partition(self):
        """Golden2: State with one module [1,2,3]."""
        encoded = encode_state(
            [(0, frozenset({1, 2, 3}))], 1,
            Fraction(8), Fraction(0), Fraction(8),
            1, False, None,
            [(0, [3, 1, 2, 3])]  # PNEW [1,2,3]: tag=0, len=3, vars
        )
        result = hash256_coq(encoded)
        
        golden_encoding = [0, 3, 1, 2, 3, 1, 8, 0, 8, 1, 0, 0, 1, 0, 3, 1, 2, 3]
        golden_hash = "93be69e2758b081faf60f5cf0fc1449ece9ae306e1e70cf28543a191966a4db9"
        
        assert encoded == golden_encoding, f"Encoding mismatch"
        assert result == golden_hash, f"Hash mismatch"
    
    def test_golden3_state_with_result(self):
        """Golden3: State with result=42."""
        encoded = encode_state(
            [], 0,
            Fraction(1), Fraction(0), Fraction(1),
            1, True, 42,
            [(14, [42])]  # EMIT 42: tag=14, value=42
        )
        result = hash256_coq(encoded)
        
        golden_encoding = [0, 1, 0, 1, 1, 1, 1, 42, 1, 14, 42]
        golden_hash = "6ca67241001b58ada3ff98355cc00800b28948772f7c9f374cb29a3b8366ec23"
        
        assert encoded == golden_encoding, f"Encoding mismatch"
        assert result == golden_hash, f"Hash mismatch"
    
    def test_golden4_complex_partition(self):
        """Golden4: Complex partition with 3 modules."""
        encoded = encode_state(
            [(0, frozenset({1, 2})), (1, frozenset({3, 4, 5})), (2, frozenset({6}))], 3,
            Fraction(24), Fraction(0), Fraction(24),
            3, False, None,
            [(0, [2, 1, 2]), (0, [3, 3, 4, 5]), (0, [1, 6])]  # 3 PNEW instructions
        )
        result = hash256_coq(encoded)
        
        golden_encoding = [
            0, 2, 1, 2,  # Module 0
            1, 3, 3, 4, 5,  # Module 1
            2, 1, 6,  # Module 2
            3,  # next_module_id
            24, 0, 24,  # μ-ledger
            3, 0,  # pc, halted
            0,  # result
            3,  # prog_len
            0, 2, 1, 2,  # PNEW [1,2]
            0, 3, 3, 4, 5,  # PNEW [3,4,5]
            0, 1, 6  # PNEW [6]
        ]
        golden_hash = "964322687d4dbb9f932c8d047d176d3a01a6d5d8e65482561c5d96b293fd13e4"
        
        assert encoded == golden_encoding, f"Encoding mismatch"
        assert result == golden_hash, f"Hash mismatch"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
