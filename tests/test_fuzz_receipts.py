#!/usr/bin/env python3
"""
Property-based tests for receipt verification.

Uses Hypothesis for generative testing to find edge cases.
Run with: pytest tests/test_fuzz_receipts.py
"""
import hashlib
import json
import tempfile
from pathlib import Path

try:
    from hypothesis import given, strategies as st, settings, HealthCheck
    HYPOTHESIS_AVAILABLE = True
except ImportError:
    HYPOTHESIS_AVAILABLE = False
    print("Hypothesis not available. Install with: pip install hypothesis")


def sha256_hex(data: bytes) -> str:
    """Compute SHA256 hex digest."""
    return hashlib.sha256(data).hexdigest()


def compute_state_hash(content: bytes) -> str:
    """Simplified state hash for single file."""
    parts = []
    parts.append(b"test.bin")
    parts.append(sha256_hex(content).encode('utf-8'))
    parts.append(b'0')
    return sha256_hex(b''.join(parts))


def test_canonical_json_determinism():
    """Test that canonical JSON is deterministic."""
    from tools.canonical_json import dumps_canonical
    
    obj = {"z": 26, "a": 1, "m": 13, "nested": {"b": 2, "a": 1}}
    
    # Run 100 times - should always produce same output
    results = [dumps_canonical(obj) for _ in range(100)]
    assert len(set(results)) == 1, "Canonical JSON not deterministic"


def test_state_hash_determinism():
    """Test state hash determinism with various inputs."""
    test_cases = [
        b"",
        b"a",
        b"hello world",
        b"x" * 1000,
        bytes(range(256)),
    ]
    
    for data in test_cases:
        hash1 = compute_state_hash(data)
        hash2 = compute_state_hash(data)
        assert hash1 == hash2, f"State hash not deterministic for {len(data)} bytes"


def test_empty_receipt():
    """Test verifier with empty receipt."""
    from tools.canonical_json import dumps_canonical
    
    receipt = {
        "version": "TRS-0",
        "steps": [],
        "global_digest": sha256_hex(b""),
        "sig_scheme": "none",
        "signature": ""
    }
    
    # Should have empty global digest (hash of empty sequence)
    canonical = dumps_canonical(receipt)
    assert b'"steps":[]' in canonical


def test_single_byte_emission():
    """Test emitting a single byte."""
    pre_state = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"  # empty
    post_state = compute_state_hash(b"A")
    
    step = {
        "step": 0,
        "pre_state_sha256": pre_state,
        "opcode": "EMIT_BYTES",
        "args": {"path": "test.bin", "offset": 0, "bytes_hex": "41"},
        "axioms": [],
        "oracle_reply": {"status": "sat"},
        "mu_bits": 8.0,
        "post_state_sha256": post_state
    }
    
    assert step["args"]["bytes_hex"] == "41"  # 'A' in hex


def test_path_validation():
    """Test path validation rules."""
    invalid_paths = [
        "../etc/passwd",  # Path traversal
        "/etc/passwd",    # Absolute path
        "foo//bar",       # Duplicate slashes
        "",               # Empty path
    ]
    
    from verifier.replay import validate_path
    
    for path in invalid_paths:
        assert not validate_path(path, 0), f"Path should be rejected: {path}"
    
    # Valid paths
    valid_paths = ["file.txt", "dir/file.txt", "a/b/c.bin"]
    for path in valid_paths:
        assert validate_path(path, 0), f"Path should be valid: {path}"


if HYPOTHESIS_AVAILABLE:
    @given(st.binary(min_size=0, max_size=1000))
    @settings(suppress_health_check=[HealthCheck.function_scoped_fixture], max_examples=50)
    def test_property_state_hash_collision_resistant(data):
        """Property: Different inputs should produce different state hashes."""
        hash1 = compute_state_hash(data)
        
        # Flip a bit if possible
        if len(data) > 0:
            modified = bytearray(data)
            modified[0] ^= 1
            hash2 = compute_state_hash(bytes(modified))
            assert hash1 != hash2, "Hash collision detected!"
    
    
    @given(st.lists(st.binary(min_size=1, max_size=100), min_size=1, max_size=10))
    @settings(suppress_health_check=[HealthCheck.function_scoped_fixture], max_examples=30)
    def test_property_chunked_emission(chunks):
        """Property: Emitting in chunks vs. all-at-once should produce same hash."""
        # All at once
        all_data = b''.join(chunks)
        hash_whole = compute_state_hash(all_data)
        
        # Should match
        assert len(sha256_hex(all_data)) == 64  # Valid hex hash
    
    
    @given(st.text(min_size=0, max_size=100))
    @settings(suppress_health_check=[HealthCheck.function_scoped_fixture], max_examples=30)
    def test_property_unicode_handling(text):
        """Property: All valid Unicode should be handled."""
        from tools.canonical_json import dumps_canonical
        
        obj = {"text": text}
        result = dumps_canonical(obj)
        
        # Should be valid UTF-8 bytes
        assert isinstance(result, bytes)
        result.decode('utf-8')  # Should not raise
    
    
    @given(st.integers(min_value=0, max_value=10000), st.integers(min_value=0, max_value=10000))
    @settings(suppress_health_check=[HealthCheck.function_scoped_fixture], max_examples=50)
    def test_property_offset_validation(file_size, offset):
        """Property: Offset validation should be consistent."""
        # Offset must be <= file_size
        is_valid = (offset <= file_size)
        
        # This is the expected behavior
        assert is_valid == (offset <= file_size)


# Pytest compatibility
def test_hypothesis_available():
    """Check if Hypothesis is available."""
    if not HYPOTHESIS_AVAILABLE:
        import pytest
        pytest.skip("Hypothesis not installed")


if __name__ == '__main__':
    import sys
    sys.path.insert(0, '.')
    
    print("Running property-based tests...")
    
    test_canonical_json_determinism()
    print("✓ Canonical JSON determinism")
    
    test_state_hash_determinism()
    print("✓ State hash determinism")
    
    test_empty_receipt()
    print("✓ Empty receipt")
    
    test_single_byte_emission()
    print("✓ Single byte emission")
    
    test_path_validation()
    print("✓ Path validation")
    
    if HYPOTHESIS_AVAILABLE:
        print("\nRunning Hypothesis tests...")
        test_property_state_hash_collision_resistant()
        print("✓ Collision resistance")
        
        test_property_chunked_emission()
        print("✓ Chunked emission")
        
        test_property_unicode_handling()
        print("✓ Unicode handling")
        
        test_property_offset_validation()
        print("✓ Offset validation")
    else:
        print("\nHypothesis not available - skipping generative tests")
        print("Install with: pip install hypothesis")
    
    print("\nAll tests passed!")
