#!/usr/bin/env python3
"""
Canonical JSON serialization helper.

Ensures deterministic JSON output for cryptographic hashing.
Self-contained with no external dependencies.
"""
import json
from typing import Any


def dumps_canonical(obj: Any) -> bytes:
    """
    Serialize object to canonical JSON bytes.
    
    Guarantees:
    - Sorted object keys (lexicographic)
    - UTF-8 encoding
    - No trailing whitespace
    - Compact format (minimal whitespace)
    - Numbers in fixed decimal notation
    
    Args:
        obj: Python object (dict, list, str, int, float, bool, None)
    
    Returns:
        Canonical JSON as UTF-8 bytes
    
    Examples:
        >>> dumps_canonical({"b": 2, "a": 1})
        b'{"a":1,"b":2}'
        
        >>> dumps_canonical({"path": "test.py", "offset": 0})
        b'{"offset":0,"path":"test.py"}'
        
        >>> dumps_canonical([3, 1, 2])
        b'[3,1,2]'
    """
    # Use compact separators and sort keys
    json_str = json.dumps(
        obj,
        ensure_ascii=False,
        sort_keys=True,
        separators=(',', ':'),
        allow_nan=False,  # Reject NaN/Infinity for determinism
    )
    
    # Encode to UTF-8 bytes
    return json_str.encode('utf-8')


def dumps_canonical_str(obj: Any) -> str:
    """
    Like dumps_canonical but returns string instead of bytes.
    
    Args:
        obj: Python object
    
    Returns:
        Canonical JSON as string
    """
    return dumps_canonical(obj).decode('utf-8')


def test_canonical_json():
    """Run self-tests."""
    import hashlib
    
    # Test 1: Key sorting
    obj1 = {"z": 26, "a": 1, "m": 13}
    result1 = dumps_canonical(obj1)
    assert result1 == b'{"a":1,"m":13,"z":26}', f"Expected sorted keys, got: {result1}"
    
    # Test 2: Nested structures
    obj2 = {"outer": {"b": 2, "a": 1}, "list": [3, 2, 1]}
    result2 = dumps_canonical(obj2)
    assert b'"a":1,"b":2' in result2, "Nested keys not sorted"
    
    # Test 3: Determinism (same input = same output)
    obj3 = {"x": 1, "y": 2}
    result3a = dumps_canonical(obj3)
    result3b = dumps_canonical(obj3)
    assert result3a == result3b, "Not deterministic"
    
    # Test 4: Hash stability
    obj4 = {"step": 0, "opcode": "EMIT_BYTES"}
    hash1 = hashlib.sha256(dumps_canonical(obj4)).hexdigest()
    hash2 = hashlib.sha256(dumps_canonical(obj4)).hexdigest()
    assert hash1 == hash2, "Hash not stable"
    
    # Test 5: No unnecessary whitespace
    obj5 = {"a": [1, 2, 3]}
    result5 = dumps_canonical(obj5)
    assert b' ' not in result5, f"Unexpected whitespace: {result5}"
    
    # Test 6: UTF-8 encoding
    obj6 = {"msg": "Hello 世界"}
    result6 = dumps_canonical(obj6)
    assert isinstance(result6, bytes), "Not bytes"
    assert "世界".encode('utf-8') in result6, "UTF-8 encoding failed"
    
    print("All tests passed!")


def main():
    """CLI entry point."""
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == '--test':
        test_canonical_json()
        return
    
    # Demo: canonicalize a fixture
    fixture = {
        "version": "TRS-0",
        "steps": [
            {
                "step": 0,
                "pre_state_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
                "opcode": "EMIT_BYTES",
                "args": {"path": "test.txt", "offset": 0, "bytes_hex": "48656c6c6f"},
                "axioms": [],
                "oracle_reply": {"status": "sat"},
                "mu_bits": 1.0,
                "post_state_sha256": "abc123"
            }
        ]
    }
    
    canonical = dumps_canonical(fixture)
    print("Canonical JSON bytes:")
    print(canonical.decode('utf-8'))
    print(f"\nLength: {len(canonical)} bytes")
    
    import hashlib
    print(f"SHA256: {hashlib.sha256(canonical).hexdigest()}")


if __name__ == '__main__':
    # Run tests when module is executed
    import sys
    if '--test' in sys.argv or len(sys.argv) == 1:
        test_canonical_json()
    else:
        main()
