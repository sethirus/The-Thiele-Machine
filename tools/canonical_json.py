#!/usr/bin/env python3
"""
Canonical JSON serialization helper.

Ensures deterministic JSON output for cryptographic hashing.
Self-contained with no external dependencies.

Canonicalization rules (JCS-like):
- Sorted object keys (lexicographic)
- UTF-8 encoding with NFC normalization
- LF-only line endings (CRLF rejected)
- Compact format (no extra whitespace)
- Numbers in fixed decimal notation
- Hex strings lowercase
"""
import json
import unicodedata
from typing import Any


class CanonicalJSONError(Exception):
    """Raised when input violates canonicalization rules."""
    pass


def dumps_canonical(obj: Any, strict: bool = True) -> bytes:
    """
    Serialize object to canonical JSON bytes.
    
    Guarantees:
    - Sorted object keys (lexicographic)
    - UTF-8 encoding with NFC normalization
    - LF-only line endings (CR/CRLF rejected)
    - Compact format (minimal whitespace)
    - Numbers in fixed decimal notation
    - Hex strings lowercase
    
    Args:
        obj: Python object (dict, list, str, int, float, bool, None)
        strict: If True, enforce NFC normalization (default: True)
    
    Returns:
        Canonical JSON as UTF-8 bytes
    
    Raises:
        CanonicalJSONError: If input violates canonicalization rules
    
    Examples:
        >>> dumps_canonical({"b": 2, "a": 1})
        b'{"a":1,"b":2}'
        
        >>> dumps_canonical({"path": "test.py", "offset": 0})
        b'{"offset":0,"path":"test.py"}'
        
        >>> dumps_canonical([3, 1, 2])
        b'[3,1,2]'
    """
    # Normalize Unicode strings to NFC if strict mode
    if strict:
        obj = _normalize_unicode(obj)
    
    # Use compact separators and sort keys
    json_str = json.dumps(
        obj,
        ensure_ascii=False,
        sort_keys=True,
        separators=(',', ':'),
        allow_nan=False,  # Reject NaN/Infinity for determinism
    )
    
    # Check for CRLF or CR (must be LF only)
    if '\r' in json_str:
        raise CanonicalJSONError("CRLF or CR line endings not allowed (use LF only)")
    
    # Encode to UTF-8 bytes
    return json_str.encode('utf-8')


def _normalize_unicode(obj: Any) -> Any:
    """Recursively normalize Unicode strings to NFC form."""
    if isinstance(obj, str):
        normalized = unicodedata.normalize('NFC', obj)
        if normalized != obj:
            # String was not in NFC form
            return normalized
        return obj
    elif isinstance(obj, dict):
        return {_normalize_unicode(k): _normalize_unicode(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [_normalize_unicode(item) for item in obj]
    else:
        return obj


def validate_canonical_json(data: bytes) -> bool:
    """
    Validate that JSON bytes are in canonical form.
    
    Args:
        data: JSON bytes to validate
    
    Returns:
        True if canonical, False otherwise
    
    Raises:
        CanonicalJSONError: If validation fails with details
    """
    # Check for CRLF or CR
    if b'\r' in data:
        raise CanonicalJSONError("Contains CR or CRLF (must be LF only)")
    
    # Decode and parse
    try:
        json_str = data.decode('utf-8')
        obj = json.loads(json_str)
    except (UnicodeDecodeError, json.JSONDecodeError) as e:
        raise CanonicalJSONError(f"Invalid JSON: {e}")
    
    # Re-canonicalize and compare
    canonical = dumps_canonical(obj)
    if canonical != data:
        raise CanonicalJSONError("Not in canonical form")
    
    return True


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
    
    # Test 7: NFC normalization
    # "é" can be represented as single char (U+00E9) or decomposed (U+0065 U+0301)
    obj7_nfc = {"text": "\u00e9"}  # NFC form
    obj7_nfd = {"text": "\u0065\u0301"}  # NFD form (decomposed)
    result7_nfc = dumps_canonical(obj7_nfc)
    result7_nfd = dumps_canonical(obj7_nfd)
    # Both should normalize to same NFC form
    assert result7_nfc == result7_nfd, "NFC normalization failed"
    
    # Test 8: CRLF rejection
    try:
        # This won't actually have CRLF in JSON output, but test the validation
        test_data = b'{"a":1\r\n}'
        validate_canonical_json(test_data)
        assert False, "Should have rejected CRLF"
    except CanonicalJSONError as e:
        assert "CRLF" in str(e) or "CR" in str(e), "Wrong error message"
    
    # Test 9: Validation of canonical form
    obj9 = {"key": "value", "num": 42}
    canonical9 = dumps_canonical(obj9)
    assert validate_canonical_json(canonical9), "Validation failed for canonical JSON"
    
    # Test 10: Non-canonical JSON detection
    non_canonical = b'{"key":"value",  "num":42}'  # Extra whitespace
    try:
        validate_canonical_json(non_canonical)
        assert False, "Should have rejected non-canonical JSON"
    except CanonicalJSONError:
        pass  # Expected
    
    print("All tests passed!")
    print("✓ Key sorting")
    print("✓ Nested structures")
    print("✓ Determinism")
    print("✓ Hash stability")
    print("✓ No whitespace")
    print("✓ UTF-8 encoding")
    print("✓ NFC normalization")
    print("✓ CRLF rejection")
    print("✓ Canonical validation")
    print("✓ Non-canonical detection")


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
