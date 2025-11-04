"""
TRS-1.0 Conformance Tests

Tests that verify correct implementation of the TRS-1.0 specification
as defined in docs/trs-spec-v1.md.

These tests use the test vectors from test_vectors.py to verify:
1. Valid receipts are accepted
2. Invalid receipts are rejected with appropriate errors
3. Edge cases are handled correctly
"""

import hashlib
import json
import sys
from pathlib import Path

import pytest

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from tests.trs_conformance.test_vectors import (
    ALL_TEST_VECTORS,
    canonical_json,
    compute_file_hash,
    compute_global_digest,
)


class SimpleTRS10Verifier:
    """
    Minimal TRS-1.0 verifier for conformance testing.
    
    This implements the verification algorithm from section 4 of the spec.
    """
    
    def __init__(self):
        self.errors = []
    
    def verify_receipt(self, receipt):
        """
        Verify a TRS-1.0 receipt.
        
        Returns:
            tuple: (is_valid, error_type, error_message)
            error_type: None, 'structure', 'version', 'path', 'integrity', 'signature'
        """
        self.errors = []
        
        try:
            # Check structure
            if not isinstance(receipt, dict):
                return False, 'structure', 'Receipt must be a JSON object'
            
            # Check version
            if 'version' not in receipt:
                return False, 'structure', 'Missing required field: version'
            
            if receipt['version'] != 'TRS-1.0':
                return False, 'version', f'Unsupported version: {receipt["version"]}'
            
            # Check required fields
            required_fields = ['version', 'files', 'global_digest', 'kernel_sha256', 
                             'timestamp', 'sig_scheme', 'signature']
            for field in required_fields:
                if field not in receipt:
                    return False, 'structure', f'Missing required field: {field}'
            
            # Verify paths
            for file_obj in receipt['files']:
                if 'path' not in file_obj:
                    return False, 'structure', 'File object missing path field'
                
                path = file_obj['path']
                
                # Check for path traversal
                if '..' in path.split('/'):
                    return False, 'path', f'Path traversal not allowed: {path}'
                
                # Check for absolute paths
                if path.startswith('/'):
                    return False, 'path', f'Absolute paths not allowed: {path}'
                
                # Check for duplicate slashes
                if '//' in path:
                    return False, 'path', f'Duplicate slashes not allowed: {path}'
            
            # Verify integrity (hash chain)
            computed_digest = compute_global_digest(receipt['files'])
            
            if computed_digest != receipt['global_digest']:
                return False, 'integrity', (
                    f'Global digest mismatch. '
                    f'Expected: {receipt["global_digest"]}, '
                    f'Computed: {computed_digest}'
                )
            
            # Signature verification (basic check, no crypto yet)
            if receipt['sig_scheme'] == 'none':
                if receipt['signature'] != '':
                    return False, 'signature', 'Signature must be empty when sig_scheme is "none"'
            elif receipt['sig_scheme'] == 'ed25519':
                # For now, just check format (full crypto verification in phase 1)
                if not receipt['signature']:
                    return False, 'signature', 'Signature required when sig_scheme is "ed25519"'
                # Would verify signature here with nacl
                pass
            else:
                return False, 'signature', f'Unknown signature scheme: {receipt["sig_scheme"]}'
            
            return True, None, None
            
        except Exception as e:
            return False, 'error', f'Verification error: {str(e)}'


# Fixtures
@pytest.fixture
def verifier():
    """Create a fresh verifier for each test."""
    return SimpleTRS10Verifier()


# Test canonical JSON implementation
class TestCanonicalJSON:
    """Test canonical JSON implementation matches spec."""
    
    def test_key_sorting(self):
        """Keys should be sorted alphabetically."""
        obj = {"z": 1, "a": 2, "m": 3}
        result = canonical_json(obj).decode('utf-8')
        assert result == '{"a":2,"m":3,"z":1}'
    
    def test_nested_sorting(self):
        """Nested keys should also be sorted."""
        obj = {"outer": {"z": 1, "a": 2}}
        result = canonical_json(obj).decode('utf-8')
        assert result == '{"outer":{"a":2,"z":1}}'
    
    def test_compact_format(self):
        """No extra whitespace."""
        obj = {"a": 1, "b": 2}
        result = canonical_json(obj).decode('utf-8')
        assert ' ' not in result
        assert '\n' not in result
    
    def test_unicode_handling(self):
        """Unicode should be preserved."""
        obj = {"тест": "значение"}
        result = canonical_json(obj)
        # Should be valid UTF-8
        result.decode('utf-8')


# Test global digest computation
class TestGlobalDigest:
    """Test global digest computation matches spec."""
    
    def test_single_file(self):
        """Compute digest for single file."""
        files = [
            {
                "path": "test.txt",
                "size": 10,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            }
        ]
        digest = compute_global_digest(files)
        # Should be a valid hex SHA-256
        assert len(digest) == 64
        assert all(c in '0123456789abcdef' for c in digest)
    
    def test_multiple_files(self):
        """Compute digest for multiple files."""
        files = [
            {"path": "a.txt", "size": 10, "sha256": "aaa"},
            {"path": "b.txt", "size": 20, "sha256": "bbb"},
        ]
        # Should not raise
        compute_global_digest(files)
    
    def test_empty_files(self):
        """Empty files array should produce valid digest."""
        digest = compute_global_digest([])
        assert len(digest) == 64


# Test conformance vectors
class TestConformanceVectors:
    """Test all conformance vectors from test_vectors.py."""
    
    @pytest.mark.parametrize("test_vector", ALL_TEST_VECTORS, 
                           ids=[v["description"] for v in ALL_TEST_VECTORS])
    def test_vector(self, verifier, test_vector):
        """Test each conformance vector."""
        receipt = test_vector["receipt"]
        expected = test_vector["expected"]
        description = test_vector["description"]
        
        is_valid, error_type, error_msg = verifier.verify_receipt(receipt)
        
        if expected == "valid":
            assert is_valid, f"{description}: Expected valid, got error: {error_msg}"
        elif expected == "invalid_integrity":
            assert not is_valid, f"{description}: Expected invalid"
            assert error_type == "integrity", f"{description}: Expected integrity error, got {error_type}"
        elif expected == "invalid_structure":
            assert not is_valid, f"{description}: Expected invalid"
            assert error_type == "structure", f"{description}: Expected structure error, got {error_type}"
        elif expected == "invalid_path":
            assert not is_valid, f"{description}: Expected invalid"
            assert error_type == "path", f"{description}: Expected path error, got {error_type}"
        elif expected == "invalid_version":
            assert not is_valid, f"{description}: Expected invalid"
            assert error_type == "version", f"{description}: Expected version error, got {error_type}"
        else:
            pytest.fail(f"Unknown expected result: {expected}")


# Test verifier implementation details
class TestVerifierImplementation:
    """Test verifier correctly implements spec requirements."""
    
    def test_rejects_missing_version(self, verifier):
        """Verifier must reject receipts without version field."""
        receipt = {
            "files": [],
            "global_digest": "abc",
            "kernel_sha256": "abc",
            "timestamp": "2025-11-04T00:00:00Z",
            "sig_scheme": "none",
            "signature": ""
        }
        is_valid, error_type, _ = verifier.verify_receipt(receipt)
        assert not is_valid
        assert error_type == "structure"
    
    def test_rejects_unsupported_version(self, verifier):
        """Verifier must reject unsupported versions."""
        receipt = {
            "version": "TRS-99.0",
            "files": [],
            "global_digest": compute_global_digest([]),
            "kernel_sha256": "abc",
            "timestamp": "2025-11-04T00:00:00Z",
            "sig_scheme": "none",
            "signature": ""
        }
        is_valid, error_type, _ = verifier.verify_receipt(receipt)
        assert not is_valid
        assert error_type == "version"
    
    def test_accepts_unknown_metadata(self, verifier):
        """Verifier must ignore unknown metadata fields (forward compat)."""
        files = [{"path": "test.txt", "size": 10, 
                 "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}]
        receipt = {
            "version": "TRS-1.0",
            "files": files,
            "global_digest": compute_global_digest(files),
            "kernel_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            "timestamp": "2025-11-04T00:00:00Z",
            "sig_scheme": "none",
            "signature": "",
            "unknown_field": "should be ignored",
            "metadata": {
                "unknown_meta": "also ignored"
            }
        }
        is_valid, _, _ = verifier.verify_receipt(receipt)
        assert is_valid
    
    def test_path_traversal_variations(self, verifier):
        """Test various path traversal attempts are rejected."""
        bad_paths = [
            "../etc/passwd",
            "dir/../../../etc/passwd",
            "dir/../../file.txt",
            "./../../etc/passwd",
        ]
        
        for bad_path in bad_paths:
            files = [{"path": bad_path, "size": 10, 
                     "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}]
            receipt = {
                "version": "TRS-1.0",
                "files": files,
                "global_digest": compute_global_digest(files),
                "kernel_sha256": "abc",
                "timestamp": "2025-11-04T00:00:00Z",
                "sig_scheme": "none",
                "signature": ""
            }
            is_valid, error_type, _ = verifier.verify_receipt(receipt)
            assert not is_valid, f"Should reject path: {bad_path}"
            assert error_type == "path", f"Should be path error for: {bad_path}"
    
    def test_absolute_paths_rejected(self, verifier):
        """Test absolute paths are rejected."""
        bad_paths = [
            "/etc/passwd",
            "/usr/bin/python",
            "/home/user/file.txt",
        ]
        
        for bad_path in bad_paths:
            files = [{"path": bad_path, "size": 10,
                     "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}]
            receipt = {
                "version": "TRS-1.0",
                "files": files,
                "global_digest": compute_global_digest(files),
                "kernel_sha256": "abc",
                "timestamp": "2025-11-04T00:00:00Z",
                "sig_scheme": "none",
                "signature": ""
            }
            is_valid, error_type, _ = verifier.verify_receipt(receipt)
            assert not is_valid, f"Should reject path: {bad_path}"
            assert error_type == "path", f"Should be path error for: {bad_path}"


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])
