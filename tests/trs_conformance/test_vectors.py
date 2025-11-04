"""
Test vectors for TRS-1.0 conformance testing.

Each test vector is a tuple of (description, receipt_dict, expected_result)
where expected_result is 'valid', 'invalid_integrity', or 'invalid_signature'.
"""

import hashlib
import json


def canonical_json(obj):
    """Canonical JSON as per TRS-1.0 spec."""
    return json.dumps(obj, sort_keys=True, separators=(',', ':')).encode('utf-8')


def compute_file_hash(file_obj):
    """Compute hash of a file object as per TRS-1.0 spec."""
    canonical = canonical_json(file_obj)
    return hashlib.sha256(canonical).hexdigest()


def compute_global_digest(files):
    """Compute global digest from files array as per TRS-1.0 spec."""
    file_hashes = [compute_file_hash(f) for f in files]
    concatenated = ''.join(file_hashes)
    hex_bytes = bytes.fromhex(concatenated)
    return hashlib.sha256(hex_bytes).hexdigest()


# Test Vector 1: Minimal valid unsigned receipt
TEST_MINIMAL_UNSIGNED = {
    "description": "Minimal valid unsigned receipt (hello.txt)",
    "receipt": {
        "version": "TRS-1.0",
        "files": [
            {
                "path": "hello.txt",
                "size": 14,
                "sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447"
            }
        ],
        "global_digest": None,  # Will be computed
        "kernel_sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": ""
    },
    "expected": "valid"
}

# Compute the correct global digest for test vector 1
files = TEST_MINIMAL_UNSIGNED["receipt"]["files"]
TEST_MINIMAL_UNSIGNED["receipt"]["global_digest"] = compute_global_digest(files)


# Test Vector 2: Multi-file unsigned receipt
TEST_MULTIFILE_UNSIGNED = {
    "description": "Multi-file unsigned receipt",
    "receipt": {
        "version": "TRS-1.0",
        "files": [
            {
                "path": "src/main.py",
                "size": 256,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"  # empty file hash for test
            },
            {
                "path": "src/utils.py",
                "size": 512,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            },
            {
                "path": "README.md",
                "size": 1024,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            }
        ],
        "global_digest": None,  # Will be computed
        "kernel_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": ""
    },
    "expected": "valid"
}

files = TEST_MULTIFILE_UNSIGNED["receipt"]["files"]
TEST_MULTIFILE_UNSIGNED["receipt"]["global_digest"] = compute_global_digest(files)


# Test Vector 3: Receipt with metadata
TEST_WITH_METADATA = {
    "description": "Receipt with optional metadata",
    "receipt": {
        "version": "TRS-1.0",
        "files": [
            {
                "path": "app.py",
                "size": 100,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            }
        ],
        "global_digest": None,  # Will be computed
        "kernel_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": "",
        "metadata": {
            "author": "Test Author",
            "description": "Test project",
            "version": "1.0.0",
            "platform": "linux-x86_64"
        }
    },
    "expected": "valid"
}

files = TEST_WITH_METADATA["receipt"]["files"]
TEST_WITH_METADATA["receipt"]["global_digest"] = compute_global_digest(files)


# Test Vector 4: Invalid - wrong global digest
TEST_INVALID_DIGEST = {
    "description": "Invalid receipt - wrong global digest",
    "receipt": {
        "version": "TRS-1.0",
        "files": [
            {
                "path": "hello.txt",
                "size": 14,
                "sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447"
            }
        ],
        "global_digest": "0000000000000000000000000000000000000000000000000000000000000000",  # Wrong!
        "kernel_sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": ""
    },
    "expected": "invalid_integrity"
}


# Test Vector 5: Invalid - missing required field
TEST_MISSING_VERSION = {
    "description": "Invalid receipt - missing version field",
    "receipt": {
        "files": [
            {
                "path": "hello.txt",
                "size": 14,
                "sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447"
            }
        ],
        "global_digest": "computed",
        "kernel_sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": ""
    },
    "expected": "invalid_structure"
}


# Test Vector 6: Invalid - path traversal attempt
TEST_PATH_TRAVERSAL = {
    "description": "Invalid receipt - path traversal attempt",
    "receipt": {
        "version": "TRS-1.0",
        "files": [
            {
                "path": "../etc/passwd",  # Path traversal!
                "size": 100,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            }
        ],
        "global_digest": None,  # Will be computed
        "kernel_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": ""
    },
    "expected": "invalid_path"
}

files = TEST_PATH_TRAVERSAL["receipt"]["files"]
TEST_PATH_TRAVERSAL["receipt"]["global_digest"] = compute_global_digest(files)


# Test Vector 7: Invalid - absolute path
TEST_ABSOLUTE_PATH = {
    "description": "Invalid receipt - absolute path",
    "receipt": {
        "version": "TRS-1.0",
        "files": [
            {
                "path": "/usr/bin/python",  # Absolute path!
                "size": 100,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            }
        ],
        "global_digest": None,  # Will be computed
        "kernel_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": ""
    },
    "expected": "invalid_path"
}

files = TEST_ABSOLUTE_PATH["receipt"]["files"]
TEST_ABSOLUTE_PATH["receipt"]["global_digest"] = compute_global_digest(files)


# Test Vector 8: Empty files array (edge case)
TEST_EMPTY_FILES = {
    "description": "Edge case - empty files array",
    "receipt": {
        "version": "TRS-1.0",
        "files": [],
        "global_digest": None,  # Will be computed
        "kernel_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": ""
    },
    "expected": "valid"  # Empty receipt is technically valid
}

files = TEST_EMPTY_FILES["receipt"]["files"]
TEST_EMPTY_FILES["receipt"]["global_digest"] = compute_global_digest(files)


# Test Vector 9: Unsupported version
TEST_UNSUPPORTED_VERSION = {
    "description": "Invalid receipt - unsupported version",
    "receipt": {
        "version": "TRS-2.0",  # Unsupported!
        "files": [
            {
                "path": "hello.txt",
                "size": 14,
                "sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447"
            }
        ],
        "global_digest": None,  # Will be computed
        "kernel_sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": ""
    },
    "expected": "invalid_version"
}

files = TEST_UNSUPPORTED_VERSION["receipt"]["files"]
TEST_UNSUPPORTED_VERSION["receipt"]["global_digest"] = compute_global_digest(files)


# Test Vector 10: Special characters in paths
TEST_SPECIAL_CHARS = {
    "description": "Valid receipt with special characters in paths",
    "receipt": {
        "version": "TRS-1.0",
        "files": [
            {
                "path": "files/test file with spaces.txt",
                "size": 100,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            },
            {
                "path": "files/test-with-dashes_and_underscores.txt",
                "size": 100,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            },
            {
                "path": "files/тест-unicode.txt",  # Unicode
                "size": 100,
                "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            }
        ],
        "global_digest": None,  # Will be computed
        "kernel_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "timestamp": "2025-11-04T00:00:00.000000+00:00",
        "sig_scheme": "none",
        "signature": ""
    },
    "expected": "valid"
}

files = TEST_SPECIAL_CHARS["receipt"]["files"]
TEST_SPECIAL_CHARS["receipt"]["global_digest"] = compute_global_digest(files)


# Collect all test vectors
ALL_TEST_VECTORS = [
    TEST_MINIMAL_UNSIGNED,
    TEST_MULTIFILE_UNSIGNED,
    TEST_WITH_METADATA,
    TEST_INVALID_DIGEST,
    TEST_MISSING_VERSION,
    TEST_PATH_TRAVERSAL,
    TEST_ABSOLUTE_PATH,
    TEST_EMPTY_FILES,
    TEST_UNSUPPORTED_VERSION,
    TEST_SPECIAL_CHARS,
]


# Generate signed test vector if nacl is available
try:
    from nacl import signing as nacl_signing
    
    # Test Vector 11: Valid signed receipt
    private_key = nacl_signing.SigningKey.generate()
    public_key = private_key.verify_key
    
    TEST_SIGNED_VALID = {
        "description": "Valid signed receipt with Ed25519",
        "receipt": {
            "version": "TRS-1.0",
            "files": [
                {
                    "path": "signed.txt",
                    "size": 100,
                    "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
                }
            ],
            "global_digest": None,  # Will be computed
            "kernel_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            "timestamp": "2025-11-04T00:00:00.000000+00:00",
            "sig_scheme": "ed25519",
            "signature": None,  # Will be computed
            "public_key": public_key.encode().hex()
        },
        "expected": "valid"
    }
    
    files = TEST_SIGNED_VALID["receipt"]["files"]
    global_digest = compute_global_digest(files)
    TEST_SIGNED_VALID["receipt"]["global_digest"] = global_digest
    
    # Sign the global digest
    message = global_digest.encode('utf-8')
    signature = private_key.sign(message).signature
    TEST_SIGNED_VALID["receipt"]["signature"] = signature.hex()
    
    ALL_TEST_VECTORS.append(TEST_SIGNED_VALID)
    
    # Test Vector 12: Invalid signature
    TEST_SIGNED_INVALID = {
        "description": "Invalid signed receipt - wrong signature",
        "receipt": {
            "version": "TRS-1.0",
            "files": [
                {
                    "path": "signed.txt",
                    "size": 100,
                    "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
                }
            ],
            "global_digest": global_digest,
            "kernel_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            "timestamp": "2025-11-04T00:00:00.000000+00:00",
            "sig_scheme": "ed25519",
            "signature": "0" * 128,  # Invalid signature!
            "public_key": public_key.encode().hex()
        },
        "expected": "invalid_signature"
    }
    
    ALL_TEST_VECTORS.append(TEST_SIGNED_INVALID)
    
except ImportError:
    # nacl not available, skip signed test vectors
    pass
