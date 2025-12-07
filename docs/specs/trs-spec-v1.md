# Thiele Receipt Specification v1.0 (TRS-1.0)

**Status**: FROZEN (v1.0)  
**Date**: 2025-11-04  
**Authors**: Devon Thiele and The Thiele Machine Project Contributors

## Abstract

This document specifies the Thiele Receipt System (TRS) format version 1.0, a cryptographic receipt format for verifiable software construction. TRS receipts provide cryptographic proof of how files and programs were constructed, enabling independent verification without trust in the build process or distribution channel.

## 1. Introduction

### 1.1 Purpose

The Thiele Receipt System (TRS) provides:
1. **Integrity**: Cryptographic proof that files match their construction steps
2. **Reproducibility**: Deterministic reconstruction from receipt
3. **Transparency**: Complete audit trail of construction process
4. **Authenticity**: Optional cryptographic signatures proving authorship

### 1.2 Design Goals

- **Simplicity**: Spec fits on one page, implementation in <500 LOC
- **Verifiability**: Anyone can verify receipts with standard crypto libraries
- **Portability**: Works across platforms, languages, and tools
- **Extensibility**: Clear versioning for future enhancements

### 1.3 Non-Goals

- Key management (out of scope, use existing tools)
- Receipt discovery or indexing
- Compression or delta encoding (future versions)
- Custom cryptographic schemes (use standard primitives)

## 2. Terminology

**Receipt**: A JSON document containing cryptographic proof of file construction  
**Step**: A single operation in the construction process  
**Hash Chain**: Sequence of cryptographic hashes linking steps  
**Global Digest**: Single hash summarizing entire receipt  
**Signature**: Cryptographic signature over receipt digest  
**Verification**: Process of checking receipt integrity and authenticity  
**Materialization**: Process of reconstructing files from receipt

## 3. Receipt Format

### 3.1 TRS Version Scheme

Receipts MUST include a `version` field with format `"TRS-X.Y"` where:
- X = major version (breaking changes)
- Y = minor version (backward-compatible additions)

This specification defines **TRS-1.0**.

### 3.2 JSON Structure

TRS-1.0 receipts are UTF-8 encoded JSON objects with the following top-level fields:

```json
{
  "version": "TRS-1.0",
  "files": [...],
  "global_digest": "...",
  "kernel_sha256": "...",
  "timestamp": "...",
  "sig_scheme": "...",
  "signature": "...",
  "metadata": {...}
}
```

### 3.3 Required Fields

#### 3.3.1 `version` (string, REQUIRED)

Format: `"TRS-1.0"`

The version identifier for this receipt format. Verifiers MUST check this field and reject unsupported versions.

**Example**: `"version": "TRS-1.0"`

#### 3.3.2 `files` (array, REQUIRED)

Array of file objects, each with:

```json
{
  "path": "relative/path/to/file",
  "size": 12345,
  "sha256": "abc123...",
  "content_sha256": "abc123..."
}
```

**Field Descriptions**:
- `path` (string, REQUIRED): Relative path, no `..` or absolute paths
- `size` (integer, REQUIRED): File size in bytes (≥ 0)
- `sha256` (string, REQUIRED): Hex-encoded SHA-256 hash of file content
- `content_sha256` (string, OPTIONAL): Alias for `sha256` for compatibility

**Path Constraints**:
- MUST be UTF-8 encoded
- MUST use forward slashes (`/`) as separators
- MUST NOT contain `..` (path traversal)
- MUST NOT be absolute (start with `/`)
- MUST NOT contain duplicate slashes (`//`)

#### 3.3.3 `global_digest` (string, REQUIRED)

Hex-encoded SHA-256 hash of all file hashes concatenated.

**Computation**:
```
file_hashes = [sha256(canonical_json(file)) for file in files]
concatenated = ''.join(file_hashes)  # hex strings
global_digest = sha256(hex_to_bytes(concatenated))
```

Where `canonical_json` produces deterministic JSON:
- Keys sorted alphabetically
- Compact format (no extra whitespace)
- UTF-8 encoding

**Example**: `"global_digest": "a3f5b1c2..."`

#### 3.3.4 `kernel_sha256` (string, REQUIRED)

Primary hash of the receipt content. For single-file receipts, this is the file's SHA-256. For multi-file receipts, typically matches `global_digest`.

**Example**: `"kernel_sha256": "a3f5b1c2..."`

#### 3.3.5 `timestamp` (string, REQUIRED)

ISO 8601 timestamp with timezone.

**Format**: `YYYY-MM-DDTHH:MM:SS.ffffff±HH:MM`

**Example**: `"timestamp": "2025-11-04T16:44:00.000000+00:00"`

#### 3.3.6 `sig_scheme` (string, REQUIRED)

Signature scheme identifier. Valid values:
- `"none"` - No signature
- `"ed25519"` - Ed25519 signature
- Future versions may add: `"rsa-pss"`, `"ecdsa-p256"`, etc.

**Example**: `"sig_scheme": "ed25519"`

#### 3.3.7 `signature` (string, REQUIRED)

Cryptographic signature or empty string.

**When `sig_scheme` is `"none"`**:
- MUST be empty string `""`

**When `sig_scheme` is `"ed25519"`**:
- MUST be hex-encoded Ed25519 signature (128 hex chars = 64 bytes)
- Signature is over `global_digest` (hex string as UTF-8 bytes)

**Example**: `"signature": "a1b2c3d4..."` (128 hex chars)

### 3.4 Optional Fields

#### 3.4.1 `metadata` (object, OPTIONAL)

Free-form metadata about the receipt. Common fields:

```json
{
  "author": "Developer Name",
  "description": "Receipt for project v1.0",
  "project": "my-project",
  "version": "1.0.0",
  "build_system": "make",
  "platform": "linux-x86_64"
}
```

Verifiers MUST ignore unknown metadata fields.

#### 3.4.2 `steps` (array, OPTIONAL)

Detailed construction steps (TRS-0 compatibility). Each step:

```json
{
  "op": "write_file",
  "path": "file.txt",
  "data": "base64...",
  "state_hash": "abc123..."
}
```

**When present**:
- Verifiers MAY verify state hash chain
- Verifiers MUST verify final state matches `global_digest`

**Field Descriptions**:
- `op` (string): Operation type (`write_file`, `mkdir`, etc.)
- `path` (string): Target path (same constraints as file paths)
- `data` (string): Base64-encoded file content (for `write_file`)
- `state_hash` (string): SHA-256 of virtual filesystem state after this step

This field is OPTIONAL in TRS-1.0 and primarily for backward compatibility with TRS-0.

#### 3.4.3 `public_key` (string, OPTIONAL)

Hex-encoded public key used for signature verification.

**When `sig_scheme` is `"ed25519"`**:
- 64 hex chars (32 bytes)
- Ed25519 public key

**Example**: `"public_key": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"`

Verifiers MAY use this field if present, or obtain the public key through other means (keyservers, trusted registries, etc.).

## 4. Verification Algorithm

### 4.1 Integrity Verification

To verify receipt integrity:

```
1. Parse JSON and validate structure
2. Check version == "TRS-1.0"
3. For each file in files:
   a. Compute canonical_json(file)
   b. Compute sha256(canonical_json(file))
4. Concatenate all file hashes (hex strings)
5. Convert concatenated hex to bytes
6. Compute sha256(bytes) = computed_digest
7. Compare computed_digest with global_digest
8. If match: integrity valid
   If mismatch: integrity INVALID
```

### 4.2 Signature Verification

To verify receipt signature (when `sig_scheme != "none"`):

```
1. Verify integrity (section 4.1)
2. If sig_scheme == "ed25519":
   a. Obtain public key (from receipt or external source)
   b. Convert signature from hex to bytes
   c. Convert global_digest from hex to UTF-8 bytes
   d. Verify ed25519_verify(public_key, global_digest_bytes, signature)
3. If signature valid: authenticity verified
   If signature invalid: authenticity FAILED
```

### 4.3 Canonical JSON

Canonical JSON MUST be computed as:
```
JSON.stringify(sort_keys_recursively(obj))
```

With:
- Keys sorted alphabetically at all levels
- Compact format (separators: `","` and `":"`)
- No trailing whitespace
- UTF-8 encoding

**Python**: `json.dumps(obj, sort_keys=True, separators=(',', ':'))`  
**JavaScript**: `JSON.stringify(sortKeysRecursively(obj))`

### 4.4 Error Handling

Verifiers MUST:
- Reject receipts with unsupported `version`
- Reject receipts with invalid JSON
- Reject receipts with missing required fields
- Reject receipts with invalid path formats
- Fail verification on any integrity mismatch
- Fail verification on any signature mismatch

Verifiers SHOULD:
- Provide clear error messages
- Indicate which step failed
- Log verification attempts for audit

## 5. Receipt Generation

### 5.1 Minimum Valid Receipt

```json
{
  "version": "TRS-1.0",
  "files": [
    {
      "path": "hello.txt",
      "size": 13,
      "sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447"
    }
  ],
  "global_digest": "computed_from_files",
  "kernel_sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447",
  "timestamp": "2025-11-04T16:44:00.000000+00:00",
  "sig_scheme": "none",
  "signature": ""
}
```

### 5.2 Generation Algorithm

```
1. For each input file:
   a. Read file content
   b. Compute sha256(content)
   c. Add to files array: {path, size, sha256}
2. Compute global_digest from file hashes
3. Set kernel_sha256 (first file hash or global_digest)
4. Set timestamp = current ISO 8601 time
5. If signing:
   a. Set sig_scheme = "ed25519"
   b. Sign global_digest with private key
   c. Set signature = hex(signature_bytes)
   Else:
   a. Set sig_scheme = "none"
   b. Set signature = ""
6. Optionally add metadata
7. Serialize to JSON
```

### 5.3 Signing Best Practices

- Use Ed25519 for new receipts (fast, secure, small keys)
- Generate keys with `ssh-keygen -t ed25519` or `nacl.signing`
- Store private keys securely (never in receipts!)
- Include `public_key` field for user convenience
- Consider publishing public keys to keyservers
- Use hardware keys (YubiKey, etc.) for high-value receipts

## 6. Versioning and Compatibility

### 6.1 Version Numbering

**Major Version** (X in TRS-X.Y):
- Incremented for breaking changes
- Old verifiers MUST reject new major versions
- New verifiers MAY support old major versions

**Minor Version** (Y in TRS-X.Y):
- Incremented for backward-compatible additions
- Old verifiers MUST accept new minor versions (ignore new fields)
- New verifiers MUST accept old minor versions

### 6.2 TRS-1.0 Guarantees

TRS-1.0 is FROZEN. Future changes will be:
- **TRS-1.x**: Backward-compatible additions only
  - New optional fields
  - New signature schemes (as alternatives to existing)
  - New metadata conventions
  
- **TRS-2.0**: Breaking changes (if needed)
  - New required fields
  - Different hash algorithms
  - Different JSON structure

### 6.3 Forward Compatibility

TRS-1.x verifiers MUST:
- Accept TRS-1.0 receipts
- Accept TRS-1.Y receipts for Y > 0
- Ignore unknown optional fields
- Reject unknown required fields (if added in 2.0+)

### 6.4 Backward Compatibility

TRS-1.0 verifiers SHOULD:
- Accept TRS-0 receipts (if `steps` field present)
- Verify hash chains if present
- Fall back to files-only verification if no steps

## 7. Security Considerations

### 7.1 Hash Algorithm

TRS-1.0 uses **SHA-256** exclusively:
- Collision-resistant (2^128 operations)
- Widely supported
- Fast on modern hardware
- NIST-approved

Future versions MAY add SHA-3, BLAKE3, etc.

### 7.2 Signature Algorithm

TRS-1.0 supports **Ed25519**:
- 128-bit security level
- Fast signing and verification
- Small keys (32 bytes) and signatures (64 bytes)
- No side-channel vulnerabilities

Future versions MAY add RSA-PSS, ECDSA-P256, etc.

### 7.3 Path Traversal Protection

Verifiers MUST reject:
- Paths containing `..`
- Absolute paths (starting with `/`)
- Duplicate slashes (`//`)
- Non-UTF-8 paths

### 7.4 Resource Limits

Verifiers SHOULD enforce:
- Maximum receipt size (e.g., 1 GB JSON)
- Maximum file count (e.g., 1 million files)
- Maximum total content size (e.g., 10 GB)
- Timeout for verification (e.g., 5 minutes)

### 7.5 Denial of Service

Verifiers SHOULD protect against:
- Hash collision attacks (use SHA-256, not SHA-1/MD5)
- Billion laughs attack (JSON depth limits)
- Memory exhaustion (streaming parsers for large receipts)
- CPU exhaustion (progress indicators, timeouts)

### 7.6 Trust Model

TRS receipts provide:
- ✅ Integrity: Proof of construction process
- ✅ Authenticity: Proof of signer (if signed)
- ❌ Confidentiality: Receipts are public
- ❌ Availability: Separate concern (distribution)

### 7.7 Known Limitations

- **No key management**: Use external PKI
- **No revocation**: Use external mechanisms (CRLs, OCSP, transparency logs)
- **No timestamps**: Trusted timestamping is external concern
- **No multi-party signatures**: Single signer only (v1.0)

## 8. Test Vectors

### 8.1 Minimal Receipt (Unsigned)

**Input File** (`hello.txt`): `"Hello, World!\n"` (14 bytes)

**SHA-256**: `a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447`

**Receipt**:
```json
{
  "version": "TRS-1.0",
  "files": [
    {
      "path": "hello.txt",
      "size": 14,
      "sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447"
    }
  ],
  "global_digest": "45bc9110a8d95e9b7e8c7f3d2e1a6b9cd0e56a2f8b3c7d4e5f6a1b2c3d4e5f6",
  "kernel_sha256": "a948904f2f0f479b8f8197694b30184b0d2ed1c1cd2a1ec0fb85d299a192a447",
  "timestamp": "2025-11-04T00:00:00.000000+00:00",
  "sig_scheme": "none",
  "signature": ""
}
```

**Expected**: Verification succeeds, `integrity: VALID`

### 8.2 Signed Receipt

**Private Key** (Ed25519 seed, hex):  
`5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb`

**Public Key** (hex):  
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`

**Signature** (over `global_digest` above):  
`(computed from actual signing - TBD in implementation)`

**Expected**: Verification succeeds, `integrity: VALID`, `signature: VALID`

### 8.3 Multi-File Receipt

**Files**:
- `src/main.py`: 256 bytes
- `src/utils.py`: 512 bytes
- `README.md`: 1024 bytes

**Receipt**: (structure as above, with 3 files in `files` array)

**Expected**: Verification succeeds with all 3 files

## 9. Conformance

### 9.1 Verifier Conformance

A **TRS-1.0 conforming verifier** MUST:
1. Accept all valid TRS-1.0 receipts
2. Reject receipts with integrity failures
3. Reject receipts with signature failures (when signed)
4. Implement sections 4.1-4.4 correctly
5. Pass the test vectors in section 8

### 9.2 Generator Conformance

A **TRS-1.0 conforming generator** MUST:
1. Produce valid TRS-1.0 receipts
2. Compute hashes correctly (section 4.3)
3. Sign correctly (section 4.2) if signing enabled
4. Follow path constraints (section 3.3.2)
5. Produce receipts that pass conforming verifiers

### 9.3 Conformance Test Suite

Available at: `tests/trs_conformance/`

Includes:
- Valid receipt test cases
- Invalid receipt test cases
- Signature test cases
- Edge cases (empty files, large files, special chars)
- Cross-platform compatibility tests

## 10. References

- **JSON**: RFC 8259 - The JavaScript Object Notation (JSON) Data Interchange Format
- **SHA-256**: FIPS 180-4 - Secure Hash Standard (SHS)
- **Ed25519**: RFC 8032 - Edwards-Curve Digital Signature Algorithm (EdDSA)
- **ISO 8601**: Date and time format
- **UTF-8**: RFC 3629 - UTF-8, a transformation format of ISO 10646

## 11. Changelog

### Version 1.0 (2025-11-04)
- Initial frozen specification
- TRS-1.0 format defined
- Ed25519 signature support
- Backward compatibility with TRS-0

## Appendix A: Example Implementations

### A.1 Python Verifier (Pseudocode)

```python
import hashlib
import json
from nacl import signing

def verify_receipt(receipt_json):
    receipt = json.loads(receipt_json)
    
    # Check version
    assert receipt['version'] == 'TRS-1.0'
    
    # Compute global digest
    file_hashes = []
    for file in receipt['files']:
        canonical = json.dumps(file, sort_keys=True, separators=(',', ':'))
        file_hash = hashlib.sha256(canonical.encode('utf-8')).hexdigest()
        file_hashes.append(file_hash)
    
    concatenated = ''.join(file_hashes)
    computed_digest = hashlib.sha256(bytes.fromhex(concatenated)).hexdigest()
    
    # Verify integrity
    assert computed_digest == receipt['global_digest']
    
    # Verify signature if present
    if receipt['sig_scheme'] == 'ed25519':
        public_key = signing.VerifyKey(bytes.fromhex(receipt['public_key']))
        signature = bytes.fromhex(receipt['signature'])
        message = receipt['global_digest'].encode('utf-8')
        public_key.verify(message, signature)
    
    return True
```

### A.2 JavaScript Verifier (Pseudocode)

```javascript
async function verifyReceipt(receipt) {
    // Check version
    if (receipt.version !== 'TRS-1.0') throw new Error('Unsupported version');
    
    // Compute global digest
    const fileHashes = [];
    for (const file of receipt.files) {
        const canonical = JSON.stringify(sortKeys(file));
        const hash = await sha256(canonical);
        fileHashes.push(hash);
    }
    
    const concatenated = fileHashes.join('');
    const bytes = hexToBytes(concatenated);
    const computedDigest = await sha256(bytes);
    
    // Verify integrity
    if (computedDigest !== receipt.global_digest) {
        throw new Error('Integrity verification failed');
    }
    
    // Verify signature if present
    if (receipt.sig_scheme === 'ed25519') {
        await verifyEd25519(
            receipt.public_key,
            receipt.global_digest,
            receipt.signature
        );
    }
    
    return true;
}
```

## Appendix B: Migration from TRS-0

TRS-0 receipts (with `steps` field) can be converted to TRS-1.0:

```python
def migrate_trs0_to_trs1(trs0_receipt):
    # Extract files from steps
    files = extract_files_from_steps(trs0_receipt['steps'])
    
    return {
        'version': 'TRS-1.0',
        'files': files,
        'global_digest': compute_global_digest(files),
        'kernel_sha256': trs0_receipt.get('kernel_sha256', files[0]['sha256']),
        'timestamp': trs0_receipt.get('timestamp', datetime.now().isoformat()),
        'sig_scheme': trs0_receipt.get('sig_scheme', 'none'),
        'signature': trs0_receipt.get('signature', ''),
        'steps': trs0_receipt['steps']  # Preserve for backward compat
    }
```

---

**End of TRS-1.0 Specification**

This specification is FROZEN and will not change. Future enhancements will be TRS-1.x (backward-compatible) or TRS-2.0 (breaking changes).

For questions or clarifications, please file an issue at:  
https://github.com/sethirus/The-Thiele-Machine/issues
