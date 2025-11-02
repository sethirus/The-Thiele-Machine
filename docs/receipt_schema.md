# Thiele Receipt Schema (TRS-0)

## Overview

This document defines the canonical JSON schema for Thiele receipts. Receipts are cryptographically verifiable proofs of construction that allow deterministic reconstruction of the Thiele kernel.

## Top-Level Receipt Structure

```json
{
  "version": "TRS-0",
  "steps": [...],
  "global_digest": "<hex_sha256>",
  "sig_scheme": "ed25519",
  "signature": "<hex_signature>"
}
```

### Top-Level Fields

- **version** (string): Schema version identifier (e.g., "TRS-0")
- **steps** (array): Ordered list of construction steps
- **global_digest** (string): Cryptographic digest of all steps (hex lowercase)
- **sig_scheme** (string): Signature scheme (e.g., "ed25519", "none")
- **signature** (string): Cryptographic signature over global_digest (hex lowercase, or empty)

## Step Structure

Each step in the `steps` array has the following structure:

```json
{
  "step": 0,
  "pre_state_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "opcode": "EMIT_BYTES",
  "args": {
    "path": "thiele_min.py",
    "offset": 0,
    "bytes_hex": "23212f7573722f62696e2f656e7620707974686f6e330a"
  },
  "axioms": ["offset_within_file", "no_overlap", "sha_invariant"],
  "oracle_reply": {
    "status": "sat",
    "witness": {"model": {"offset": 0}}
  },
  "mu_bits": 7.0,
  "post_state_sha256": "<computed_hash>"
}
```

### Step Fields

- **step** (integer): Step number (0-indexed, sequential)
- **pre_state_sha256** (string): State hash before operation (hex lowercase)
- **opcode** (string): Operation to perform (see Opcodes section)
- **args** (object): Operation-specific arguments
- **axioms** (array of strings): Logical axioms that justify this step
- **oracle_reply** (object): Response from constraint solver/oracle
  - **status** (string): "sat", "unsat", or "unknown"
  - **witness** (any): Solver-specific witness/model (freeform)
- **mu_bits** (number): Information-theoretic cost in μ-bits
- **post_state_sha256** (string): State hash after operation (hex lowercase)

## Opcodes

### EMIT_BYTES

Emit bytes to a file at a specific offset.

**Arguments:**
- `path` (string): File path (UTF-8, normalized, no "..")
- `offset` (integer): Byte offset (≥0, ≤ current file length)
- `bytes_hex` (string): Hex-encoded bytes to emit (lowercase)

**Preconditions:**
- Offset must be within file bounds or exactly at end
- No overlapping writes in same step
- Offsets must be monotone non-decreasing per file

**Effect:**
- Splices bytes at the specified offset

### MAKE_EXEC

Mark a file as executable.

**Arguments:**
- `path` (string): File path

**Effect:**
- Sets executable flag (doesn't affect content hash)
- Materialized file will have +x permission

### ASSERT_SHA256

Assert that a file's content matches a given hash.

**Arguments:**
- `path` (string): File path
- `sha256` (string): Expected SHA256 hash (hex lowercase)

**Effect:**
- Verification fails if hash doesn't match
- No state change if successful

## Canonicalization Rules

To ensure deterministic verification, all JSON must be canonicalized:

1. **Encoding**: UTF-8 without BOM
2. **Object keys**: Sorted lexicographically
3. **Whitespace**: Compact format (no unnecessary spaces)
4. **Line endings**: LF (`\n`) only
5. **Hex strings**: Lowercase
6. **Numbers**: Fixed decimal notation (no scientific notation)
7. **String escaping**: Minimal (only required characters escaped)

## State Hashing Algorithm

The state hash captures the complete virtual filesystem state:

```python
def compute_state_hash(virtual_fs, exec_flags):
    """
    Compute deterministic state hash.
    
    Args:
        virtual_fs: dict[path] = bytes
        exec_flags: dict[path] = bool
    
    Returns:
        hex SHA256 hash
    """
    parts = []
    for path in sorted(virtual_fs.keys()):
        parts.append(path.encode('utf-8'))
        parts.append(sha256(virtual_fs[path]).hexdigest().encode('utf-8'))
        parts.append(b'1' if exec_flags.get(path, False) else b'0')
    return sha256(b''.join(parts)).hexdigest()
```

**Empty state hash:**
```
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
```
(This is `sha256(b'')`)

## Global Digest Algorithm

The global digest is computed from all steps:

```python
def compute_global_digest(steps):
    """
    Compute cryptographic digest over all steps.
    
    Each step is independently canonicalized, hashed,
    then all hashes are concatenated and hashed again.
    """
    step_hashes = []
    for step in steps:
        canonical_bytes = dumps_canonical(step)
        step_hash = sha256(canonical_bytes).digest()
        step_hashes.append(step_hash)
    
    return sha256(b''.join(step_hashes)).hexdigest()


def dumps_canonical(obj):
    """Serialize to canonical JSON bytes."""
    import json
    return json.dumps(
        obj,
        ensure_ascii=False,
        sort_keys=True,
        separators=(',', ':'),
    ).encode('utf-8')
```

## Example Receipt

Minimal receipt that emits a simple Python file:

```json
{
  "version": "TRS-0",
  "steps": [
    {
      "step": 0,
      "pre_state_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
      "opcode": "EMIT_BYTES",
      "args": {
        "path": "hello.py",
        "offset": 0,
        "bytes_hex": "7072696e742822486572652069732074686520547275746822290a"
      },
      "axioms": ["initial_emit"],
      "oracle_reply": {
        "status": "sat",
        "witness": null
      },
      "mu_bits": 42.0,
      "post_state_sha256": "a1b2c3d4e5f6..."
    },
    {
      "step": 1,
      "pre_state_sha256": "a1b2c3d4e5f6...",
      "opcode": "MAKE_EXEC",
      "args": {
        "path": "hello.py"
      },
      "axioms": ["exec_permission"],
      "oracle_reply": {
        "status": "sat",
        "witness": null
      },
      "mu_bits": 1.0,
      "post_state_sha256": "b2c3d4e5f6a1..."
    },
    {
      "step": 2,
      "pre_state_sha256": "b2c3d4e5f6a1...",
      "opcode": "ASSERT_SHA256",
      "args": {
        "path": "hello.py",
        "sha256": "abc123..."
      },
      "axioms": ["hash_integrity"],
      "oracle_reply": {
        "status": "sat",
        "witness": null
      },
      "mu_bits": 0.0,
      "post_state_sha256": "b2c3d4e5f6a1..."
    }
  ],
  "global_digest": "fedcba9876543210...",
  "sig_scheme": "none",
  "signature": ""
}
```

## Security Properties

1. **Determinism**: Same receipts always produce identical output
2. **Verifiability**: Any party can verify construction independently
3. **Tamper-evidence**: Modification invalidates global_digest
4. **Minimalism**: Small trusted computing base (TCB)

## Path Validation

All file paths must satisfy:

- UTF-8 encoded
- Normalized (no redundant `.` or `..` components)
- No absolute paths starting with `/` (unless explicitly allowed)
- No path traversal attacks

## Version History

- **TRS-0**: Initial specification (2025)
