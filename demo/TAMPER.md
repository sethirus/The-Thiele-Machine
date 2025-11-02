# Tamper Evidence Demonstration

## Overview

This demonstration shows how the Thiele receipt verification system detects any tampering with receipts. Even changing a single byte causes verification to fail with clear diagnostic messages.

## What This Proves

The receipt system provides **tamper evidence** through cryptographic hash chains:

1. Each step has a `pre_state_sha256` and `post_state_sha256`
2. Any modification to step data changes the post-state hash
3. The next step's pre-state check immediately detects the mismatch
4. The `global_digest` provides an additional integrity check over all steps

## Running the Demo

```bash
python3 demo/tamper.py
```

### What It Does

1. **Copies** the original kernel receipt to a temporary location
2. **Mutates** one byte in step 0's hex data (changes first byte to `0xff`)
3. **Attempts** verification with the tampered receipt
4. **Shows** the exact error message from the verifier

### Expected Output

```
=== Thiele Receipt Tamper Evidence Demo ===

1. Original receipt copied to: /tmp/.../050_kernel_emit.json
   Original global_digest: 45bc91102be2a30e3d8f851c375809f5640bed1a180f0597f559d3bb927ef1f7

2. Tampering with receipt (changing 1 byte in step 0)...
   Before: 23212f7573722f62696e...
   After:  ff212f7573722f62696e...

3. Attempting verification with tampered receipt...

--- Verifier Output ---
STDERR: Error: step 0 post-state mismatch
  Expected: 314a151945ceecf0243e610f85e26167e874b920d0d2efe266f373df88c97877
  Got: f2b1c6df0b91a34fc82d1e19a83d5b7e62d3bf2c91d3eb7bdb504e2fee17c0f8

--- End Output ---

✓ SUCCESS: Tampered receipt was rejected!
  Exit code: 1

Key observation:
  - The verifier detected the tampering immediately
  - Hash mismatches are reported with exact step and expected/actual values
  - Cryptographic integrity is maintained
```

## How Tamper Detection Works

### 1. State Hash Chain

Each step computes a state hash from the virtual filesystem:

```python
state_sha256 = sha256(
    concat(
        sorted_paths,
        sha256(content) for each path,
        exec_flags
    )
)
```

When step 0's hex data is changed:
- The reconstructed file content is different
- The `post_state_sha256` is different
- Step 1's `pre_state_sha256` check fails

### 2. Immediate Detection

The verifier checks `pre_state == current_state` **before** executing each step:

```python
if pre_state != current_state:
    print(f"Error: step {step_num} pre-state mismatch")
    print(f"  Expected: {current_state}")
    print(f"  Got: {pre_state}")
    return 1  # FAIL
```

### 3. Global Digest

The `global_digest` is computed from all step hashes:

```python
global_digest = sha256(
    sha256(step_0) || sha256(step_1) || ... || sha256(step_n)
)
```

Any change to any step invalidates the global digest.

## Types of Tampering Detected

The system detects:

- ✓ Modified step data (hex bytes, offsets, paths)
- ✓ Reordered steps
- ✓ Added steps
- ✓ Removed steps
- ✓ Modified pre/post state hashes
- ✓ Modified global digest
- ✓ Modified arguments or opcodes

## Security Properties

1. **Tamper-evident**: Any modification is immediately detected
2. **Precise diagnostics**: Error shows exact step and hash mismatch
3. **No false positives**: Valid receipts always verify
4. **Deterministic**: Same receipts → same verification result

## Try It Yourself

Modify the demo to try different tampering scenarios:

```python
# In demo/tamper.py, try:

# 1. Change a different step
receipt['steps'][1]['args']['path'] = 'evil.py'

# 2. Reorder steps
receipt['steps'][0], receipt['steps'][1] = receipt['steps'][1], receipt['steps'][0]

# 3. Modify a hash
receipt['steps'][0]['post_state_sha256'] = 'invalid_hash'

# 4. Change global digest
receipt['global_digest'] = 'tampered_digest'
```

All will be detected!

## Cryptographic Foundation

The tamper evidence relies on:

- **SHA-256**: Collision-resistant hash function
- **Hash chains**: Each step depends on previous state
- **Canonical serialization**: Deterministic JSON formatting
- **Merkle tree**: Global digest acts as root hash

This makes it **computationally infeasible** to forge a valid receipt.

## Limitations

What this does NOT protect against:

- ❌ Complete replacement of all receipts (would need signature verification)
- ❌ Social engineering (user accepting wrong hash)
- ❌ Compromised verifier code

For protection against these, see:
- **Item E**: Signed receipts (Ed25519) - cryptographic signing
- **Small TCB**: Only 210 LoC to audit
- **Diverse replay**: Multiple independent verifiers

## Conclusion

The Thiele receipt system provides strong tamper evidence through:
1. Cryptographic hash chains
2. Immediate detection at step boundaries
3. Clear diagnostic messages
4. Deterministic verification

Run `python3 demo/tamper.py` to see it in action!
