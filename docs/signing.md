# Receipt Signing with Ed25519

## Overview

Receipts can be cryptographically signed using Ed25519 to provide additional integrity guarantees beyond hash chains. This is optional but recommended for production deployments.

## Why Sign Receipts?

- **Authenticity**: Proves receipts come from a trusted source
- **Non-repudiation**: Signer cannot deny creating the receipt
- **Additional security**: Complements hash-based integrity
- **Trust anchor**: Public key is the root of trust

## Ed25519 Properties

- **Fast**: Signing and verification are very fast
- **Small**: 64-byte signatures, 32-byte keys
- **Secure**: 128-bit security level
- **Deterministic**: Same message always produces same signature

## Signature Scheme

Receipts use the following signature scheme:

```
sig_scheme: "ed25519"
signature: hex(Ed25519Sign(private_key, global_digest))
```

The signature is computed over the `global_digest` field, which is itself a hash of all steps.

## Usage

### Generate Keypair

```bash
python3 tools/sign_receipts.py generate
```

Output:
```
Generated Ed25519 keypair:
Private key: a1b2c3d4...
Public key:  e5f6g7h8...

⚠️  Keep private key secret!
```

**Store the private key securely!** Anyone with the private key can sign receipts.

### Sign a Receipt

```bash
python3 tools/sign_receipts.py sign bootstrap_receipts/050_kernel_emit.json \
    --key <private_key_hex>
```

This adds `sig_scheme` and `signature` fields to the receipt.

### Verify a Signature

```bash
python3 tools/sign_receipts.py verify bootstrap_receipts/050_kernel_emit.json \
    --pubkey <public_key_hex>
```

Exit code 0 = valid, 1 = invalid.

## Receipt Format

Signed receipt structure:

```json
{
  "version": "TRS-0",
  "steps": [...],
  "global_digest": "45bc91102be2a30e3d8f851c375809f5640bed1a180f0597f559d3bb927ef1f7",
  "sig_scheme": "ed25519",
  "signature": "a1b2c3d4e5f6...64_bytes_hex"
}
```

## Verification in Verifier

The verifier (`verifier/replay.py`) can optionally verify signatures. This is not yet implemented but the interface is:

```python
if receipt.get('sig_scheme') == 'ed25519':
    if not verify_signature(receipt, BUILT_IN_PUBLIC_KEY):
        print("Warning: Signature verification failed")
        # Continue or abort based on --strict flag
```

## Public Key Distribution

The public key should be distributed through a trusted channel:

1. **Embedded in verifier**: Hard-code in `verifier/replay.py`
2. **Separate file**: `PUBKEY.txt` in repository
3. **Documentation**: Published in README or website
4. **Multiple keys**: Support key rotation with key IDs

## Key Management

**Private Key Storage:**
- ✓ Hardware security module (HSM)
- ✓ Encrypted keystore
- ✓ Environment variable (CI/CD)
- ✗ Never commit to repository
- ✗ Never share via email/chat

**Key Rotation:**
1. Generate new keypair
2. Sign new receipts with new key
3. Update public key in verifier
4. Old receipts remain valid with old key

## Implementation Notes

### Dependencies

Signing requires the `cryptography` package:

```bash
pip install cryptography
```

This is a **development dependency** only. The verifier can be stdlib-only if you implement pure Python Ed25519 verification (see next section).

### Pure Python Verification

For a truly zero-dependency verifier, implement Ed25519 verification in pure Python:

```python
# Example: Use a small pure-Python Ed25519 library
# (Include in verifier source or vendor)
def verify_ed25519_pure(public_key_bytes, message, signature_bytes):
    # Pure Python implementation
    # See: https://ed25519.cr.yp.to/python/ed25519.py
    ...
```

This keeps the TCB small and avoids external dependencies.

## Security Considerations

1. **Private key security is critical**: Compromise = ability to sign fake receipts
2. **Public key pinning**: Hard-code expected public key in verifier
3. **Key rotation**: Plan for periodic key updates
4. **Signature verification**: Always verify before trusting receipts
5. **Hash-first**: Even with signatures, verify hash chains (defense in depth)

## Example: Complete Workflow

```bash
# 1. Generate keypair (once)
python3 tools/sign_receipts.py generate > keys.txt

# 2. Extract keys
PRIVATE_KEY=$(grep "Private key:" keys.txt | cut -d: -f2 | tr -d ' ')
PUBLIC_KEY=$(grep "Public key:" keys.txt | cut -d: -f2 | tr -d ' ')

# 3. Sign receipt
python3 tools/sign_receipts.py sign bootstrap_receipts/050_kernel_emit.json \
    --key "$PRIVATE_KEY"

# 4. Verify signature
python3 tools/sign_receipts.py verify bootstrap_receipts/050_kernel_emit.json \
    --pubkey "$PUBLIC_KEY"

# 5. Distribute public key
echo "$PUBLIC_KEY" > PUBKEY.txt
git add PUBKEY.txt
```

## Future Enhancements

- Multi-signature support (threshold signatures)
- Timestamping integration
- Revocation lists for compromised keys
- Hardware key support (YubiKey, etc.)

## References

- Ed25519: https://ed25519.cr.yp.to/
- RFC 8032: https://tools.ietf.org/html/rfc8032
- PyNaCl: https://pynacl.readthedocs.io/
