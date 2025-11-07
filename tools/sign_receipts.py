#!/usr/bin/env python3
"""
Receipt signing with Ed25519.

Provides cryptographic signing for receipts using Ed25519.
Uses standard library only (no external dependencies for verification).
"""
import hashlib
import json
import sys
from pathlib import Path


def sign_receipt(receipt_path: str, private_key_hex: str, output_path: str = None, key_id: str = None):
    """
    Sign a receipt with Ed25519.
    
    Args:
        receipt_path: Path to receipt JSON file
        private_key_hex: Ed25519 private key (64 hex chars)
        output_path: Output path (default: overwrite original)
    
    Note: Requires 'cryptography' package for signing (dev dependency only).
    Verification can be done with stdlib only.
    """
    try:
        from cryptography.hazmat.primitives.asymmetric import ed25519
        from cryptography.hazmat.primitives import serialization
    except ImportError:
        print("Error: 'cryptography' package required for signing", file=sys.stderr)
        print("Install with: pip install cryptography", file=sys.stderr)
        return False
    
    # Load receipt
    with open(receipt_path, 'r') as f:
        receipt = json.load(f)
    
    # Get global digest
    global_digest = receipt.get('global_digest', '')
    if not global_digest:
        print(f"Error: Receipt missing global_digest", file=sys.stderr)
        return False
    
    # Load private key
    try:
        private_key_bytes = bytes.fromhex(private_key_hex)
        private_key = ed25519.Ed25519PrivateKey.from_private_bytes(private_key_bytes)
        public_key = private_key.public_key()
    except Exception as e:
        print(f"Error loading private key: {e}", file=sys.stderr)
        return False
    
    # Sign the global digest
    message = global_digest.encode('utf-8')
    signature_bytes = private_key.sign(message)
    signature_hex = signature_bytes.hex()
    
    # Update receipt
    receipt['sig_scheme'] = 'ed25519'
    receipt['signature'] = signature_hex

    public_key_hex = public_key.public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()
    receipt['public_key'] = public_key_hex
    if key_id:
        receipt['key_id'] = key_id
    
    # Write output
    output = output_path or receipt_path
    with open(output, 'w') as f:
        json.dump(receipt, f, indent=2, sort_keys=True)
    
    print(f"✓ Receipt signed with Ed25519")
    print(f"  Global digest: {global_digest}")
    print(f"  Signature: {signature_hex[:32]}...")
    print(f"  Output: {output}")
    
    return True


def generate_keypair():
    """
    Generate a new Ed25519 keypair.
    
    Returns:
        Tuple of (private_key_hex, public_key_hex)
    """
    try:
        from cryptography.hazmat.primitives.asymmetric import ed25519
    except ImportError:
        print("Error: 'cryptography' package required", file=sys.stderr)
        return None, None
    
    private_key = ed25519.Ed25519PrivateKey.generate()
    public_key = private_key.public_key()
    
    private_bytes = private_key.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption()
    )
    
    public_bytes = public_key.public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw
    )
    
    return private_bytes.hex(), public_bytes.hex()


def verify_signature_stdlib(global_digest_hex: str, signature_hex: str, public_key_hex: str) -> bool:
    """
    Verify Ed25519 signature (stdlib-only implementation for reference).
    
    Note: For production use with stdlib only, consider using PyNaCl or
    implementing Ed25519 verification in pure Python (complex).
    This is a placeholder showing the interface.
    """
    try:
        from cryptography.hazmat.primitives.asymmetric import ed25519
    except ImportError:
        print("Note: Verification requires 'cryptography' package", file=sys.stderr)
        print("In production, use pure Python Ed25519 implementation", file=sys.stderr)
        return False
    
    try:
        public_key_bytes = bytes.fromhex(public_key_hex)
        public_key = ed25519.Ed25519PublicKey.from_public_bytes(public_key_bytes)
        
        message = global_digest_hex.encode('utf-8')
        signature_bytes = bytes.fromhex(signature_hex)

        public_key.verify(signature_bytes, message)
        return True
    except Exception as e:
        print(f"Signature verification failed: {e}", file=sys.stderr)
        return False


def main():
    """CLI entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Sign Thiele receipts with Ed25519')
    subparsers = parser.add_subparsers(dest='command', help='Commands')
    
    # Generate keypair
    gen_parser = subparsers.add_parser('generate', help='Generate new Ed25519 keypair')
    
    # Sign receipt
    sign_parser = subparsers.add_parser('sign', help='Sign a receipt')
    sign_parser.add_argument('receipt', help='Receipt file to sign')
    sign_parser.add_argument('--key', required=True, help='Private key (hex)')
    sign_parser.add_argument('--output', help='Output file (default: overwrite)')
    sign_parser.add_argument('--key-id', help='Identifier recorded in the signed receipt')
    
    # Verify signature
    verify_parser = subparsers.add_parser('verify', help='Verify a signature')
    verify_parser.add_argument('receipt', help='Signed receipt file')
    verify_parser.add_argument('--pubkey', required=True, help='Public key (hex)')
    
    args = parser.parse_args()
    
    if args.command == 'generate':
        private, public = generate_keypair()
        if private and public:
            print("Generated Ed25519 keypair:")
            print(f"Private key: {private}")
            print(f"Public key:  {public}")
            print("\n⚠️  Keep private key secret!")
    
    elif args.command == 'sign':
        success = sign_receipt(args.receipt, args.key, args.output, key_id=args.key_id)
        sys.exit(0 if success else 1)
    
    elif args.command == 'verify':
        with open(args.receipt, 'r') as f:
            receipt = json.load(f)
        
        global_digest = receipt.get('global_digest', '')
        signature = receipt.get('signature', '')
        
        if verify_signature_stdlib(global_digest, signature, args.pubkey):
            print("✓ Signature valid")
            sys.exit(0)
        else:
            print("✗ Signature invalid")
            sys.exit(1)
    
    else:
        parser.print_help()


if __name__ == '__main__':
    main()
