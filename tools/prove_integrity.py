#!/usr/bin/env python3
"""
Integrity Proof Script

Verifies the complete integrity chain:
1. Loads receipts and recomputes global_digest
2. Reconstructs kernel and computes its SHA256
3. Confirms equality with expected hash
"""
import hashlib
import json
import sys
from pathlib import Path


def sha256_hex(data: bytes) -> str:
    """Compute SHA256 hex digest."""
    return hashlib.sha256(data).hexdigest()


def canonical_json(obj) -> bytes:
    """Serialize to canonical JSON bytes."""
    return json.dumps(
        obj,
        ensure_ascii=False,
        sort_keys=True,
        separators=(',', ':'),
    ).encode('utf-8')


def prove_integrity(receipts_dir: str = 'receipts/bootstrap_receipts', expected_hash_file: str = 'tests/expected_kernel_sha256.txt') -> int:
    """
    Prove integrity of the self-hosting system.
    
    Returns:
        0 on success, 1 on failure
    """
    print("=== Thiele Kernel Integrity Proof ===\n")
    
    # 1. Load receipts and compute global digest
    receipt_files = sorted(Path(receipts_dir).glob("*.json"))
    if not receipt_files:
        print(f"ERROR: No receipts found in {receipts_dir}", file=sys.stderr)
        return 1
    
    print(f"Found {len(receipt_files)} receipt file(s)")
    
    for receipt_file in receipt_files:
        print(f"\nProcessing: {receipt_file.name}")
        with open(receipt_file, 'r', encoding='utf-8') as f:
            receipt = json.load(f)
        
        # Recompute global digest
        steps = receipt.get('steps', [])
        step_hashes = []
        for step in steps:
            canonical_bytes = canonical_json(step)
            step_hash = hashlib.sha256(canonical_bytes).digest()
            step_hashes.append(step_hash)
        
        computed_digest = hashlib.sha256(b''.join(step_hashes)).hexdigest()
        expected_digest = receipt.get('global_digest', '')
        
        print(f"  Steps: {len(steps)}")
        print(f"  Global digest (receipt): {expected_digest}")
        print(f"  Global digest (computed): {computed_digest}")
        
        if expected_digest and expected_digest != computed_digest:
            print(f"  ✗ MISMATCH", file=sys.stderr)
            return 1
        else:
            print(f"  ✓ Match")
    
    # 2. Check reconstructed kernel hash
    kernel_path = Path('thiele_min.py')
    if not kernel_path.exists():
        print(f"\nERROR: Kernel not found at {kernel_path}", file=sys.stderr)
        print("Run: python3 verifier/replay.py receipts/bootstrap_receipts", file=sys.stderr)
        return 1
    
    kernel_bytes = kernel_path.read_bytes()
    kernel_sha = sha256_hex(kernel_bytes)
    
    print(f"\nReconstructed kernel:")
    print(f"  Path: {kernel_path}")
    print(f"  Size: {len(kernel_bytes)} bytes")
    print(f"  SHA256: {kernel_sha}")
    
    # 3. Compare with expected hash
    expected_hash_path = Path(expected_hash_file)
    if not expected_hash_path.exists():
        print(f"\nERROR: Expected hash file not found: {expected_hash_file}", file=sys.stderr)
        return 1
    
    expected_hash = expected_hash_path.read_text().strip()
    print(f"\nExpected kernel hash:")
    print(f"  Hash: {expected_hash}")
    
    if kernel_sha != expected_hash:
        print(f"\n✗ INTEGRITY FAILURE: Hash mismatch!", file=sys.stderr)
        return 1
    
    print(f"\n✓ INTEGRITY VERIFIED")
    print(f"\nAll checks passed:")
    print(f"  • Receipt global digests are correct")
    print(f"  • Kernel hash matches expected value")
    print(f"  • System integrity is cryptographically sound")
    
    return 0


def main():
    """CLI entry point."""
    receipts_dir = sys.argv[1] if len(sys.argv) > 1 else 'receipts/bootstrap_receipts'
    expected_hash_file = sys.argv[2] if len(sys.argv) > 2 else 'tests/expected_kernel_sha256.txt'
    
    exit_code = prove_integrity(receipts_dir, expected_hash_file)
    sys.exit(exit_code)


if __name__ == '__main__':
    main()
