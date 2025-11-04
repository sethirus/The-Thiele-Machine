#!/usr/bin/env python3
"""Standalone offline receipt verifier - zero dependencies!"""

import sys
import json
import hashlib
from pathlib import Path

def sha256_file(filepath):
    """Compute SHA-256 hash of file contents."""
    h = hashlib.sha256()
    with open(filepath, 'rb') as f:
        while True:
            chunk = f.read(8192)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()

def canonical_json(obj):
    """Convert Python object to canonical JSON (sorted keys, no whitespace), return bytes."""
    return json.dumps(obj, separators=(',', ':'), sort_keys=True, ensure_ascii=False).encode('utf-8')

def compute_file_hash(file_obj):
    """Compute hash of a file object as per TRS-1.0 spec."""
    canonical = canonical_json(file_obj)
    return hashlib.sha256(canonical).hexdigest()

def compute_global_digest(files):
    """
    Compute global digest from files array as per TRS-1.0 spec.
    
    Algorithm (TRS-1.0):
    1. For each file object, compute canonical JSON and SHA-256 hash
    2. Concatenate all hashes (as hex strings)
    3. Convert concatenated hex to bytes
    4. Compute SHA-256 of the bytes
    """
    file_hashes = [compute_file_hash(f) for f in files]
    concatenated = ''.join(file_hashes)
    # Convert hex string to bytes
    hex_bytes = bytes.fromhex(concatenated)
    return hashlib.sha256(hex_bytes).hexdigest()

def verify_receipt(receipt_path, file_paths):
    """Verify a TRS-1.0 receipt against actual files."""
    # Load receipt
    try:
        with open(receipt_path, 'r') as f:
            receipt = json.load(f)
    except Exception as e:
        return False, f"Failed to load receipt: {e}"
    
    # Check required fields
    for field in ['version', 'files', 'global_digest']:
        if field not in receipt:
            return False, f"Invalid receipt: Missing field '{field}'"
    
    # Get file list from receipt
    receipt_files = receipt.get('files', [])
    if not receipt_files:
        return False, "Receipt contains no files"
    
    # Verify each file
    print(f"\nVerifying {len(receipt_files)} file(s)...")
    print("-" * 60)
    
    for i, file_entry in enumerate(receipt_files):
        # Match receipt entry to actual file path
        actual_path = file_paths[i] if i < len(file_paths) else file_entry.get('path', '')
        
        # Check if file exists
        if not Path(actual_path).exists():
            return False, f"File not found: {actual_path}"
        
        # Compute actual hash
        actual_hash = sha256_file(actual_path)
        expected_hash = file_entry.get('sha256')
        
        # Compare
        if actual_hash != expected_hash:
            return False, f"Hash mismatch for {actual_path}"
        
        print(f"  ✓ {actual_path}")
    
    # Recompute global digest per TRS-1.0 spec
    computed_global = compute_global_digest(receipt_files)
    expected_global = receipt.get('global_digest')
    
    print("-" * 60)
    print(f"\nGlobal Digest:")
    print(f"  Expected: {expected_global}")
    print(f"  Computed: {computed_global}")
    
    if computed_global != expected_global:
        return False, "Global digest mismatch!"
    
    return True, "Receipt verification successful"

def main():
    """Main entry point."""
    if len(sys.argv) < 3:
        print("Usage: python verify_offline.py RECEIPT_FILE ARTIFACT_FILE [...]")
        sys.exit(1)
    
    receipt_path = sys.argv[1]
    file_paths = sys.argv[2:]
    
    print("=" * 60)
    print("  Thiele Offline Receipt Verifier")
    print("=" * 60)
    print(f"\nReceipt: {receipt_path}")
    print(f"Files:   {', '.join(file_paths)}")
    
    success, message = verify_receipt(receipt_path, file_paths)
    
    print("\n" + "=" * 60)
    if success:
        print("✅ " + message)
        print("=" * 60)
        sys.exit(0)
    else:
        print("❌ " + message)
        print("=" * 60)
        sys.exit(1)

if __name__ == '__main__':
    main()
