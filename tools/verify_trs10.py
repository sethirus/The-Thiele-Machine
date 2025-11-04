#!/usr/bin/env python3
"""
Simple TRS-1.0 receipt verifier for testing purposes.
Verifies the integrity of receipts created by create_receipt.py.
"""

import hashlib
import json
import sys
from pathlib import Path


def sha256_hex(data: bytes) -> str:
    """Compute SHA256 hex digest."""
    return hashlib.sha256(data).hexdigest()


def canonical_json(obj):
    """Compute canonical JSON as per TRS-1.0 spec."""
    return json.dumps(obj, sort_keys=True, separators=(',', ':')).encode('utf-8')


def compute_file_hash(file_obj):
    """Compute hash of a file object as per TRS-1.0 spec."""
    canonical = canonical_json(file_obj)
    return sha256_hex(canonical)


def compute_global_digest(files):
    """
    Compute global digest from files array as per TRS-1.0 spec.
    
    Algorithm:
    1. For each file object, compute canonical JSON and SHA-256 hash
    2. Concatenate all hashes (as hex strings)
    3. Convert concatenated hex to bytes
    4. Compute SHA-256 of the bytes
    """
    file_hashes = [compute_file_hash(f) for f in files]
    concatenated = ''.join(file_hashes)
    # Convert hex string to bytes
    hex_bytes = bytes.fromhex(concatenated)
    return sha256_hex(hex_bytes)


def verify_trs10_receipt(receipt_path: Path, files_dir: Path = None) -> bool:
    """
    Verify a TRS-1.0 format receipt.
    
    Args:
        receipt_path: Path to the receipt JSON file
        files_dir: Directory containing the files (defaults to receipt's parent dir)
    
    Returns:
        True if verification succeeds, False otherwise
    """
    if files_dir is None:
        files_dir = receipt_path.parent
    
    try:
        with open(receipt_path) as f:
            receipt = json.load(f)
        
        # Check version
        if "version" not in receipt:
            print("Error: Missing 'version' field", file=sys.stderr)
            return False
        
        if not receipt["version"].startswith("TRS-1"):
            print(f"Error: Unsupported version: {receipt['version']}", file=sys.stderr)
            return False
        
        # Check required fields
        if "files" not in receipt:
            print("Error: Missing 'files' field", file=sys.stderr)
            return False
        
        if "global_digest" not in receipt:
            print("Error: Missing 'global_digest' field", file=sys.stderr)
            return False
        
        # Verify each file
        for file_entry in receipt["files"]:
            file_path = files_dir / file_entry["path"]
            
            if not file_path.exists():
                print(f"Error: File not found: {file_entry['path']}", file=sys.stderr)
                return False
            
            # Compute file hash
            with open(file_path, 'rb') as f:
                file_hash = sha256_hex(f.read())
            
            # Verify against receipt
            if file_hash != file_entry["sha256"]:
                print(f"Error: Hash mismatch for {file_entry['path']}", file=sys.stderr)
                print(f"  Expected: {file_entry['sha256']}", file=sys.stderr)
                print(f"  Got:      {file_hash}", file=sys.stderr)
                return False
        
        # Verify global digest per TRS-1.0 spec
        computed_global = compute_global_digest(receipt["files"])
        
        if computed_global != receipt["global_digest"]:
            print(f"Error: Global digest mismatch", file=sys.stderr)
            print(f"  Expected: {receipt['global_digest']}", file=sys.stderr)
            print(f"  Got:      {computed_global}", file=sys.stderr)
            return False
        
        # Verify signature if present
        if "signature" in receipt and receipt["signature"]:
            if receipt.get("sig_scheme") != "none":
                print("Warning: Signature verification not implemented", file=sys.stderr)
        
        print(f"✓ Receipt verified: {len(receipt['files'])} file(s)")
        print(f"✓ Global digest: {receipt['global_digest']}")
        
        return True
        
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return False


def main():
    if len(sys.argv) < 2:
        print("Usage: verify_trs10.py <receipt.json>", file=sys.stderr)
        sys.exit(1)
    
    receipt_path = Path(sys.argv[1])
    
    if not receipt_path.exists():
        print(f"Error: Receipt not found: {receipt_path}", file=sys.stderr)
        sys.exit(1)
    
    if verify_trs10_receipt(receipt_path):
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
