#!/usr/bin/env python3
"""
Delta Receipt Replay

Applies a delta receipt to a base receipt to reconstruct the new state.
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Dict, Any, List


def load_receipt(path: Path) -> Dict[str, Any]:
    """Load and parse a receipt file."""
    with open(path, 'r') as f:
        return json.load(f)


def apply_delta(base_receipt: Dict[str, Any], delta_receipt: Dict[str, Any]) -> Dict[str, Any]:
    """
    Apply a delta receipt to a base receipt.
    
    Args:
        base_receipt: Base receipt
        delta_receipt: Delta receipt
    
    Returns:
        New receipt after applying delta
    """
    # Verify delta format
    if delta_receipt.get('version') != 'TRS-DELTA-1':
        raise ValueError(f"Invalid delta version: {delta_receipt.get('version')}")
    
    # Verify base digest matches
    base_digest = base_receipt.get('global_digest', '')
    expected_base = delta_receipt['base_receipt']['global_digest']
    
    if base_digest != expected_base:
        raise ValueError(
            f"Base digest mismatch!\n"
            f"  Expected: {expected_base}\n"
            f"  Got: {base_digest}"
        )
    
    # Start with base files
    files_by_path = {f['path']: f for f in base_receipt.get('files', [])}
    
    # Apply deletions
    for path in delta_receipt['delta'].get('deleted_files', []):
        if path in files_by_path:
            del files_by_path[path]
            print(f"  Deleted: {path}")
    
    # Apply modifications
    for file_entry in delta_receipt['delta'].get('modified_files', []):
        path = file_entry['path']
        files_by_path[path] = file_entry
        print(f"  Modified: {path}")
    
    # Apply additions
    for file_entry in delta_receipt['delta'].get('added_files', []):
        path = file_entry['path']
        files_by_path[path] = file_entry
        print(f"  Added: {path}")
    
    # Reconstruct new receipt
    new_receipt = {
        'version': base_receipt.get('version', 'TRS-0-INLINE'),
        'files': sorted(files_by_path.values(), key=lambda f: f['path']),
        'global_digest': delta_receipt['global_digest'],
    }
    
    return new_receipt


def compute_global_digest(files: List[Dict[str, Any]]) -> str:
    """Compute global digest from file entries."""
    hasher = hashlib.sha256()
    
    sorted_files = sorted(files, key=lambda f: f['path'])
    
    for file_entry in sorted_files:
        hasher.update(file_entry['path'].encode('utf-8'))
        hasher.update(file_entry['content_sha256'].encode('utf-8'))
        
        if file_entry.get('executable', False):
            hasher.update(b'executable')
    
    return hasher.hexdigest()


def main():
    parser = argparse.ArgumentParser(
        description='Apply delta receipt to base receipt'
    )
    
    parser.add_argument('--base', type=Path, required=True, help='Base receipt')
    parser.add_argument('--delta', type=Path, required=True, help='Delta receipt')
    parser.add_argument('--out', type=Path, help='Output new receipt (optional)')
    parser.add_argument('--print-digest', action='store_true', help='Print global digest')
    parser.add_argument('--verify', action='store_true', help='Verify digest matches')
    
    args = parser.parse_args()
    
    # Load receipts
    print(f"Loading base: {args.base}")
    base_receipt = load_receipt(args.base)
    
    print(f"Loading delta: {args.delta}")
    delta_receipt = load_receipt(args.delta)
    
    # Apply delta
    print("\nApplying delta...")
    new_receipt = apply_delta(base_receipt, delta_receipt)
    
    # Compute and verify digest
    computed_digest = compute_global_digest(new_receipt['files'])
    expected_digest = new_receipt['global_digest']
    
    print(f"\nResult:")
    print(f"  Files: {len(new_receipt['files'])}")
    print(f"  Expected digest: {expected_digest}")
    print(f"  Computed digest: {computed_digest}")
    
    if args.verify:
        if computed_digest == expected_digest:
            print("\n✓ Digest verified successfully!")
        else:
            print("\n✗ Digest verification FAILED!")
            sys.exit(1)
    
    if args.print_digest:
        print(computed_digest)
    
    # Write output if requested
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        with open(args.out, 'w') as f:
            json.dump(new_receipt, f, indent=2, sort_keys=True)
        print(f"\n✓ New receipt written: {args.out}")


if __name__ == '__main__':
    main()
