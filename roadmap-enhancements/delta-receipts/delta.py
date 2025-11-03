#!/usr/bin/env python3
"""
Delta Receipt Generator

Creates efficient delta receipts that contain only changes from a base receipt.
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Dict, Any, List, Set


def load_receipt(path: Path) -> Dict[str, Any]:
    """Load and parse a receipt file."""
    with open(path, 'r') as f:
        return json.load(f)


def compute_file_set(receipt: Dict[str, Any]) -> Set[str]:
    """Get set of file paths in a receipt."""
    return {f['path'] for f in receipt.get('files', [])}


def find_file(receipt: Dict[str, Any], path: str) -> Dict[str, Any]:
    """Find a file entry by path."""
    for f in receipt.get('files', []):
        if f['path'] == path:
            return f
    raise KeyError(f"File not found: {path}")


def create_delta_receipt(
    base_receipt: Dict[str, Any],
    new_receipt: Dict[str, Any],
    base_source: str = None,
) -> Dict[str, Any]:
    """
    Create a delta receipt from base to new.
    
    Args:
        base_receipt: Base receipt
        new_receipt: New receipt
        base_source: URL or path to base receipt (optional)
    
    Returns:
        Delta receipt
    """
    base_files = compute_file_set(base_receipt)
    new_files = compute_file_set(new_receipt)
    
    # Identify changes
    added = new_files - base_files
    deleted = base_files - new_files
    potentially_modified = base_files & new_files
    
    # Check for actual modifications
    modified = []
    for path in potentially_modified:
        base_file = find_file(base_receipt, path)
        new_file = find_file(new_receipt, path)
        
        if base_file['content_sha256'] != new_file['content_sha256']:
            modified.append(path)
    
    # Build delta
    delta = {
        'version': 'TRS-DELTA-1',
        'base_receipt': {
            'global_digest': base_receipt.get('global_digest', ''),
        },
        'delta': {
            'added_files': [find_file(new_receipt, p) for p in sorted(added)],
            'modified_files': [find_file(new_receipt, p) for p in sorted(modified)],
            'deleted_files': list(sorted(deleted)),
        },
        'global_digest': new_receipt.get('global_digest', ''),
    }
    
    if base_source:
        delta['base_receipt']['source'] = base_source
    
    return delta


def compute_delta_size(delta: Dict[str, Any]) -> int:
    """Compute size of delta receipt in bytes."""
    return len(json.dumps(delta, sort_keys=True, separators=(',', ':')))


def main():
    parser = argparse.ArgumentParser(
        description='Create delta receipt from base and new receipts'
    )
    
    parser.add_argument('--base', type=Path, required=True, help='Base receipt')
    parser.add_argument('--new', type=Path, required=True, help='New receipt')
    parser.add_argument('--out', type=Path, required=True, help='Output delta receipt')
    parser.add_argument('--base-source', type=str, help='URL/path to base receipt')
    
    args = parser.parse_args()
    
    # Load receipts
    print(f"Loading base: {args.base}")
    base_receipt = load_receipt(args.base)
    
    print(f"Loading new: {args.new}")
    new_receipt = load_receipt(args.new)
    
    # Create delta
    print("Computing delta...")
    delta = create_delta_receipt(base_receipt, new_receipt, args.base_source)
    
    # Stats
    added = len(delta['delta']['added_files'])
    modified = len(delta['delta']['modified_files'])
    deleted = len(delta['delta']['deleted_files'])
    
    print(f"\nDelta summary:")
    print(f"  Added: {added} files")
    print(f"  Modified: {modified} files")
    print(f"  Deleted: {deleted} files")
    
    # Size comparison
    base_size = len(json.dumps(base_receipt, sort_keys=True))
    new_size = len(json.dumps(new_receipt, sort_keys=True))
    delta_size = compute_delta_size(delta)
    
    print(f"\nSize comparison:")
    print(f"  Base: {base_size:,} bytes")
    print(f"  New: {new_size:,} bytes")
    print(f"  Delta: {delta_size:,} bytes")
    print(f"  Savings: {100 * (1 - delta_size / new_size):.1f}%")
    
    # Write delta
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, 'w') as f:
        json.dump(delta, f, indent=2, sort_keys=True)
    
    print(f"\n✓ Delta receipt written: {args.out}")


if __name__ == '__main__':
    main()
