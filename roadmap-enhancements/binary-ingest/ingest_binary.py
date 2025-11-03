#!/usr/bin/env python3
"""
Binary Ingest Tool for Thiele Receipts

Convert any binary or directory into a TRS-0 receipt with cryptographic verification.
This enables "day one" adoption - wrap existing binaries in verifiable receipts.

Usage:
    python3 ingest_binary.py /path/to/binary --out receipt.json
    python3 ingest_binary.py /path/to/directory --out receipt.json --recursive
"""

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import List, Dict, Any, Optional


def sha256_file(path: Path) -> str:
    """Compute SHA256 of a file."""
    hasher = hashlib.sha256()
    with open(path, 'rb') as f:
        while chunk := f.read(8192):
            hasher.update(chunk)
    return hasher.hexdigest()


def is_executable(path: Path) -> bool:
    """Check if file has executable permission."""
    return os.access(path, os.X_OK)


def chunk_file_deterministically(path: Path, chunk_size: int = 4096) -> List[Dict[str, Any]]:
    """
    Chunk a file deterministically for receipt generation.
    
    Returns list of chunks with offset, size, and SHA256.
    """
    chunks = []
    with open(path, 'rb') as f:
        offset = 0
        while True:
            data = f.read(chunk_size)
            if not data:
                break
            
            chunks.append({
                'offset': offset,
                'size': len(data),
                'sha256': hashlib.sha256(data).hexdigest(),
            })
            offset += len(data)
    
    return chunks


def ingest_file(path: Path, relative_to: Optional[Path] = None) -> Dict[str, Any]:
    """
    Ingest a single file into receipt format.
    
    Args:
        path: Absolute path to file
        relative_to: Base directory for relative paths (optional)
    
    Returns:
        File entry dictionary
    """
    if relative_to:
        rel_path = path.relative_to(relative_to)
    else:
        rel_path = path.name
    
    file_entry = {
        'path': str(rel_path),
        'content_sha256': sha256_file(path),
        'size': path.stat().st_size,
    }
    
    if is_executable(path):
        file_entry['executable'] = True
    
    # Optionally include chunking info for large files
    if path.stat().st_size > 1024 * 1024:  # > 1MB
        file_entry['chunks'] = chunk_file_deterministically(path)
    
    return file_entry


def ingest_directory(directory: Path, recursive: bool = True) -> List[Dict[str, Any]]:
    """
    Ingest all files in a directory.
    
    Args:
        directory: Directory to ingest
        recursive: Whether to recurse into subdirectories
    
    Returns:
        List of file entries
    """
    files = []
    
    if recursive:
        for root, _, filenames in os.walk(directory):
            root_path = Path(root)
            for filename in sorted(filenames):
                file_path = root_path / filename
                if file_path.is_file():
                    files.append(ingest_file(file_path, relative_to=directory))
    else:
        for item in sorted(directory.iterdir()):
            if item.is_file():
                files.append(ingest_file(item, relative_to=directory))
    
    return files


def compute_global_digest(files: List[Dict[str, Any]]) -> str:
    """
    Compute global digest from file entries.
    
    Uses a canonical concatenation of file paths and SHA256s.
    """
    hasher = hashlib.sha256()
    
    # Sort by path for determinism
    sorted_files = sorted(files, key=lambda f: f['path'])
    
    for file_entry in sorted_files:
        # Include path and content hash
        hasher.update(file_entry['path'].encode('utf-8'))
        hasher.update(file_entry['content_sha256'].encode('utf-8'))
        
        # Include executable flag if present
        if file_entry.get('executable', False):
            hasher.update(b'executable')
    
    return hasher.hexdigest()


def create_receipt(
    files: List[Dict[str, Any]],
    description: Optional[str] = None,
    sign: bool = False,
    signing_key_path: Optional[str] = None,
) -> Dict[str, Any]:
    """
    Create a TRS-0 inline receipt from file entries.
    
    Args:
        files: List of file entries
        description: Optional description
        sign: Whether to sign the receipt
        signing_key_path: Path to Ed25519 signing key
    
    Returns:
        Receipt dictionary
    """
    receipt = {
        'version': 'TRS-0-INLINE',
        'global_digest': compute_global_digest(files),
        'files': files,
    }
    
    if description:
        receipt['description'] = description
    
    if sign:
        # Import signing functionality
        try:
            from nacl import signing
            
            if not signing_key_path:
                raise ValueError("Signing key path required when sign=True")
            
            # Load signing key
            with open(signing_key_path, 'rb') as f:
                signing_key = signing.SigningKey(f.read())
            
            # Sign the canonical JSON
            canonical = json.dumps(receipt, sort_keys=True, separators=(',', ':')).encode('utf-8')
            signed = signing_key.sign(canonical)
            
            receipt['signature'] = {
                'algorithm': 'Ed25519',
                'signature': signed.signature.hex(),
                'public_key': signing_key.verify_key.encode().hex(),
            }
        
        except ImportError:
            print("Warning: PyNaCl not installed, skipping signature", file=sys.stderr)
        except Exception as e:
            print(f"Warning: Failed to sign receipt: {e}", file=sys.stderr)
    
    return receipt


def main():
    parser = argparse.ArgumentParser(
        description='Ingest binary or directory into TRS-0 receipt',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Ingest single binary
  python3 ingest_binary.py /usr/bin/busybox --out busybox.receipt.json
  
  # Ingest directory recursively
  python3 ingest_binary.py /my/app --out app.receipt.json --recursive
  
  # Sign with Ed25519 key
  python3 ingest_binary.py ./binary --out receipt.json --sign ed25519.key
        """
    )
    
    parser.add_argument('path', type=Path, help='File or directory to ingest')
    parser.add_argument('--out', type=Path, required=True, help='Output receipt path')
    parser.add_argument('--recursive', action='store_true', help='Recurse into directories')
    parser.add_argument('--description', type=str, help='Receipt description')
    parser.add_argument('--sign', type=Path, help='Sign with Ed25519 key at path')
    parser.add_argument('--pretty', action='store_true', help='Pretty-print JSON')
    
    args = parser.parse_args()
    
    # Check input exists
    if not args.path.exists():
        print(f"Error: Path not found: {args.path}", file=sys.stderr)
        sys.exit(1)
    
    # Ingest files
    print(f"Ingesting: {args.path}")
    
    if args.path.is_file():
        files = [ingest_file(args.path)]
        print(f"  File: {args.path.name}")
        print(f"  Size: {args.path.stat().st_size:,} bytes")
    elif args.path.is_dir():
        files = ingest_directory(args.path, recursive=args.recursive)
        total_size = sum(f['size'] for f in files)
        print(f"  Files: {len(files)}")
        print(f"  Total size: {total_size:,} bytes")
    else:
        print(f"Error: Path is neither file nor directory: {args.path}", file=sys.stderr)
        sys.exit(1)
    
    # Create receipt
    receipt = create_receipt(
        files,
        description=args.description,
        sign=bool(args.sign),
        signing_key_path=str(args.sign) if args.sign else None,
    )
    
    # Write receipt
    args.out.parent.mkdir(parents=True, exist_ok=True)
    
    with open(args.out, 'w') as f:
        if args.pretty:
            json.dump(receipt, f, indent=2, sort_keys=True)
        else:
            json.dump(receipt, f, sort_keys=True, separators=(',', ':'))
    
    print(f"\n✓ Receipt created: {args.out}")
    print(f"  Global digest: {receipt['global_digest']}")
    print(f"  Files: {len(receipt['files'])}")
    
    if 'signature' in receipt:
        print(f"  Signed: Yes (Ed25519)")
        print(f"  Public key: {receipt['signature']['public_key'][:16]}...")
    
    print("\nVerify with:")
    print(f"  python3 verifier/replay.py {args.out} --dry-run --print-digest")


if __name__ == '__main__':
    main()
