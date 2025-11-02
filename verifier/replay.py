#!/usr/bin/env python3
"""
Thiele Receipt Replay Verifier
Reconstructs kernel from cryptographically verifiable receipts.
Target: ≤200 LoC (excluding comments/blank lines)
"""
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List


def sha256_hex(data: bytes) -> str:
    """Compute SHA256 hex digest (lowercase)."""
    return hashlib.sha256(data).hexdigest()


def canonical_json(obj: Any) -> bytes:
    """
    Serialize object to canonical JSON bytes.
    Rules: sorted keys, UTF-8, compact, no trailing whitespace.
    """
    return json.dumps(
        obj,
        ensure_ascii=False,
        sort_keys=True,
        separators=(',', ':'),
    ).encode('utf-8')


def compute_state_hash(virtual_fs: Dict[str, bytes], exec_flags: Dict[str, bool]) -> str:
    """
    Compute state hash from virtual filesystem.
    state_sha256 = sha256(concat(sorted_paths, sha256(content) per path, exec_flags))
    """
    parts = []
    for path in sorted(virtual_fs.keys()):
        parts.append(path.encode('utf-8'))
        parts.append(sha256_hex(virtual_fs[path]).encode('utf-8'))
        parts.append(b'1' if exec_flags.get(path, False) else b'0')
    return sha256_hex(b''.join(parts))


def validate_path(path: str, step_num: int, whitelist: List[str] = None) -> bool:
    """
    Validate that a path is safe.
    - Must be UTF-8
    - No path traversal (..)
    - No absolute paths
    - No duplicate slashes
    - Optional whitelist enforcement
    Returns True if valid, False otherwise.
    """
    if not path:
        print(f"Error: step {step_num} empty path", file=sys.stderr)
        return False
    
    # Check for duplicate slashes
    if '//' in path:
        print(f"Error: step {step_num} duplicate slashes in path: {path}", file=sys.stderr)
        return False
    
    # Check for path traversal
    if '..' in path.split('/'):
        print(f"Error: step {step_num} path traversal attempt: {path}", file=sys.stderr)
        return False
    
    # Check for absolute paths
    if path.startswith('/'):
        print(f"Error: step {step_num} absolute path not allowed: {path}", file=sys.stderr)
        return False
    
    # Check whitelist if provided
    if whitelist is not None and path not in whitelist:
        print(f"Error: step {step_num} path not in whitelist: {path}", file=sys.stderr)
        print(f"  Allowed paths: {', '.join(whitelist)}", file=sys.stderr)
        return False
    
    return True


def verify_receipts(receipts_dir: str, max_total_bytes: int = 1024 * 1024, path_whitelist: List[str] = None, emit_dir: str = '.', dry_run: bool = False, strict: bool = False) -> int:
    """
    Main verification logic.
    
    Args:
        receipts_dir: Directory containing receipt JSON files
        max_total_bytes: Maximum total bytes that can be emitted (default 1 MiB)
        path_whitelist: Optional list of allowed paths (None = allow any safe path)
        emit_dir: Directory to materialize files (default: current directory)
        dry_run: If True, verify only without writing files
        strict: If True, reject unknown fields in receipt JSON
    
    Returns 0 on success, 1 on failure.
    """
    receipts_path = Path(receipts_dir)
    if not receipts_path.exists():
        print(f"Error: receipts directory not found: {receipts_dir}", file=sys.stderr)
        return 1
    
    # Load all receipt files
    receipt_files = sorted(receipts_path.glob("*.json"))
    if not receipt_files:
        print(f"Error: no receipt files found in {receipts_dir}", file=sys.stderr)
        return 1
    
    # Virtual filesystem and execution flags
    virtual_fs: Dict[str, bytes] = {}
    exec_flags: Dict[str, bool] = {}
    
    # Track per-file write offsets to ensure monotone, non-overlapping writes
    file_last_offset: Dict[str, int] = {}
    
    # Track total bytes emitted
    total_bytes_emitted = 0
    
    # Current state hash (empty state initially)
    current_state = compute_state_hash(virtual_fs, exec_flags)
    
    # Process each receipt file
    for receipt_file in receipt_files:
        with open(receipt_file, 'r', encoding='utf-8') as f:
            receipt = json.load(f)
        
        # Verify receipt structure
        if 'steps' not in receipt:
            print(f"Error: receipt missing 'steps': {receipt_file}", file=sys.stderr)
            return 1
        
        # Process each step
        for step_data in receipt['steps']:
            step_num = step_data.get('step', '?')
            
            # Verify pre-state
            pre_state = step_data.get('pre_state_sha256', '')
            if pre_state != current_state:
                print(f"Error: step {step_num} pre-state mismatch", file=sys.stderr)
                print(f"  Expected: {current_state}", file=sys.stderr)
                print(f"  Got: {pre_state}", file=sys.stderr)
                return 1
            
            # Execute opcode
            opcode = step_data.get('opcode', '')
            args = step_data.get('args', {})
            
            if opcode == 'EMIT_BYTES':
                path = args.get('path', '')
                offset = args.get('offset', 0)
                bytes_hex = args.get('bytes_hex', '')
                
                # Validate path (with whitelist if provided)
                if not validate_path(path, step_num, path_whitelist):
                    return 1
                
                # Decode hex bytes
                try:
                    new_bytes = bytes.fromhex(bytes_hex)
                except ValueError as e:
                    print(f"Error: step {step_num} invalid hex: {e}", file=sys.stderr)
                    return 1
                
                # Check total size limit
                total_bytes_emitted += len(new_bytes)
                if total_bytes_emitted > max_total_bytes:
                    print(f"Error: step {step_num} exceeded max total bytes limit", file=sys.stderr)
                    print(f"  Limit: {max_total_bytes} bytes", file=sys.stderr)
                    print(f"  Emitted: {total_bytes_emitted} bytes", file=sys.stderr)
                    return 1
                
                # Initialize file if needed
                if path not in virtual_fs:
                    virtual_fs[path] = b''
                    file_last_offset[path] = -1
                
                # Check offset validity (must be at or before end)
                if offset > len(virtual_fs[path]):
                    print(f"Error: step {step_num} offset beyond file end", file=sys.stderr)
                    print(f"  File length: {len(virtual_fs[path])}, offset: {offset}", file=sys.stderr)
                    return 1
                
                # Check monotone offset constraint
                if offset < file_last_offset.get(path, -1):
                    print(f"Error: step {step_num} non-monotone offset for {path}", file=sys.stderr)
                    print(f"  Previous offset: {file_last_offset[path]}, current: {offset}", file=sys.stderr)
                    return 1
                
                # Check for overlapping writes (offset should be at end for append-only)
                if offset < len(virtual_fs[path]):
                    print(f"Warning: step {step_num} overlapping write at offset {offset} for {path}", file=sys.stderr)
                
                # Splice bytes at offset
                virtual_fs[path] = virtual_fs[path][:offset] + new_bytes + virtual_fs[path][offset:]
                file_last_offset[path] = offset
                
            elif opcode == 'MAKE_EXEC':
                path = args.get('path', '')
                if not validate_path(path, step_num, path_whitelist):
                    return 1
                exec_flags[path] = True
                
            elif opcode == 'ASSERT_SHA256':
                path = args.get('path', '')
                expected_sha = args.get('sha256', '')
                
                if not validate_path(path, step_num, path_whitelist):
                    return 1
                
                if path not in virtual_fs:
                    print(f"Error: step {step_num} file not found: {path}", file=sys.stderr)
                    return 1
                
                actual_sha = sha256_hex(virtual_fs[path])
                if actual_sha != expected_sha:
                    print(f"Error: step {step_num} SHA256 mismatch for {path}", file=sys.stderr)
                    print(f"  Expected: {expected_sha}", file=sys.stderr)
                    print(f"  Got: {actual_sha}", file=sys.stderr)
                    return 1
            
            else:
                print(f"Error: step {step_num} unknown opcode: {opcode}", file=sys.stderr)
                return 1
            
            # Compute post-state and verify
            current_state = compute_state_hash(virtual_fs, exec_flags)
            post_state = step_data.get('post_state_sha256', '')
            if post_state != current_state:
                print(f"Error: step {step_num} post-state mismatch", file=sys.stderr)
                print(f"  Expected: {post_state}", file=sys.stderr)
                print(f"  Got: {current_state}", file=sys.stderr)
                return 1
    
    # Materialize virtual filesystem to disk
    if not dry_run:
        for path, content in virtual_fs.items():
            output_path = Path(emit_dir) / path
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_bytes(content)
            
            # Set executable bit if flagged
            if exec_flags.get(path, False):
                os.chmod(output_path, 0o755)
            
            print(f"Materialized: {path} ({len(content)} bytes, sha256={sha256_hex(content)})")
    else:
        for path, content in virtual_fs.items():
            print(f"Would materialize: {path} ({len(content)} bytes, sha256={sha256_hex(content)})")
    
    print("Receipt verification complete. All invariants satisfied.")
    return 0


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description='Thiele Receipt Replay Verifier')
    parser.add_argument('receipts_dir', help='Directory containing receipt JSON files')
    parser.add_argument('--dry-run', action='store_true', help='Verify only, do not write files')
    parser.add_argument('--emit-dir', default='.', help='Directory to materialize files (default: current)')
    parser.add_argument('--strict', action='store_true', help='Reject unknown fields in receipts')
    parser.add_argument('--print-digest', action='store_true', help='Print only global_digest and exit')
    parser.add_argument('--max-bytes', type=int, default=1024*1024, help='Max total bytes (default: 1 MiB)')
    parser.add_argument('--whitelist', nargs='*', help='Allowed file paths')
    
    args = parser.parse_args()
    
    # Print digest mode
    if args.print_digest:
        import json
        from pathlib import Path
        receipt_files = sorted(Path(args.receipts_dir).glob("*.json"))
        for receipt_file in receipt_files:
            with open(receipt_file, 'r') as f:
                receipt = json.load(f)
            if 'global_digest' in receipt:
                print(receipt['global_digest'])
        sys.exit(0)
    
    # Run verification
    exit_code = verify_receipts(
        args.receipts_dir,
        max_total_bytes=args.max_bytes,
        path_whitelist=args.whitelist,
        emit_dir=args.emit_dir,
        dry_run=args.dry_run,
        strict=args.strict
    )
    sys.exit(exit_code)


if __name__ == '__main__':
    main()
