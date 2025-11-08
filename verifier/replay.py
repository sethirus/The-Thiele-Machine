#!/usr/bin/env python3
"""Thiele Receipt Replay Verifier."""

import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

from verifier.signature_utils import (
    SignatureVerificationError,
    TrustContextError,
    TrustManifest,
    TrustManifestError,
    resolve_trust,
    verify_ed25519_signature,
)


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


def compute_receipt_digest(steps: List[Dict[str, Any]]) -> str:
    """Compute the TRS-0 ``global_digest`` from canonicalised ``steps``."""

    step_hashes = []
    for step in steps:
        canonical_bytes = canonical_json(step)
        step_hashes.append(hashlib.sha256(canonical_bytes).digest())
    return hashlib.sha256(b''.join(step_hashes)).hexdigest()


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


def _gather_receipt_files(receipts_path: Path) -> List[Path]:
    """Return an ordered list of receipt JSON files from ``receipts_path``."""

    if receipts_path.is_file():
        return [receipts_path]

    if receipts_path.is_dir():
        return sorted(receipts_path.glob("*.json"))

    return []


def verify_receipts(
    receipts_dir: str,
    max_total_bytes: int = 1024 * 1024,
    path_whitelist: List[str] = None,
    emit_dir: str = '.',
    dry_run: bool = False,
    strict: bool = False,
    trust_manifest: Optional[TrustManifest] = None,
    trusted_pubkey: Optional[str] = None,
    allow_unsigned: bool = False,
) -> int:
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
        print(f"Error: receipts path not found: {receipts_dir}", file=sys.stderr)
        return 1

    # Load all receipt files
    receipt_files = _gather_receipt_files(receipts_path)
    if not receipt_files:
        target = receipts_dir if receipts_path.is_dir() else receipts_path.parent
        print(f"Error: no receipt files found in {target}", file=sys.stderr)
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

        try:
            computed_digest = compute_receipt_digest(receipt['steps'])
        except Exception as exc:
            print(f"Error: failed to compute digest for {receipt_file}: {exc}", file=sys.stderr)
            return 1

        declared_digest = receipt.get('global_digest')
        if computed_digest != declared_digest:
            print(f"Error: receipt global_digest mismatch in {receipt_file}", file=sys.stderr)
            print(f"  Declared: {declared_digest}", file=sys.stderr)
            print(f"  Computed: {computed_digest}", file=sys.stderr)
            return 1

        sig_scheme = receipt.get('sig_scheme')
        signature_hex = receipt.get('signature', '')

        expected_pubkey: Optional[str] = None
        manifest_entry = None
        if sig_scheme == 'ed25519':
            if not signature_hex:
                print(f"Error: receipt {receipt_file.name} missing signature", file=sys.stderr)
                return 1

            manifest_error: Optional[TrustManifestError] = None
            if trust_manifest is not None:
                try:
                    manifest_entry = trust_manifest.select_entry(receipt_file, receipt)
                except TrustManifestError as exc:
                    manifest_error = exc

            if manifest_entry is not None:
                expected_pubkey = manifest_entry.public_key.lower()

                receipt_pubkey = receipt.get('public_key')
                if receipt_pubkey and receipt_pubkey.lower() != expected_pubkey:
                    print(
                        f"Error: public_key in {receipt_file.name} does not match manifest",
                        file=sys.stderr,
                    )
                    return 1

            if trusted_pubkey is not None:
                if manifest_entry is not None and manifest_entry.public_key.lower() != trusted_pubkey.lower():
                    print(
                        f"Error: trusted public key does not match manifest for {receipt_file.name}",
                        file=sys.stderr,
                    )
                    return 1
                expected_pubkey = trusted_pubkey.lower()

            if expected_pubkey is None and manifest_error is not None:
                print(f"Error: {manifest_error}", file=sys.stderr)
                return 1

            if expected_pubkey is None:
                if allow_unsigned:
                    print(
                        f"Warning: no trust anchor for {receipt_file.name}; signature skipped",
                        file=sys.stderr,
                    )
                else:
                    print(
                        f"Error: no trust manifest or trusted public key for {receipt_file.name}",
                        file=sys.stderr,
                    )
                    print(
                        "Hint: provide --trust-manifest <path> or --trusted-pubkey <hex>; "
                        "use --allow-unsigned for testing only.",
                        file=sys.stderr,
                    )
                    return 1
            else:
                try:
                    verify_ed25519_signature(declared_digest, signature_hex, expected_pubkey)
                except SignatureVerificationError as exc:
                    print(
                        f"Error: signature verification failed for {receipt_file.name}: {exc}",
                        file=sys.stderr,
                    )
                    return 1

        else:
            if allow_unsigned:
                print(
                    f"Warning: unsigned receipt {receipt_file.name} accepted due to --allow-unsigned",
                    file=sys.stderr,
                )
            else:
                print(
                    f"Error: receipt {receipt_file.name} must be signed with Ed25519",
                    file=sys.stderr,
                )
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
    
    parser = argparse.ArgumentParser(
        description='Verify TRS-0 receipts with Ed25519 trust enforcement'
    )
    parser.add_argument(
        'receipts_dir',
        help='Receipt JSON file or directory to verify (TRS-0 replay)',
    )
    parser.add_argument('--dry-run', action='store_true', help='Verify only, do not write files')
    parser.add_argument('--emit-dir', default='.', help='Directory to materialize files (default: current)')
    parser.add_argument('--strict', action='store_true', help='Reject unknown fields in receipts')
    parser.add_argument('--print-digest', action='store_true', help='Print only global_digest and exit')
    parser.add_argument('--max-bytes', type=int, default=1024*1024, help='Max total bytes (default: 1 MiB)')
    parser.add_argument('--whitelist', nargs='*', help='Allowed file paths')
    parser.add_argument(
        '--trust-manifest',
        help=(
            'Path to trust_manifest.json (defaults to the receipt location or '
            "receipts/trust_manifest.json if present)"
        ),
    )
    parser.add_argument(
        '--trusted-pubkey',
        help=(
            'Hex-encoded Ed25519 public key trusted for all receipts '
            '(overrides manifest lookup)'
        ),
    )
    parser.add_argument(
        '--allow-unsigned',
        action='store_true',
        help=(
            'Permit unsigned receipts (testing only). Overrides signature '
            'enforcement when no trust anchor is available.'
        ),
    )
    
    args = parser.parse_args()
    
    # Print digest mode
    if args.print_digest:
        import json
        input_path = Path(args.receipts_dir)
        receipt_files = _gather_receipt_files(input_path)
        for receipt_file in receipt_files:
            with open(receipt_file, 'r') as f:
                receipt = json.load(f)
            if 'global_digest' in receipt:
                print(receipt['global_digest'])
        sys.exit(0)

    manifest_path = args.trust_manifest
    if manifest_path is None:
        input_path = Path(args.receipts_dir)
        search_base = input_path if input_path.is_dir() else input_path.parent
        candidate = search_base / 'trust_manifest.json'
        if candidate.exists():
            manifest_path = str(candidate)
        else:
            repo_default = Path('receipts') / 'trust_manifest.json'
            if repo_default.exists():
                manifest_path = str(repo_default)

    # Prefer an explicit trusted pubkey argument; otherwise, if a kernel_public.key
    # file exists (created by CI's generate_kernel_keys.py), use it as the trust anchor.
    kernel_pub = Path("kernel_public.key")
    if args.trusted_pubkey is None and kernel_pub.exists():
        args.trusted_pubkey = kernel_pub.read_text().strip()
        print(f"Using generated trust anchor from kernel_public.key: {args.trusted_pubkey}")

    try:
        trust_manifest, trusted_pubkey = resolve_trust(manifest_path, args.trusted_pubkey)
    except TrustContextError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        if args.allow_unsigned:
            trust_manifest, trusted_pubkey = None, None
        else:
            sys.exit(1)

    # Run verification
    exit_code = verify_receipts(
        args.receipts_dir,
        max_total_bytes=args.max_bytes,
        path_whitelist=args.whitelist,
        emit_dir=args.emit_dir,
        dry_run=args.dry_run,
        strict=args.strict,
        trust_manifest=trust_manifest,
        trusted_pubkey=trusted_pubkey,
        allow_unsigned=args.allow_unsigned,
    )
    sys.exit(exit_code)


# CLI entry point for setuptools
def main_cli():
    """Entry point for thiele-replay command."""
    main()


if __name__ == '__main__':
    main()
