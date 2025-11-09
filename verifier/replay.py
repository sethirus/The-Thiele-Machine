#!/usr/bin/env python3
"""Thiele Receipt Replay Verifier."""

import json
import sys
from pathlib import Path

from verifier.replay_helpers import verify_receipts
from verifier.signature_utils import resolve_trust, TrustContextError


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
        from verifier.replay_helpers import _gather_receipt_files
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
