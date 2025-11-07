#!/usr/bin/env python3
"""TRS-1.0 receipt verifier with Ed25519 authentication.

Simple helper that checks receipts produced by ``create_receipt.py``.
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Dict, Optional

# Ensure the project root (one directory above ``tools/``) is importable when the
# script is executed via ``python tools/verify_trs10.py`` or through subprocess
# helpers that do not install the package first.  This mirrors the logic used in
# the test helpers and keeps the CLI usable without ``pip install .``.
PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from verifier.signature_utils import (
    SignatureVerificationError,
    TrustContextError,
    TrustManifest,
    TrustManifestError,
    resolve_trust,
    verify_ed25519_signature,
)


def sha256_hex(data: bytes) -> str:
    """Compute SHA256 hex digest."""
    return hashlib.sha256(data).hexdigest()


def canonical_json(obj: Dict) -> bytes:
    """Compute canonical JSON as per TRS-1.0 spec."""
    return json.dumps(obj, sort_keys=True, separators=(',', ':')).encode('utf-8')


def compute_file_hash(file_obj: Dict) -> str:
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


def verify_trs10_receipt(
    receipt_path: Path,
    files_dir: Optional[Path] = None,
    trust_manifest: Optional[TrustManifest] = None,
    trusted_pubkey: Optional[str] = None,
    allow_unsigned: bool = False,
) -> bool:
    """
    Verify a TRS-1.0 format receipt.
    
    Args:
        receipt_path: Path to the receipt JSON file
        files_dir: Directory containing the files (defaults to the receipt directory)
    
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

        sig_scheme = receipt.get("sig_scheme")
        signature_hex = receipt.get("signature", "")
        declared_digest = receipt["global_digest"]

        expected_pubkey: Optional[str] = None
        manifest_entry = None
        if sig_scheme == "ed25519":
            if not signature_hex:
                print(f"Error: Receipt {receipt_path.name} missing signature", file=sys.stderr)
                return False

            manifest_error: Optional[TrustManifestError] = None
            if trust_manifest is not None:
                try:
                    manifest_entry = trust_manifest.select_entry(receipt_path, receipt)
                except TrustManifestError as exc:
                    manifest_error = exc

            if manifest_entry is not None:
                expected_pubkey = manifest_entry.public_key.lower()
                receipt_pubkey = receipt.get("public_key")
                if receipt_pubkey and receipt_pubkey.lower() != expected_pubkey:
                    print(
                        f"Error: public_key in {receipt_path.name} does not match manifest",
                        file=sys.stderr,
                    )
                    return False

            if trusted_pubkey is not None:
                if manifest_entry is not None and manifest_entry.public_key.lower() != trusted_pubkey.lower():
                    print(
                        f"Error: trusted public key does not match manifest for {receipt_path.name}",
                        file=sys.stderr,
                    )
                    return False
                expected_pubkey = trusted_pubkey.lower()

            if expected_pubkey is None and manifest_error is not None:
                print(f"Error: {manifest_error}", file=sys.stderr)
                return False

            if expected_pubkey is None:
                if allow_unsigned:
                    print(
                        f"Warning: no trust anchor for {receipt_path.name}; signature skipped",
                        file=sys.stderr,
                    )
                else:
                    print(
                        f"Error: no trust manifest or trusted public key for {receipt_path.name}",
                        file=sys.stderr,
                    )
                    print(
                        "Hint: provide --trust-manifest <path> or --trusted-pubkey <hex>; "
                        "use --allow-unsigned for testing only.",
                        file=sys.stderr,
                    )
                    return False
            else:
                try:
                    verify_ed25519_signature(declared_digest, signature_hex, expected_pubkey)
                except SignatureVerificationError as exc:
                    print(
                        f"Error: signature verification failed for {receipt_path.name}: {exc}",
                        file=sys.stderr,
                    )
                    return False

        else:
            if allow_unsigned:
                print(
                    f"Warning: unsigned receipt {receipt_path.name} accepted due to --allow-unsigned",
                    file=sys.stderr,
                )
            else:
                print(
                    f"Error: receipt {receipt_path.name} must be signed with Ed25519",
                    file=sys.stderr,
                )
                return False

        print(f"✓ Receipt verified: {len(receipt['files'])} file(s)")
        print(f"✓ Global digest: {receipt['global_digest']}")

        return True
        
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Verify TRS-1.0 receipts with Ed25519 trust enforcement"
    )
    parser.add_argument("receipt", help="Path to the receipt JSON file")
    parser.add_argument(
        "--files-dir",
        help="Directory containing the referenced files (defaults to receipt directory)",
    )
    parser.add_argument(
        '--trust-manifest',
        help=(
            'Path to trust_manifest.json (defaults to the receipt directory or '
            "receipts/trust_manifest.json if present)"
        ),
    )
    parser.add_argument(
        '--trusted-pubkey',
        help=(
            'Hex-encoded Ed25519 public key to trust for this receipt '
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

    receipt_path = Path(args.receipt)
    if not receipt_path.exists():
        print(f"Error: Receipt not found: {receipt_path}", file=sys.stderr)
        sys.exit(1)

    files_dir = Path(args.files_dir) if args.files_dir else None
    manifest_path = args.trust_manifest
    if manifest_path is None:
        candidate = receipt_path.parent / 'trust_manifest.json'
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

    if verify_trs10_receipt(
        receipt_path,
        files_dir=files_dir,
        trust_manifest=trust_manifest,
        trusted_pubkey=trusted_pubkey,
        allow_unsigned=args.allow_unsigned,
    ):
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
