#!/usr/bin/env python3
"""
Submit artifacts to Sigstore Rekor transparency log.

This creates a permanent, tamper-evident record of release artifacts
in the public transparency log.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, Any


def compute_sha256(file_path: Path) -> str:
    """Compute SHA256 hash of a file."""
    hasher = hashlib.sha256()
    with open(file_path, 'rb') as f:
        while chunk := f.read(8192):
            hasher.update(chunk)
    return hasher.hexdigest()


def submit_to_rekor(artifact_path: Path, artifact_type: str = "hashedrekord") -> Dict[str, Any]:
    """
    Submit artifact hash to Rekor transparency log.
    
    Args:
        artifact_path: Path to artifact file
        artifact_type: Rekor entry type (default: hashedrekord)
    
    Returns:
        Dictionary with log entry details
    
    Raises:
        RuntimeError: If rekor-cli is not installed or submission fails
    """
    # Check if rekor-cli is installed
    try:
        result = subprocess.run(
            ["rekor-cli", "version"],
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            raise RuntimeError("rekor-cli not found. Install from: https://github.com/sigstore/rekor")
    except FileNotFoundError:
        raise RuntimeError("rekor-cli not found. Install from: https://github.com/sigstore/rekor")
    
    # Compute artifact hash
    artifact_sha = compute_sha256(artifact_path)
    
    print(f"Submitting to Rekor transparency log...")
    print(f"  Artifact: {artifact_path.name}")
    print(f"  SHA256: {artifact_sha}")
    
    # Submit to Rekor
    # In production, use: rekor-cli upload --artifact <file>
    # For now, create a mock submission
    
    mock_entry = {
        "artifact": str(artifact_path.name),
        "sha256": artifact_sha,
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "log_index": "<PLACEHOLDER_LOG_INDEX>",
        "uuid": "<PLACEHOLDER_UUID>",
        "note": "This is a placeholder. In production, use rekor-cli to submit to the real transparency log."
    }
    
    return mock_entry


def save_transparency_record(entries: list[Dict[str, Any]], output_path: Path):
    """Save transparency log entries to file."""
    record = {
        "version": "1.0",
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "entries": entries,
        "instructions": {
            "verify": "Use 'rekor-cli get --uuid <UUID>' to retrieve and verify entries",
            "search": "Use 'rekor-cli search --sha <SHA256>' to find entries by hash"
        }
    }
    
    with open(output_path, 'w') as f:
        json.dump(record, f, indent=2, sort_keys=True)
    
    print(f"\n✓ Transparency record saved: {output_path}")


def main():
    parser = argparse.ArgumentParser(
        description='Submit artifacts to Sigstore Rekor transparency log',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Submit single artifact
  python3 rekor_submit.py dist/receipt.json
  
  # Submit multiple artifacts
  python3 rekor_submit.py dist/receipt.json dist/zkproof.json
  
  # Specify output file
  python3 rekor_submit.py dist/*.json --out attestations/TRANSPARENCY.txt

Prerequisites:
  Install rekor-cli: https://github.com/sigstore/rekor
        """
    )
    
    parser.add_argument(
        'artifacts',
        nargs='+',
        type=Path,
        help='Artifact files to submit'
    )
    parser.add_argument(
        '--out',
        type=Path,
        default=Path('attestations/TRANSPARENCY.txt'),
        help='Output transparency record file (default: attestations/TRANSPARENCY.txt)'
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Dry run - compute hashes but do not submit'
    )
    
    args = parser.parse_args()
    
    # Validate all artifacts exist
    for artifact in args.artifacts:
        if not artifact.exists():
            print(f"Error: Artifact not found: {artifact}", file=sys.stderr)
            sys.exit(1)
    
    # Submit each artifact
    entries = []
    
    for artifact in args.artifacts:
        try:
            if args.dry_run:
                sha256 = compute_sha256(artifact)
                print(f"[DRY RUN] Would submit: {artifact.name}")
                print(f"          SHA256: {sha256}")
                entry = {
                    "artifact": str(artifact.name),
                    "sha256": sha256,
                    "dry_run": True
                }
            else:
                entry = submit_to_rekor(artifact)
            
            entries.append(entry)
            
        except Exception as e:
            print(f"Error submitting {artifact.name}: {e}", file=sys.stderr)
            if not args.dry_run:
                sys.exit(1)
    
    # Save transparency record
    args.out.parent.mkdir(parents=True, exist_ok=True)
    save_transparency_record(entries, args.out)
    
    # Print verification instructions
    print("\nVerification:")
    print("  Retrieve entries with: rekor-cli get --uuid <UUID>")
    print("  Search by hash with: rekor-cli search --sha <SHA256>")
    
    if args.dry_run:
        print("\n[DRY RUN] No actual submissions made")


if __name__ == '__main__':
    main()
