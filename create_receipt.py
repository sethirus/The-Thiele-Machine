#!/usr/bin/env python3
"""
Simple Thiele Receipt Creator

This script helps you create basic Thiele receipts for your files.
Use this to get started with receipt-based software distribution.

Usage:
    python3 create_receipt.py myfile.py
    python3 create_receipt.py myfile.py --output myfile_receipt.json
    python3 create_receipt.py myfile1.py myfile2.py --output multi_receipt.json
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path
from datetime import datetime


def sha256_file(filepath):
    """Compute SHA256 hash of a file."""
    sha256 = hashlib.sha256()
    with open(filepath, 'rb') as f:
        for chunk in iter(lambda: f.read(4096), b''):
            sha256.update(chunk)
    return sha256.hexdigest()


def create_receipt(files, output_path=None, include_steps=False):
    """
    Create a Thiele receipt for one or more files.
    
    Args:
        files: List of file paths to include in receipt
        output_path: Where to save the receipt (default: auto-generated)
        include_steps: Whether to include detailed TRS-0 steps (default: False, uses TRS-1.0)
    
    Returns:
        dict: The created receipt
    """
    
    file_infos = []
    all_content = b''
    
    for filepath in files:
        path = Path(filepath)
        
        if not path.exists():
            print(f"Error: File not found: {filepath}", file=sys.stderr)
            sys.exit(1)
        
        # Read file content
        with open(path, 'rb') as f:
            content = f.read()
        
        # Compute hash
        content_hash = hashlib.sha256(content).hexdigest()
        
        file_infos.append({
            "path": path.name,
            "size": len(content),
            "sha256": content_hash,
            "content_sha256": content_hash
        })
        
        all_content += content
        
        print(f"✓ Added: {path.name} ({len(content)} bytes, SHA256: {content_hash[:16]}...)")
    
    # Compute global digest (simplified)
    global_digest = hashlib.sha256(all_content).hexdigest()
    
    # Determine receipt version and structure
    if include_steps:
        # TRS-0 with detailed steps
        receipt = create_trs0_receipt(file_infos, global_digest)
    else:
        # TRS-1.0 simplified format
        receipt = {
            "version": "TRS-1.0",
            "files": file_infos,
            "global_digest": global_digest,
            "kernel_sha256": file_infos[0]["sha256"] if len(file_infos) == 1 else global_digest,
            "timestamp": datetime.now().astimezone().isoformat(),
            "sig_scheme": "none",
            "signature": ""
        }
    
    # Determine output path
    if output_path is None:
        if len(files) == 1:
            output_path = f"{Path(files[0]).stem}_receipt.json"
        else:
            output_path = "receipt.json"
    
    # Save receipt
    with open(output_path, 'w') as f:
        json.dump(receipt, f, indent=2, ensure_ascii=False)
    
    print(f"\n✓ Receipt created: {output_path}")
    print(f"✓ Global digest: {global_digest}")
    print(f"\nTo verify and materialize:")
    print(f"  python3 verifier/replay.py {output_path}")
    
    return receipt


def create_trs0_receipt(file_infos, global_digest):
    """Create a TRS-0 receipt with detailed steps."""
    
    # Empty state hash (SHA-256 of empty bytes)
    empty_state = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    
    steps = []
    current_state = empty_state
    
    for idx, file_info in enumerate(file_infos):
        # Read file for hex encoding
        with open(file_info["path"], 'rb') as f:
            content = f.read()
        
        # Create EMIT_BYTES step
        step = {
            "step": idx * 2,
            "pre_state_sha256": current_state,
            "opcode": "EMIT_BYTES",
            "args": {
                "path": file_info["path"],
                "offset": 0,
                "bytes_hex": content.hex()
            },
            "axioms": ["initial_emit" if idx == 0 else "emit_next_file"],
            "oracle_reply": {
                "status": "sat",
                "witness": None
            },
            "mu_bits": len(content) * 8.0,  # 8 bits per byte
            "post_state_sha256": "computed_by_verifier"
        }
        steps.append(step)
        
        # Create ASSERT_SHA256 step
        assert_step = {
            "step": idx * 2 + 1,
            "pre_state_sha256": "computed_by_verifier",
            "opcode": "ASSERT_SHA256",
            "args": {
                "path": file_info["path"],
                "sha256": file_info["sha256"]
            },
            "axioms": ["hash_integrity"],
            "oracle_reply": {
                "status": "sat",
                "witness": {"verified_hash": file_info["sha256"]}
            },
            "mu_bits": 256.0,  # Cost of SHA-256 verification
            "post_state_sha256": "computed_by_verifier"
        }
        steps.append(assert_step)
        
        current_state = "computed_by_verifier"
    
    return {
        "version": "TRS-0",
        "steps": steps,
        "global_digest": global_digest,
        "sig_scheme": "none",
        "signature": ""
    }


def main():
    parser = argparse.ArgumentParser(
        description="Create Thiele receipts for cryptographically verifiable software distribution",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Create receipt for a single file
  %(prog)s script.py
  
  # Create receipt for multiple files
  %(prog)s main.py utils.py config.json
  
  # Specify output path
  %(prog)s script.py --output my_receipt.json
  
  # Create TRS-0 receipt with detailed steps
  %(prog)s script.py --steps

After creating a receipt, verify it with:
  python3 verifier/replay.py <receipt.json>

Learn more: docs/RECEIPT_GUIDE.md
"""
    )
    
    parser.add_argument(
        'files',
        nargs='+',
        help='Files to include in the receipt'
    )
    
    parser.add_argument(
        '-o', '--output',
        help='Output path for the receipt (default: auto-generated)'
    )
    
    parser.add_argument(
        '--steps',
        action='store_true',
        help='Create TRS-0 receipt with detailed steps (default: TRS-1.0 simplified)'
    )
    
    parser.add_argument(
        '--verify',
        action='store_true',
        help='Verify the receipt after creation (requires verifier/replay.py)'
    )
    
    args = parser.parse_args()
    
    # Create receipt
    print(f"Creating Thiele receipt for {len(args.files)} file(s)...\n")
    receipt = create_receipt(
        args.files,
        output_path=args.output,
        include_steps=args.steps
    )
    
    # Optionally verify
    if args.verify:
        import subprocess
        output_path = args.output or (
            f"{Path(args.files[0]).stem}_receipt.json" if len(args.files) == 1 else "receipt.json"
        )
        print(f"\nVerifying receipt...")
        try:
            subprocess.run(
                ["python3", "verifier/replay.py", output_path],
                check=True
            )
            print("✓ Verification successful!")
        except subprocess.CalledProcessError:
            print("✗ Verification failed!", file=sys.stderr)
            sys.exit(1)
        except FileNotFoundError:
            print("Warning: verifier/replay.py not found, skipping verification", file=sys.stderr)


if __name__ == "__main__":
    main()
