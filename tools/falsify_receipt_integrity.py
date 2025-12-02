#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Falsify Receipt Integrity

Verifies Thiele nonlocal box receipts by:
- Recomputing hash from stored traces
- Verifying μ-cost accounting
- Checking partition trace consistency

Exits with non-zero status if verification fails.

Usage:
    python tools/falsify_receipt_integrity.py --receipt artifacts/nl_search/receipt.json
"""

import argparse
import sys
from pathlib import Path

# Add repository root to path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from tools.thiele_nonlocal_receipt import load_receipt


def main():
    parser = argparse.ArgumentParser(description="Falsify Thiele nonlocal box receipt integrity")
    parser.add_argument("--receipt", required=True, help="Path to receipt JSON file")
    parser.add_argument("--verbose", action="store_true", help="Verbose output")
    args = parser.parse_args()
    
    receipt_path = Path(args.receipt)
    if not receipt_path.exists():
        print(f"ERROR: Receipt file not found: {receipt_path}")
        sys.exit(1)
    
    try:
        receipt = load_receipt(str(receipt_path))
    except Exception as e:
        print(f"ERROR: Failed to load receipt: {e}")
        sys.exit(1)
    
    if args.verbose:
        print(f"Verifying receipt: {receipt_path}")
        print(f"  Shape: {receipt.shape}")
        print(f"  Seed: {receipt.seed}")
        print(f"  Bell value: {receipt.bell_value}")
        print(f"  VM μ-discovery: {receipt.vm_mu_discovery}")
        print(f"  VM μ-execution: {receipt.vm_mu_execution}")
        print(f"  Partition trace entries: {len(receipt.partition_trace)}")
    
    # Verify integrity
    is_valid, message = receipt.verify_integrity()
    
    if is_valid:
        print(f"✓ Receipt integrity VERIFIED: {message}")
        if args.verbose:
            print(f"  Trace hash: {receipt.vm_canonical_hash}")
        sys.exit(0)
    else:
        print(f"✗ Receipt integrity FAILED: {message}")
        sys.exit(1)


if __name__ == "__main__":
    main()
