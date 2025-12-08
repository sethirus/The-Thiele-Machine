#!/usr/bin/env python3
"""
Tamper Evidence Demonstration

Shows how receipt verification detects any modification to receipts.
This script mutates a single byte in a receipt and attempts verification.
"""
import json
import shutil
import sys
import tempfile
from pathlib import Path
import subprocess


def tamper_demo():
    """Demonstrate tamper detection."""
    print("=== Thiele Receipt Tamper Evidence Demo ===\n")
    
    # Copy receipt to temp location
    temp_dir = tempfile.mkdtemp()
    receipt_path = Path(temp_dir) / "050_kernel_emit.json"
    shutil.copy("receipts/bootstrap_receipts/050_kernel_emit.json", receipt_path)
    
    print(f"1. Original receipt copied to: {receipt_path}")
    
    # Load and show original
    with open(receipt_path, 'r') as f:
        receipt = json.load(f)
    
    original_digest = receipt.get('global_digest', '')
    print(f"   Original global_digest: {original_digest}\n")
    
    # Mutate one byte in a step's hex data
    print("2. Tampering with receipt (changing 1 byte in step 0)...")
    step0_hex = receipt['steps'][0]['args']['bytes_hex']
    original_hex = step0_hex
    
    # Change first byte
    if step0_hex:
        mutated_hex = 'ff' + step0_hex[2:]
        receipt['steps'][0]['args']['bytes_hex'] = mutated_hex
        print(f"   Before: {step0_hex[:20]}...")
        print(f"   After:  {mutated_hex[:20]}...\n")
    
    # Write tampered receipt
    with open(receipt_path, 'w') as f:
        json.dump(receipt, f, indent=2)
    
    print("3. Attempting verification with tampered receipt...\n")
    
    # Try to verify
    result = subprocess.run(
        ['python3', 'verifier/replay.py', '--dry-run', temp_dir],
        capture_output=True,
        text=True
    )
    
    print("--- Verifier Output ---")
    if result.stdout:
        print(result.stdout)
    if result.stderr:
        print("STDERR:", result.stderr)
    print("--- End Output ---\n")
    
    # Clean up
    shutil.rmtree(temp_dir)
    
    if result.returncode != 0:
        print("✓ SUCCESS: Tampered receipt was rejected!")
        print(f"  Exit code: {result.returncode}")
        print("\nKey observation:")
        print("  - The verifier detected the tampering immediately")
        print("  - Hash mismatches are reported with exact step and expected/actual values")
        print("  - Cryptographic integrity is maintained")
        return 0
    else:
        print("✗ FAILURE: Tampered receipt was NOT rejected!")
        print("  This should never happen - integrity check failed")
        return 1


def main():
    try:
        return tamper_demo()
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
