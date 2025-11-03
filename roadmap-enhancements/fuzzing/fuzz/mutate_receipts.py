#!/usr/bin/env python3
"""
Receipt Fuzzer

Mutates valid receipts to test robustness of verifiers.
All mutations should be detected and rejected.
"""

import argparse
import json
import random
import sys
from pathlib import Path
from typing import List, Callable, Dict, Any


def flip_random_bit(data: bytes) -> bytes:
    """Flip a single random bit."""
    pos = random.randint(0, len(data) - 1)
    bit = random.randint(0, 7)
    
    byte_arr = bytearray(data)
    byte_arr[pos] ^= (1 << bit)
    return bytes(byte_arr)


def flip_random_nibble(data: bytes) -> bytes:
    """Flip a single random hex nibble."""
    pos = random.randint(0, len(data) - 1)
    
    byte_arr = bytearray(data)
    byte_arr[pos] ^= random.randint(1, 15)
    return bytes(byte_arr)


def reorder_keys(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Randomly reorder JSON keys (breaks canonical form)."""
    keys = list(receipt.keys())
    random.shuffle(keys)
    return {k: receipt[k] for k in keys}


def modify_version(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Change version string."""
    mutated = receipt.copy()
    mutated['version'] = 'TRS-INVALID'
    return mutated


def corrupt_digest(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Corrupt global digest."""
    mutated = receipt.copy()
    if 'global_digest' in mutated:
        digest = mutated['global_digest']
        # Flip one hex digit
        pos = random.randint(0, len(digest) - 1)
        chars = '0123456789abcdef'
        new_char = random.choice(chars.replace(digest[pos], ''))
        mutated['global_digest'] = digest[:pos] + new_char + digest[pos+1:]
    return mutated


def corrupt_file_hash(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Corrupt a file's SHA256."""
    mutated = receipt.copy()
    if 'files' in mutated and len(mutated['files']) > 0:
        file_idx = random.randint(0, len(mutated['files']) - 1)
        file_entry = mutated['files'][file_idx].copy()
        
        if 'content_sha256' in file_entry:
            sha = file_entry['content_sha256']
            pos = random.randint(0, len(sha) - 1)
            chars = '0123456789abcdef'
            new_char = random.choice(chars.replace(sha[pos], ''))
            file_entry['content_sha256'] = sha[:pos] + new_char + sha[pos+1:]
        
        mutated['files'][file_idx] = file_entry
    return mutated


MUTATIONS: List[Callable[[Dict[str, Any]], Dict[str, Any]]] = [
    reorder_keys,
    modify_version,
    corrupt_digest,
    corrupt_file_hash,
]


def mutate_receipt(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Apply a random mutation to a receipt."""
    mutation = random.choice(MUTATIONS)
    return mutation(receipt)


def main():
    parser = argparse.ArgumentParser(description='Fuzz receipts by mutation')
    parser.add_argument('receipt', type=Path, help='Input receipt to mutate')
    parser.add_argument('--count', type=int, default=100, help='Number of mutations')
    parser.add_argument('--out-dir', type=Path, default=Path('fuzz_output'), help='Output directory')
    
    args = parser.parse_args()
    
    # Load receipt
    with open(args.receipt, 'r') as f:
        receipt = json.load(f)
    
    # Create output directory
    args.out_dir.mkdir(parents=True, exist_ok=True)
    
    print(f"Fuzzing {args.receipt} ({args.count} mutations)")
    
    # Generate mutations
    for i in range(args.count):
        mutated = mutate_receipt(receipt)
        
        out_file = args.out_dir / f"mutated_{i:04d}.json"
        with open(out_file, 'w') as f:
            json.dump(mutated, f, sort_keys=True, separators=(',', ':'))
    
    print(f"✓ Generated {args.count} mutations in {args.out_dir}")
    print("\nTest with:")
    print(f"  for f in {args.out_dir}/*.json; do")
    print(f"    python3 verifier/replay.py $f && echo 'FAIL: $f accepted!' || echo 'PASS: $f rejected'")
    print(f"  done")


if __name__ == '__main__':
    main()
