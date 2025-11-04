#!/usr/bin/env python3
"""
Receipt Fuzzer for Thiele Receipts.

Fuzzes valid receipts by randomly corrupting them to ensure:
1. Verifier never crashes
2. Verifier properly rejects malformed receipts
3. No false positives (corrupted receipts are never accepted)
"""

import json
import random
import copy
import sys
import tempfile
import subprocess
from pathlib import Path
from typing import Any, Dict, List

PROJECT_ROOT = Path(__file__).parent.parent


def load_receipt(receipt_path: Path) -> Dict[str, Any]:
    """Load a receipt JSON file."""
    with open(receipt_path) as f:
        return json.load(f)


def save_receipt(receipt: Dict[str, Any], path: Path):
    """Save a receipt JSON file."""
    with open(path, 'w') as f:
        json.dump(receipt, f, indent=2)


def verify_receipt(receipt_path: Path) -> tuple:
    """
    Verify a receipt and return (success, stdout, stderr).
    
    Returns:
        (bool, str, str): (verification_passed, stdout, stderr)
    """
    cmd = [
        sys.executable,
        str(PROJECT_ROOT / "tools" / "verify_trs10.py"),
        str(receipt_path)
    ]
    
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=10,
            cwd=PROJECT_ROOT
        )
        return (result.returncode == 0, result.stdout, result.stderr)
    except subprocess.TimeoutExpired:
        return (False, "", "TIMEOUT: Verifier hung")
    except Exception as e:
        return (False, "", f"EXCEPTION: {str(e)}")


# ==================== Fuzzing Strategies ====================

def fuzz_delete_field(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Delete a random field from the receipt."""
    mutated = copy.deepcopy(receipt)
    
    # Get all deletable keys (keep at least one key)
    if len(mutated) > 1:
        key = random.choice(list(mutated.keys()))
        del mutated[key]
    
    return mutated


def fuzz_change_type(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Change the type of a random field."""
    mutated = copy.deepcopy(receipt)
    
    key = random.choice(list(mutated.keys()))
    
    # Change to a different type
    type_choices = [
        "string",
        42,
        [],
        {},
        None,
        True
    ]
    mutated[key] = random.choice(type_choices)
    
    return mutated


def fuzz_truncate_string(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Truncate a random string field."""
    mutated = copy.deepcopy(receipt)
    
    # Find string fields
    string_fields = []
    for key, value in mutated.items():
        if isinstance(value, str) and len(value) > 1:
            string_fields.append(key)
    
    if string_fields:
        key = random.choice(string_fields)
        value = mutated[key]
        # Truncate to random length
        new_len = random.randint(0, len(value) - 1)
        mutated[key] = value[:new_len]
    
    return mutated


def fuzz_corrupt_digest(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Corrupt a digest field (flip bits)."""
    mutated = copy.deepcopy(receipt)
    
    if "global_digest" in mutated and mutated["global_digest"]:
        digest = mutated["global_digest"]
        # Flip a random character
        pos = random.randint(0, len(digest) - 1)
        chars = '0123456789abcdef'
        new_char = random.choice([c for c in chars if c != digest[pos]])
        mutated["global_digest"] = digest[:pos] + new_char + digest[pos+1:]
    
    return mutated


def fuzz_corrupt_file_entry(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Corrupt a file entry."""
    mutated = copy.deepcopy(receipt)
    
    if "files" in mutated and isinstance(mutated["files"], list) and mutated["files"]:
        file_entry = random.choice(mutated["files"])
        
        # Choose corruption type
        corruption = random.choice([
            "delete_path",
            "corrupt_hash",
            "wrong_size",
            "add_invalid_field"
        ])
        
        if corruption == "delete_path" and "path" in file_entry:
            del file_entry["path"]
        elif corruption == "corrupt_hash" and "sha256" in file_entry:
            h = file_entry["sha256"]
            pos = random.randint(0, len(h) - 1)
            file_entry["sha256"] = h[:pos] + ('x' if h[pos] != 'x' else 'y') + h[pos+1:]
        elif corruption == "wrong_size" and "size" in file_entry:
            file_entry["size"] = -1 if file_entry["size"] >= 0 else 99999999
        elif corruption == "add_invalid_field":
            file_entry["__invalid__"] = "should_not_exist"
    
    return mutated


def fuzz_add_invalid_field(receipt: Dict[str, Any]) -> Dict[str, Any]:
    """Add an invalid top-level field."""
    mutated = copy.deepcopy(receipt)
    mutated["__fuzzer_invalid_field__"] = random.choice([
        "invalid_data",
        12345,
        ["list", "of", "nonsense"],
        {"nested": "invalid"}
    ])
    return mutated


def fuzz_malformed_json(receipt_path: Path) -> Path:
    """Create malformed JSON by truncating the file."""
    with open(receipt_path) as f:
        content = f.read()
    
    # Truncate JSON
    truncated = content[:len(content) // 2]
    
    malformed_path = receipt_path.parent / "malformed.json"
    malformed_path.write_text(truncated)
    
    return malformed_path


def fuzz_empty_json(receipt_path: Path) -> Path:
    """Create empty JSON."""
    empty_path = receipt_path.parent / "empty.json"
    empty_path.write_text("")
    return empty_path


def fuzz_invalid_json(receipt_path: Path) -> Path:
    """Create invalid JSON."""
    invalid_path = receipt_path.parent / "invalid.json"
    invalid_path.write_text("{ this is not valid json }")
    return invalid_path


# ==================== Fuzzing Engine ====================

FUZZING_STRATEGIES = [
    ("delete_field", fuzz_delete_field),
    ("change_type", fuzz_change_type),
    ("truncate_string", fuzz_truncate_string),
    ("corrupt_digest", fuzz_corrupt_digest),
    ("corrupt_file_entry", fuzz_corrupt_file_entry),
    ("add_invalid_field", fuzz_add_invalid_field),
]


def fuzz_receipt(valid_receipt_path: Path, num_iterations: int = 100) -> Dict[str, int]:
    """
    Fuzz a valid receipt and track results.
    
    Returns:
        dict: Statistics about fuzzing results
    """
    results = {
        "total": 0,
        "rejected": 0,  # Properly rejected (expected)
        "accepted": 0,  # Incorrectly accepted (BUG!)
        "crashed": 0,   # Verifier crashed (BUG!)
        "timeout": 0    # Verifier hung (BUG!)
    }
    
    print(f"Fuzzing receipt: {valid_receipt_path}")
    print(f"Running {num_iterations} fuzzing iterations...")
    print()
    
    workspace = valid_receipt_path.parent
    
    # Verify original is valid
    success, stdout, stderr = verify_receipt(valid_receipt_path)
    if not success:
        print(f"ERROR: Original receipt is invalid!")
        print(f"STDERR: {stderr}")
        return results
    
    print(f"✓ Original receipt verifies successfully")
    print()
    
    for i in range(num_iterations):
        results["total"] += 1
        
        # Load fresh copy
        receipt = load_receipt(valid_receipt_path)
        
        # Choose fuzzing strategy
        strategy_name, strategy_func = random.choice(FUZZING_STRATEGIES)
        
        # Apply fuzzing
        fuzzed_receipt = strategy_func(receipt)
        
        # Save fuzzed receipt
        fuzzed_path = workspace / f"fuzzed_{i}.json"
        save_receipt(fuzzed_receipt, fuzzed_path)
        
        # Verify fuzzed receipt
        success, stdout, stderr = verify_receipt(fuzzed_path)
        
        if success:
            # This is a BUG! Fuzzed receipt should not verify
            results["accepted"] += 1
            print(f"[ITER {i}] BUG: Fuzzed receipt ACCEPTED (strategy: {strategy_name})")
            print(f"  Fuzzed receipt: {fuzzed_path}")
            print(f"  STDOUT: {stdout}")
            print()
        elif "TIMEOUT" in stderr:
            results["timeout"] += 1
            print(f"[ITER {i}] BUG: Verifier TIMEOUT (strategy: {strategy_name})")
            print()
        elif "EXCEPTION" in stderr or "Traceback" in stderr:
            results["crashed"] += 1
            print(f"[ITER {i}] BUG: Verifier CRASHED (strategy: {strategy_name})")
            print(f"  STDERR: {stderr}")
            print()
        else:
            # Properly rejected
            results["rejected"] += 1
        
        # Clean up
        fuzzed_path.unlink()
    
    # Test malformed JSON
    print("Testing malformed JSON...")
    
    for name, func in [
        ("malformed", fuzz_malformed_json),
        ("empty", fuzz_empty_json),
        ("invalid", fuzz_invalid_json)
    ]:
        results["total"] += 1
        path = func(valid_receipt_path)
        success, stdout, stderr = verify_receipt(path)
        
        if success:
            results["accepted"] += 1
            print(f"BUG: {name} JSON ACCEPTED")
        elif "TIMEOUT" in stderr:
            results["timeout"] += 1
            print(f"BUG: {name} JSON caused TIMEOUT")
        elif "EXCEPTION" in stderr:
            results["crashed"] += 1
            print(f"BUG: {name} JSON caused CRASH")
        else:
            results["rejected"] += 1
        
        path.unlink()
    
    return results


def main():
    if len(sys.argv) < 2:
        print("Usage: fuzz_receipts.py <valid_receipt.json> [num_iterations]")
        print()
        print("Fuzzes a valid receipt to test verifier robustness.")
        sys.exit(1)
    
    receipt_path = Path(sys.argv[1])
    num_iterations = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    
    if not receipt_path.exists():
        print(f"Error: Receipt not found: {receipt_path}")
        sys.exit(1)
    
    # Run fuzzing
    results = fuzz_receipt(receipt_path, num_iterations)
    
    # Print results
    print()
    print("=" * 70)
    print("FUZZING RESULTS")
    print("=" * 70)
    print(f"Total iterations: {results['total']}")
    print(f"Properly rejected: {results['rejected']}")
    print(f"Incorrectly accepted (BUG): {results['accepted']}")
    print(f"Verifier crashed (BUG): {results['crashed']}")
    print(f"Verifier timeout (BUG): {results['timeout']}")
    print()
    
    bugs_found = results['accepted'] + results['crashed'] + results['timeout']
    
    if bugs_found == 0:
        print("✓ No bugs found! Verifier is robust.")
        sys.exit(0)
    else:
        print(f"✗ Found {bugs_found} bug(s)!")
        sys.exit(1)


if __name__ == "__main__":
    main()
