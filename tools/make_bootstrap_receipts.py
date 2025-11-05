#!/usr/bin/env python3
"""
Bootstrap Receipt Generator

Reads kernel template and generates receipts that can reconstruct it.
This tool is used during development but not distributed with the final system.
"""
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Dict, List


def sha256_hex(data: bytes) -> str:
    """Compute SHA256 hex digest."""
    return hashlib.sha256(data).hexdigest()


def canonical_json(obj: Any) -> bytes:
    """Serialize to canonical JSON bytes."""
    return json.dumps(
        obj,
        ensure_ascii=False,
        sort_keys=True,
        separators=(',', ':'),
    ).encode('utf-8')


def compute_state_hash(virtual_fs: Dict[str, bytes], exec_flags: Dict[str, bool]) -> str:
    """Compute state hash from virtual filesystem."""
    parts = []
    for path in sorted(virtual_fs.keys()):
        parts.append(path.encode('utf-8'))
        parts.append(sha256_hex(virtual_fs[path]).encode('utf-8'))
        parts.append(b'1' if exec_flags.get(path, False) else b'0')
    return sha256_hex(b''.join(parts))


def generate_bootstrap_receipts(
    template_path: str,
    output_path: str,
    chunk_size: int = 2048
) -> str:
    """
    Generate bootstrap receipts from kernel template.
    
    Args:
        template_path: Path to kernel_template/thiele_min.py
        output_path: Path to output receipt JSON
        chunk_size: Size of each EMIT_BYTES chunk
    
    Returns:
        SHA256 hash of the generated kernel
    """
    # Read kernel template
    template_file = Path(template_path)
    if not template_file.exists():
        raise FileNotFoundError(f"Template not found: {template_path}")
    
    kernel_bytes = template_file.read_bytes()
    kernel_sha = sha256_hex(kernel_bytes)
    
    print(f"Generating receipts for kernel ({len(kernel_bytes)} bytes)")
    print(f"Kernel SHA256: {kernel_sha}")
    
    # Initialize virtual state
    virtual_fs: Dict[str, bytes] = {}
    exec_flags: Dict[str, bool] = {}
    target_path = "thiele_min.py"
    
    # Generate steps
    steps: List[Dict[str, Any]] = []
    offset = 0
    step_num = 0
    
    # Split into chunks and emit
    while offset < len(kernel_bytes):
        # Compute pre-state
        pre_state = compute_state_hash(virtual_fs, exec_flags)
        
        # Get chunk
        chunk = kernel_bytes[offset:offset + chunk_size]
        chunk_hex = chunk.hex()
        
        # Create step
        step = {
            "step": step_num,
            "pre_state_sha256": pre_state,
            "opcode": "EMIT_BYTES",
            "args": {
                "path": target_path,
                "offset": offset,
                "bytes_hex": chunk_hex
            },
            "axioms": ["offset_within_file", "no_overlap", "monotone_offset"],
            "oracle_reply": {
                "status": "sat",
                "witness": {"offset": offset, "length": len(chunk)}
            },
            "mu_bits": float(len(chunk) * 8),  # 8 bits per byte
            "post_state_sha256": ""  # Will compute below
        }
        
        # Update virtual state
        if target_path not in virtual_fs:
            virtual_fs[target_path] = b''
        virtual_fs[target_path] = virtual_fs[target_path][:offset] + chunk + virtual_fs[target_path][offset:]
        
        # Compute post-state
        post_state = compute_state_hash(virtual_fs, exec_flags)
        step["post_state_sha256"] = post_state
        
        steps.append(step)
        
        offset += len(chunk)
        step_num += 1
        
        if step_num % 10 == 0 or offset >= len(kernel_bytes):
            print(f"  Step {step_num}: emitted {offset}/{len(kernel_bytes)} bytes")
    
    # Add MAKE_EXEC step
    pre_state = compute_state_hash(virtual_fs, exec_flags)
    exec_step = {
        "step": step_num,
        "pre_state_sha256": pre_state,
        "opcode": "MAKE_EXEC",
        "args": {
            "path": target_path
        },
        "axioms": ["exec_permission"],
        "oracle_reply": {
            "status": "sat",
            "witness": None
        },
        "mu_bits": 1.0,
        "post_state_sha256": ""
    }
    
    exec_flags[target_path] = True
    post_state = compute_state_hash(virtual_fs, exec_flags)
    exec_step["post_state_sha256"] = post_state
    steps.append(exec_step)
    step_num += 1
    
    # Add ASSERT_SHA256 step
    pre_state = compute_state_hash(virtual_fs, exec_flags)
    assert_step = {
        "step": step_num,
        "pre_state_sha256": pre_state,
        "opcode": "ASSERT_SHA256",
        "args": {
            "path": target_path,
            "sha256": kernel_sha
        },
        "axioms": ["hash_integrity", "sha_invariant"],
        "oracle_reply": {
            "status": "sat",
            "witness": {"verified_hash": kernel_sha}
        },
        "mu_bits": 256.0,  # Hash computation cost
        "post_state_sha256": pre_state  # No state change
    }
    steps.append(assert_step)
    
    print(f"Generated {len(steps)} steps")
    
    # Compute global digest
    step_hashes = []
    for step in steps:
        canonical_bytes = canonical_json(step)
        step_hash = hashlib.sha256(canonical_bytes).digest()
        step_hashes.append(step_hash)
    
    global_digest = hashlib.sha256(b''.join(step_hashes)).hexdigest()
    
    # Create receipt
    receipt = {
        "version": "TRS-0",
        "steps": steps,
        "global_digest": global_digest,
        "sig_scheme": "none",
        "signature": ""
    }
    
    # Write receipt
    output_file = Path(output_path)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(receipt, f, indent=2, sort_keys=True)
    
    print(f"Receipt written to: {output_path}")
    print(f"Global digest: {global_digest}")
    
    return kernel_sha


def main():
    """CLI entry point."""
    if len(sys.argv) < 2:
        print("Usage: python3 tools/make_bootstrap_receipts.py <template_path> [output_path] [chunk_size]")
        print("Example: python3 tools/make_bootstrap_receipts.py kernel_template/thiele_min.py bootstrap_receipts/050_kernel_emit.json")
        sys.exit(1)
    
    template_path = sys.argv[1]
    output_path = sys.argv[2] if len(sys.argv) > 2 else "bootstrap_receipts/050_kernel_emit.json"
    chunk_size = int(sys.argv[3]) if len(sys.argv) > 3 else 2048
    
    try:
        kernel_sha = generate_bootstrap_receipts(template_path, output_path, chunk_size)
        
        # Write expected hash
        expected_hash_file = Path("tests/expected_kernel_sha256.txt")
        expected_hash_file.write_text(kernel_sha + "\n")
        print(f"Expected hash written to: {expected_hash_file}")
        
        print("\n=== Bootstrap receipts generated successfully! ===")
        return 0
        
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
