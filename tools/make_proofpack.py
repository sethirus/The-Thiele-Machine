#!/usr/bin/env python3
"""
Proof Pack Builder

Creates a self-contained, reproducible proof pack containing only
the minimal files needed to verify and reconstruct the kernel.
"""
import hashlib
import json
import os
import subprocess
import sys
import tarfile
from pathlib import Path


def count_verifier_loc(verifier_path: str) -> int:
    """Count non-blank, non-comment lines in verifier."""
    with open(verifier_path, 'r') as f:
        lines = f.readlines()
    return sum(1 for line in lines if line.strip() and not line.strip().startswith('#'))


def sha256_hex(data: bytes) -> str:
    """Compute SHA256 hex digest."""
    return hashlib.sha256(data).hexdigest()


def make_proofpack(output_dir: str = "dist") -> str:
    """
    Create a proof pack tarball.
    
    Returns:
        Path to created tarball
    """
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    # Files to include in proof pack
    files_to_pack = [
        "verifier/replay.py",
        "bootstrap_receipts/050_kernel_emit.json",
        "docs/receipt_schema.md",
        "roadmap-enhancements/supply-chain/attestations/REPRODUCIBILITY.md",
        "checksums/receipts_sha256.txt",
        "tests/expected_kernel_sha256.txt",
    ]
    
    # Verify all files exist
    for file_path in files_to_pack:
        if not Path(file_path).exists():
            print(f"ERROR: Required file not found: {file_path}", file=sys.stderr)
            return None
    
    # Read kernel hash
    with open("tests/expected_kernel_sha256.txt", 'r') as f:
        kernel_sha256 = f.read().strip()
    
    # Compute global digest from receipts
    with open("bootstrap_receipts/050_kernel_emit.json", 'r') as f:
        receipt = json.load(f)
    
    steps = receipt.get('steps', [])
    step_hashes = []
    for step in steps:
        canonical_bytes = json.dumps(
            step,
            ensure_ascii=False,
            sort_keys=True,
            separators=(',', ':'),
        ).encode('utf-8')
        step_hash = hashlib.sha256(canonical_bytes).digest()
        step_hashes.append(step_hash)
    
    global_digest = hashlib.sha256(b''.join(step_hashes)).hexdigest()
    
    # Count verifier LoC
    verifier_loc = count_verifier_loc("verifier/replay.py")
    
    # Create PROOF.txt
    proof_txt = f"""THIELE SELF-HOSTING KERNEL PROOF PACK
========================================

Kernel SHA256:       {kernel_sha256}
Global Digest:       {global_digest}
Verifier TCB (LoC):  {verifier_loc}

This proof pack contains the minimal files needed to:
1. Verify the cryptographic integrity of the kernel construction
2. Reconstruct the kernel from receipts
3. Validate the self-hosting system

To use:
  1. Extract this tarball
  2. Run: python3 verifier/replay.py bootstrap_receipts
  3. Verify: sha256sum thiele_min.py

Expected kernel hash: {kernel_sha256}

For full instructions, see roadmap-enhancements/supply-chain/attestations/REPRODUCIBILITY.md
"""
    
    # Write PROOF.txt
    proof_path = output_path / "PROOF.txt"
    proof_path.write_text(proof_txt)
    
    # Create tarball
    tarball_path = output_path / "proofpack.tar.zst"
    temp_tarball = output_path / "proofpack.tar"
    
    print(f"Creating proof pack...")
    print(f"  Kernel SHA256: {kernel_sha256}")
    print(f"  Global Digest: {global_digest}")
    print(f"  Verifier LoC:  {verifier_loc}")
    
    # Create tar file
    with tarfile.open(temp_tarball, 'w') as tar:
        # Add PROOF.txt
        tar.add(proof_path, arcname="PROOF.txt")
        
        # Add all required files
        for file_path in files_to_pack:
            tar.add(file_path, arcname=file_path)
            print(f"  Added: {file_path}")
    
    # Compress with zstd if available, otherwise gzip
    try:
        subprocess.run(['zstd', '--version'], capture_output=True, check=True)
        print("\nCompressing with zstd...")
        subprocess.run(['zstd', '-f', str(temp_tarball), '-o', str(tarball_path)], check=True)
        temp_tarball.unlink()
        final_path = tarball_path
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("\nzstd not available, using gzip compression...")
        tarball_path = output_path / "proofpack.tar.gz"
        subprocess.run(['gzip', '-f', str(temp_tarball)], check=True)
        (output_path / "proofpack.tar.gz").rename(tarball_path)
        final_path = tarball_path
    
    # Clean up temporary PROOF.txt
    proof_path.unlink()
    
    size_mb = final_path.stat().st_size / 1024 / 1024
    print(f"\nProof pack created: {final_path}")
    print(f"Size: {size_mb:.2f} MB")
    
    return str(final_path)


def main():
    """CLI entry point."""
    output_dir = sys.argv[1] if len(sys.argv) > 1 else "dist"
    
    proofpack_path = make_proofpack(output_dir)
    
    if proofpack_path:
        print(f"\n✓ Success! Proof pack ready at: {proofpack_path}")
        print(f"\nTo verify:")
        print(f"  tar -xf {proofpack_path}")
        print(f"  python3 verifier/replay.py bootstrap_receipts")
        print(f"  sha256sum thiele_min.py")
        return 0
    else:
        return 1


if __name__ == '__main__':
    sys.exit(main())
