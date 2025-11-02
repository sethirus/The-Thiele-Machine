"""
ZK Bridge for Thiele Receipts

This module provides Python bindings to the Rust ZK prover/verifier.
It wraps the zk-prove and zk-verify CLI tools for easy integration.
"""

import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, Any, Optional


class ZKBridgeError(Exception):
    """Exception raised for ZK bridge errors."""
    pass


def find_zk_binary(name: str) -> Optional[Path]:
    """Find ZK binary in expected locations."""
    candidates = [
        Path(__file__).parent.parent.parent / "zk" / "host" / "target" / "release" / name,
        Path(__file__).parent.parent.parent / "zk" / "host" / "target" / "debug" / name,
        Path(name),  # System PATH
    ]
    
    for candidate in candidates:
        if candidate.exists() and candidate.is_file():
            return candidate
    
    # Try which/where on system PATH
    try:
        result = subprocess.run(
            ["which" if sys.platform != "win32" else "where", name],
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode == 0 and result.stdout.strip():
            return Path(result.stdout.strip().split('\n')[0])
    except Exception:
        pass
    
    return None


def prove_receipt(receipt_path: str, output_path: str) -> Dict[str, Any]:
    """
    Generate a ZK proof for a receipt.
    
    Args:
        receipt_path: Path to receipt.json
        output_path: Path to write zkproof.json
    
    Returns:
        Dictionary containing proof metadata
    
    Raises:
        ZKBridgeError: If proof generation fails
    """
    zk_prove = find_zk_binary("zk-prove")
    if not zk_prove:
        raise ZKBridgeError(
            "zk-prove binary not found. Build it with: cd zk/host && cargo build --release"
        )
    
    try:
        result = subprocess.run(
            [str(zk_prove), "--receipt", receipt_path, "--out", output_path],
            capture_output=True,
            text=True,
            check=True,
        )
        
        # Parse output for metadata
        output_file = Path(output_path)
        if output_file.exists():
            with open(output_file, 'r') as f:
                proof_data = json.load(f)
            return {
                "success": True,
                "output": output_path,
                "manifest_sha256": proof_data.get("manifest_sha256"),
                "merkle_root": proof_data.get("merkle_root"),
                "file_count": len(proof_data.get("files", [])),
                "stdout": result.stdout,
            }
        else:
            raise ZKBridgeError(f"Output file not created: {output_path}")
    
    except subprocess.CalledProcessError as e:
        raise ZKBridgeError(f"Proof generation failed: {e.stderr}")


def verify_proof(zkproof_path: str) -> Dict[str, Any]:
    """
    Verify a ZK proof.
    
    Args:
        zkproof_path: Path to zkproof.json
    
    Returns:
        Dictionary containing verification result
    
    Raises:
        ZKBridgeError: If verification fails
    """
    zk_verify = find_zk_binary("zk-verify")
    if not zk_verify:
        raise ZKBridgeError(
            "zk-verify binary not found. Build it with: cd zk/host && cargo build --release"
        )
    
    try:
        result = subprocess.run(
            [str(zk_verify), zkproof_path],
            capture_output=True,
            text=True,
            check=True,
        )
        
        return {
            "success": True,
            "verified": "verification PASSED" in result.stdout,
            "stdout": result.stdout,
        }
    
    except subprocess.CalledProcessError as e:
        return {
            "success": False,
            "verified": False,
            "error": e.stderr,
        }


def main():
    """CLI entry point for ZK bridge."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Thiele ZK Proof Bridge")
    subparsers = parser.add_subparsers(dest="command", help="Command to run")
    
    # Prove subcommand
    prove_parser = subparsers.add_parser("prove", help="Generate ZK proof")
    prove_parser.add_argument("receipt", help="Path to receipt.json")
    prove_parser.add_argument("--out", default="dist/zkproof.json", help="Output path")
    
    # Verify subcommand
    verify_parser = subparsers.add_parser("verify", help="Verify ZK proof")
    verify_parser.add_argument("zkproof", help="Path to zkproof.json")
    
    args = parser.parse_args()
    
    if args.command == "prove":
        try:
            result = prove_receipt(args.receipt, args.out)
            print(f"✓ Proof generated: {args.out}")
            print(f"  Manifest: {result['manifest_sha256']}")
            print(f"  Merkle root: {result['merkle_root']}")
            print(f"  Files: {result['file_count']}")
        except ZKBridgeError as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)
    
    elif args.command == "verify":
        try:
            result = verify_proof(args.zkproof)
            if result["verified"]:
                print("✅ Verification PASSED")
                sys.exit(0)
            else:
                print("❌ Verification FAILED")
                if "error" in result:
                    print(result["error"], file=sys.stderr)
                sys.exit(1)
        except ZKBridgeError as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)
    
    else:
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    main()
