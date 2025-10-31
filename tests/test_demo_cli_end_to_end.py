import json
import subprocess
import sys
from pathlib import Path


def test_demo_cli_end_to_end(tmp_path: Path):
    """Run the demo CLI end-to-end: create-demo, then canonicalize/sign/normalize and verify with the generated public key."""
    repo_root = Path(__file__).resolve().parents[1]
    outdir = tmp_path / "demo"
    outdir.mkdir()

    # Step 1: create demo
    res = subprocess.run([sys.executable, str(repo_root / "scripts" / "demo_isomorphism_cli.py"), "--create-demo", "--outdir", str(outdir)], check=True)
    # Find created receipt
    receipt = outdir / "demo_receipt.json"
    assert receipt.exists(), "demo_receipt.json should have been created"

    # Step 2: canonicalize + sign + normalize + verify-with-public-key
    # This should exit 0 on success
    cmd = [
        sys.executable,
        str(repo_root / "scripts" / "demo_isomorphism_cli.py"),
        "--receipt",
        str(receipt),
        "--show-cert-store",
        "--sign",
        "--normalize",
        "--verify-with-public-key",
        "kernel_public.key",
    ]
    subprocess.run(cmd, check=True)
