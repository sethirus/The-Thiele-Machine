import json
import hashlib
from pathlib import Path
from typing import Dict, Any
from .receipt_protocol import _sha256_hex, write_trust_manifest

class CausalVerificationError(Exception):
    pass


def verify_causal(run_dir: Path, trust_manifest_path: Path) -> Dict[str, Any]:
    # Read receipt
    receipt_path = run_dir / "causal.receipt.json"
    if not receipt_path.exists():
        raise CausalVerificationError("receipt missing")

    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    # Verify that required files are present in receipt
    file_paths = [f["path"] for f in receipt.get("files", [])]
    if "assumptions.json" not in file_paths:
        raise CausalVerificationError("Receipt missing required assumptions")

    # Check hashes match current files (detect tampering)
    for f in receipt.get("files", []):
        p = run_dir / f["path"]
        if not p.exists():
            raise CausalVerificationError("Receipt references missing file")
        cur_hash = _sha256_hex(p)
        if cur_hash != f.get("sha256"):
            raise CausalVerificationError("Hash mismatch")

    # Check disclosure bits
    assumptions_path = run_dir / "assumptions.json"
    assumptions = json.loads(assumptions_path.read_text(encoding="utf-8"))
    disclosure_bits = assumptions.get("disclosure_bits")
    if disclosure_bits is None or disclosure_bits < 8:
        raise CausalVerificationError("Insufficient disclosure_bits")

    return {"ok": True}
