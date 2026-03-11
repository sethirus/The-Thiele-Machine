import json
from pathlib import Path
from typing import Dict, Any
from .receipt_protocol import _sha256_hex

class RandomnessVerificationError(Exception):
    pass


def verify_randomness(run_dir: Path, trust_manifest_path: Path) -> Dict[str, Any]:
    receipt_path = run_dir / "randomness.receipt.json"
    if not receipt_path.exists():
        raise RandomnessVerificationError("receipt missing")

    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    file_paths = [f["path"] for f in receipt.get("files", [])]
    if "randomness.bin" not in file_paths:
        raise RandomnessVerificationError("Receipt missing required randomness.bin")

    # Hash checks
    for f in receipt.get("files", []):
        p = run_dir / f["path"]
        if not p.exists():
            raise RandomnessVerificationError("Receipt references missing file")
        cur_hash = _sha256_hex(p)
        if cur_hash != f.get("sha256"):
            raise RandomnessVerificationError("Hash mismatch")

    # Check disclosure bits in nonlocality.json
    nonlocality = json.loads((run_dir / "nonlocality.json").read_text(encoding="utf-8"))
    disclosure_bits = nonlocality.get("disclosure_bits")
    if disclosure_bits is None or disclosure_bits < 8:
        raise RandomnessVerificationError("Insufficient disclosure_bits")

    return {"ok": True}
