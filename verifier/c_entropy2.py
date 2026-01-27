import json
from pathlib import Path
from typing import Dict, Any
from .receipt_protocol import _sha256_hex

class EntropyVerificationError(Exception):
    pass


def verify_entropy2(run_dir: Path, trust_manifest_path: Path) -> Dict[str, Any]:
    receipt_path = run_dir / "entropy.receipt.json"
    if not receipt_path.exists():
        raise EntropyVerificationError("receipt missing")

    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    file_paths = [f["path"] for f in receipt.get("files", [])]
    if "coarse_graining.json" not in file_paths:
        raise EntropyVerificationError("Receipt missing required coarse_graining.json")

    # Hash checks
    for f in receipt.get("files", []):
        p = run_dir / f["path"]
        if not p.exists():
            raise EntropyVerificationError("Receipt references missing file")
        cur_hash = _sha256_hex(p)
        if cur_hash != f.get("sha256"):
            raise EntropyVerificationError("Hash mismatch")

    coarse = json.loads((run_dir / "coarse_graining.json").read_text(encoding="utf-8"))
    disclosure_bits = coarse.get("disclosure_bits")
    if disclosure_bits is None or disclosure_bits < 8:
        raise EntropyVerificationError("Insufficient disclosure_bits")

    return {"ok": True}
