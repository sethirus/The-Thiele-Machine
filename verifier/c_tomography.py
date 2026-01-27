import json
import math
from pathlib import Path
from typing import Dict, Any
from .receipt_protocol import _sha256_hex

class TomographyVerificationError(Exception):
    pass


def verify_tomography(run_dir: Path, trust_manifest_path: Path) -> Dict[str, Any]:
    receipt_path = run_dir / "tomography.receipt.json"
    if not receipt_path.exists():
        raise TomographyVerificationError("receipt missing")

    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    file_paths = [f["path"] for f in receipt.get("files", [])]
    if "trials.csv" not in file_paths:
        raise TomographyVerificationError("Receipt missing required trials.csv")

    # Hash checks
    for f in receipt.get("files", []):
        p = run_dir / f["path"]
        if not p.exists():
            raise TomographyVerificationError("Receipt references missing file")
        cur_hash = _sha256_hex(p)
        if cur_hash != f.get("sha256"):
            raise TomographyVerificationError("Hash mismatch")

    claim = json.loads((run_dir / "claim.json").read_text(encoding="utf-8"))
    epsilon = claim.get("epsilon")
    n_trials = claim.get("n_trials")

    if epsilon is None or n_trials is None:
        raise TomographyVerificationError("Malformed claim")

    required = math.ceil(1.0 / (epsilon ** 2))
    if n_trials < required:
        raise TomographyVerificationError("Underpaid")

    return {"ok": True}

    if epsilon is None or n_trials is None:
        raise TomographyVerificationError("Malformed claim")

    required = math.ceil(1.0 / (epsilon ** 2))
    if n_trials < required:
        raise TomographyVerificationError("Underpaid")

    return {"ok": True}
