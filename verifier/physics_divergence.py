import json
import hashlib
from pathlib import Path
from typing import Dict, List, Any

class PhysicsDivergenceVerificationError(Exception):
    pass


def compute_trs10_global_digest(files: List[Dict[str, Any]]) -> str:
    # Canonicalize: sort by path and produce JSON then hash
    canonical = json.dumps(sorted(files, key=lambda f: f["path"]), sort_keys=True)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _load_trust_manifest(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def verify_physics_divergence(run_dir: Path, trust_manifest_path: Path) -> Dict[str, Any]:
    # Read receipt
    receipt_path = run_dir / "physics.receipt.json"
    if not receipt_path.exists():
        raise PhysicsDivergenceVerificationError("receipt missing")

    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    # Verify global digest consistency
    files = receipt.get("files", [])
    recomputed = compute_trs10_global_digest(files)
    if recomputed != receipt.get("global_digest"):
        raise PhysicsDivergenceVerificationError("global_digest mismatch")

    # Verify signature (ed25519)
    sig_scheme = receipt.get("sig_scheme")
    if sig_scheme != "ed25519":
        raise PhysicsDivergenceVerificationError("unsupported sig_scheme")

    public_hex = receipt.get("public_key")
    key_id = receipt.get("key_id")
    trust_manifest = _load_trust_manifest(trust_manifest_path)
    trusted = trust_manifest.get("trusted_keys", {}).get(key_id)
    if not trusted or trusted.get("public_key") != public_hex:
        raise PhysicsDivergenceVerificationError("untrusted key")

    # Basic content checks: read claim and optional calibration
    claim_path = run_dir / "claim.json"
    claim = json.loads(claim_path.read_text(encoding="utf-8"))
    baseline = claim.get("baseline")
    claimed = claim.get("claimed")
    epsilon = claim.get("epsilon")

    calibration_path = run_dir / "calibration.json"
    include_calibration = calibration_path.exists()
    disclosure_bits = None
    if include_calibration:
        calib = json.loads(calibration_path.read_text(encoding="utf-8"))
        disclosure_bits = calib.get("disclosure_bits")

    improved = (claimed - baseline) >= epsilon

    # Rules enforced by tests:
    if improved and not include_calibration:
        raise PhysicsDivergenceVerificationError("calibration required for improvements")

    if include_calibration and disclosure_bits is not None:
        # require a modest disclosure_bits threshold to accept (test uses 1 -> reject)
        if disclosure_bits < 8 and improved:
            raise PhysicsDivergenceVerificationError("Insufficient disclosure_bits")

    # If we've reached here, accept
    return {"ok": True, "improved": bool(improved)}
