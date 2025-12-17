"""Receipt-defined verifier for the C1 (physics) divergence milestone.

C1 is *not* a physics simulator. It is a provenance + disclosure gate:
- claims must be backed by a signed artifact receipt (TRS-1.0 file manifest)
- any claimed improvement above baseline must include explicit calibration/disclosure

This keeps the milestone executable inside the repo while remaining compatible with
future external experiment mappings.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from verifier.receipt_protocol import (
    ReceiptProtocolError,
    compute_trs10_global_digest,
    ensure_in_receipt,
    sha256_hex,
    verify_trs10_receipt,
)
from verifier.signature_utils import TrustManifest, load_trust_manifest


class PhysicsDivergenceVerificationError(Exception):
    """Raised when a C1 physics-divergence claim cannot be verified."""


@dataclass(frozen=True)
class PhysicsClaim:
    metric: str
    baseline: float
    claimed: float
    epsilon: float

    @property
    def improvement(self) -> float:
        return self.claimed - self.baseline

    @property
    def is_improved(self) -> bool:
        return self.improvement > self.epsilon


def canonical_json(obj: Mapping[str, object]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _load_json(path: Path) -> Dict[str, object]:
    try:
        with path.open("r", encoding="utf-8") as handle:
            data = json.load(handle)
    except FileNotFoundError as exc:
        raise PhysicsDivergenceVerificationError(f"Missing required file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise PhysicsDivergenceVerificationError(f"Invalid JSON: {path}") from exc

    if not isinstance(data, dict):
        raise PhysicsDivergenceVerificationError(f"Expected JSON object in {path}")
    return data


def _parse_claim(path: Path) -> PhysicsClaim:
    payload = _load_json(path)

    metric = str(payload.get("metric") or "metric")
    try:
        baseline = float(payload["baseline"])
        claimed = float(payload["claimed"])
        epsilon = float(payload["epsilon"])
    except KeyError as exc:
        raise PhysicsDivergenceVerificationError(f"claim.json missing field: {exc}") from exc
    except (TypeError, ValueError) as exc:
        raise PhysicsDivergenceVerificationError("claim.json has non-numeric baseline/claimed/epsilon") from exc

    if epsilon < 0:
        raise PhysicsDivergenceVerificationError("epsilon must be non-negative")

    return PhysicsClaim(metric=metric, baseline=baseline, claimed=claimed, epsilon=epsilon)


def _min_disclosure_bits(epsilon: float, scale: int = 1024) -> int:
    """Simple monotone cost proxy: larger claimed improvements require more bits."""

    if epsilon <= 0:
        return 0
    return int(math.ceil(scale * epsilon))


def verify_physics_divergence(
    run_dir: Path,
    trust_manifest_path: Path,
    claim_name: str = "claim.json",
    receipt_name: str = "physics.receipt.json",
    calibration_name: str = "calibration.json",
) -> Mapping[str, object]:
    """Verify a physics/bench claim using only receipt-defined artifacts."""

    run_dir = Path(run_dir)
    trust_manifest = load_trust_manifest(Path(trust_manifest_path))

    claim_path = run_dir / claim_name
    receipt_path = run_dir / receipt_name

    claim = _parse_claim(claim_path)
    try:
        receipt = verify_trs10_receipt(
            receipt_path,
            files_dir=run_dir,
            trust_manifest_path=Path(trust_manifest_path),
        )
        ensure_in_receipt(receipt, [claim_name])
    except ReceiptProtocolError as exc:
        raise PhysicsDivergenceVerificationError(str(exc)) from exc

    required_disclosure = _min_disclosure_bits(claim.epsilon)
    calibration_path = run_dir / calibration_name

    if claim.is_improved:
        try:
            ensure_in_receipt(receipt, [calibration_name])
        except ReceiptProtocolError as exc:
            raise PhysicsDivergenceVerificationError(str(exc)) from exc
        if not calibration_path.exists():
            raise PhysicsDivergenceVerificationError("Missing calibration.json for improved claim")

        calibration = _load_json(calibration_path)
        bits = calibration.get("disclosure_bits")
        if not isinstance(bits, int):
            raise PhysicsDivergenceVerificationError("calibration.json must include integer 'disclosure_bits'")
        if bits < required_disclosure:
            raise PhysicsDivergenceVerificationError(
                f"Insufficient disclosure_bits: need >= {required_disclosure}, got {bits}"
            )

    return {
        "ok": True,
        "metric": claim.metric,
        "baseline": claim.baseline,
        "claimed": claim.claimed,
        "epsilon": claim.epsilon,
        "improved": claim.is_improved,
        "required_disclosure_bits": required_disclosure,
        "receipt": receipt_path.name,
    }
