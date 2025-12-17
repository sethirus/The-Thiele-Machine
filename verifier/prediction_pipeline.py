"""Receipt-defined verifier for C2 prediction-pipeline divergence.

Goal (C2): reject “free insight” improvements unless they come with explicit,
checkable structure/revelation certificates.

This verifier intentionally uses only **receipt-defined observables**:
- step receipts (signed): `step_receipts.json`
- μ-ledger: `mu_ledger.json`

It does not trust logs, stdout, or non-receipted files.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Optional

from thielecpu.receipts import load_receipts


@dataclass(frozen=True)
class PredictionVerificationResult:
    ok: bool
    claimed_score: Optional[float]
    has_structure_addition: bool
    mu_information_total: float
    reason: str


def _parse_claimed_score_from_event_value(value: str) -> Optional[float]:
    value = value.strip()
    if not value:
        return None

    # Accept a minimal canonical format: `SCORE <float>`
    # Example: `SCORE 0.99`
    parts = value.split()
    if len(parts) == 2 and parts[0].upper() == "SCORE":
        try:
            return float(parts[1])
        except ValueError:
            return None

    return None


def extract_claimed_score(outdir: Path) -> Optional[float]:
    """Extract the last claimed score from signed step receipts."""

    receipts_path = outdir / "step_receipts.json"
    receipts = load_receipts(receipts_path)

    claimed: Optional[float] = None
    for receipt in receipts:
        event = receipt.observation.event or {}
        value = str(event.get("value", ""))
        score = _parse_claimed_score_from_event_value(value)
        if score is not None:
            claimed = score
    return claimed


def has_semantic_structure_addition(outdir: Path) -> bool:
    """Return True iff receipts show cert_addr transitioned empty -> non-empty."""

    receipts_path = outdir / "step_receipts.json"
    receipts = load_receipts(receipts_path)

    for receipt in receipts:
        pre_cert = str(receipt.pre_state.get("cert_addr", ""))
        post_cert = str(receipt.post_state.get("cert_addr", ""))
        if (not pre_cert) and post_cert:
            return True
    return False


def mu_information_total(outdir: Path) -> float:
    """Return total μ-information from `mu_ledger.json` (last snapshot)."""

    ledger_path = outdir / "mu_ledger.json"
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    if not ledger:
        return 0.0
    return float(ledger[-1].get("total_mu_information", 0.0))


def verify_prediction_pipeline(
    outdir: Path,
    *,
    baseline_score: float,
    require_cert_for_improvement: bool = True,
    require_mu_for_improvement: bool = True,
    min_mu_information: float = 1.0,
) -> PredictionVerificationResult:
    """Verify a prediction pipeline run from receipts.

    Policy encoded here for C2:
    - If the pipeline claims an improved score above baseline, it must also show:
      - a semantic structure-addition event (cert_addr transition), and
      - a positive μ-information charge.

    Otherwise, the claimed improvement is rejected as “free insight”.
    """

    claimed = extract_claimed_score(outdir)
    structure_addition = has_semantic_structure_addition(outdir)
    mu_info = mu_information_total(outdir)

    if claimed is None:
        return PredictionVerificationResult(
            ok=False,
            claimed_score=None,
            has_structure_addition=structure_addition,
            mu_information_total=mu_info,
            reason="no SCORE claim found in receipts",
        )

    if claimed <= baseline_score:
        # Non-improving claims are allowed without structure addition.
        return PredictionVerificationResult(
            ok=True,
            claimed_score=claimed,
            has_structure_addition=structure_addition,
            mu_information_total=mu_info,
            reason="score does not exceed baseline",
        )

    # Claimed improvement: require certificate / μ-info.
    if require_cert_for_improvement and not structure_addition:
        return PredictionVerificationResult(
            ok=False,
            claimed_score=claimed,
            has_structure_addition=structure_addition,
            mu_information_total=mu_info,
            reason="claimed improvement without semantic structure-addition evidence",
        )

    if require_mu_for_improvement and mu_info < min_mu_information:
        return PredictionVerificationResult(
            ok=False,
            claimed_score=claimed,
            has_structure_addition=structure_addition,
            mu_information_total=mu_info,
            reason="claimed improvement without sufficient μ-information charge",
        )

    return PredictionVerificationResult(
        ok=True,
        claimed_score=claimed,
        has_structure_addition=structure_addition,
        mu_information_total=mu_info,
        reason="claimed improvement is certified and paid",
    )


__all__ = [
    "PredictionVerificationResult",
    "extract_claimed_score",
    "has_semantic_structure_addition",
    "mu_information_total",
    "verify_prediction_pipeline",
]
