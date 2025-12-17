"""Receipt-defined verifier for C-CAUSAL (no free causal explanation).

This verifier enforces that *strictly stronger-than-observational* causal claims
must be accompanied by explicit assumptions or interventional evidence, captured
in receipted artifacts.

It is intentionally minimal and conservative.
"""

from __future__ import annotations

import csv
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Mapping

from verifier.receipt_protocol import ReceiptProtocolError, ensure_in_receipt, verify_trs10_receipt


class CausalVerificationError(Exception):
    """Raised when C-CAUSAL verification fails."""


@dataclass(frozen=True)
class CausalClaim:
    claim_type: str  # "unique_dag" | "ate"
    n_obs: int


def _load_json_obj(path: Path) -> Dict[str, object]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise CausalVerificationError(f"Missing required file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise CausalVerificationError(f"Invalid JSON: {path}") from exc
    if not isinstance(data, dict):
        raise CausalVerificationError(f"Expected JSON object in {path}")
    return data


def _parse_claim(path: Path) -> CausalClaim:
    payload = _load_json_obj(path)
    claim_type = payload.get("claim_type")
    n_obs = payload.get("n_obs")
    if not isinstance(claim_type, str) or claim_type not in {"unique_dag", "ate"}:
        raise CausalVerificationError("claim.json claim_type must be 'unique_dag' or 'ate'")
    if not isinstance(n_obs, int) or n_obs <= 0:
        raise CausalVerificationError("claim.json n_obs must be a positive integer")
    return CausalClaim(claim_type=claim_type, n_obs=n_obs)


def _count_rows_csv(path: Path) -> int:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            raise CausalVerificationError(f"{path.name} missing header")
        count = 0
        for _ in reader:
            count += 1
        return count


def _required_disclosure_bits(claim_type: str) -> int:
    if claim_type == "unique_dag":
        return 8192
    if claim_type == "ate":
        return 2048
    return 0


def verify_causal(
    run_dir: Path,
    trust_manifest_path: Path,
    *,
    claim_name: str = "claim.json",
    receipt_name: str = "causal.receipt.json",
    observational_name: str = "observational.csv",
    assumptions_name: str = "assumptions.json",
    interventions_name: str = "interventions.csv",
) -> Mapping[str, object]:
    run_dir = Path(run_dir)
    claim_path = run_dir / claim_name
    receipt_path = run_dir / receipt_name
    obs_path = run_dir / observational_name
    assumptions_path = run_dir / assumptions_name
    interventions_path = run_dir / interventions_name

    claim = _parse_claim(claim_path)

    try:
        receipt = verify_trs10_receipt(
            receipt_path,
            files_dir=run_dir,
            trust_manifest_path=Path(trust_manifest_path),
        )
        ensure_in_receipt(receipt, [claim_name, observational_name])
    except ReceiptProtocolError as exc:
        raise CausalVerificationError(str(exc)) from exc

    if not obs_path.exists():
        raise CausalVerificationError("Missing observational.csv")

    observed = _count_rows_csv(obs_path)
    if observed != claim.n_obs:
        raise CausalVerificationError(f"Claimed n_obs={claim.n_obs} but observational.csv has {observed} rows")

    # Stronger-than-observational claims require either interventional data, or explicit assumptions.
    has_interventions = interventions_path.exists()
    if has_interventions:
        try:
            ensure_in_receipt(receipt, [interventions_name])
        except ReceiptProtocolError as exc:
            raise CausalVerificationError(str(exc)) from exc

    required = _required_disclosure_bits(claim.claim_type)
    provided = 0

    if claim.claim_type == "unique_dag" and not has_interventions:
        # Uniqueness from observational alone is forbidden without explicit assumptions.
        try:
            ensure_in_receipt(receipt, [assumptions_name])
        except ReceiptProtocolError as exc:
            raise CausalVerificationError(str(exc)) from exc

    if required > 0 and not has_interventions:
        if not assumptions_path.exists():
            raise CausalVerificationError("Missing assumptions.json")

        assumptions = _load_json_obj(assumptions_path)
        bits = assumptions.get("disclosure_bits")
        if not isinstance(bits, int) or bits < 0:
            raise CausalVerificationError("assumptions.json must include non-negative integer disclosure_bits")
        provided = bits

        if bits < required:
            raise CausalVerificationError(f"Insufficient disclosure_bits: need >= {required}, got {bits}")

    return {
        "ok": True,
        "claim_type": claim.claim_type,
        "n_obs": claim.n_obs,
        "has_interventions": bool(has_interventions),
        "required_disclosure_bits": int(required if not has_interventions else 0),
        "provided_disclosure_bits": int(provided if not has_interventions else 0),
        "receipt": receipt_path.name,
    }
