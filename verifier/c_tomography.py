"""Receipt-defined verifier for C-TOMO (tomography / estimation as priced knowledge).

This verifier enforces a simple monotone rule: tighter epsilon requires more trials.
It also enforces that the trials file is receipted, and that its row count matches
what the claim declares.
"""

from __future__ import annotations

import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Mapping

from verifier.receipt_protocol import ReceiptProtocolError, ensure_in_receipt, verify_trs10_receipt


class TomographyVerificationError(Exception):
    """Raised when C-TOMO verification fails."""


@dataclass(frozen=True)
class TomographyClaim:
    epsilon: float
    n_trials: int


def _load_json_obj(path: Path) -> Dict[str, object]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise TomographyVerificationError(f"Missing required file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise TomographyVerificationError(f"Invalid JSON: {path}") from exc
    if not isinstance(data, dict):
        raise TomographyVerificationError(f"Expected JSON object in {path}")
    return data


def _parse_claim(path: Path) -> TomographyClaim:
    payload = _load_json_obj(path)
    try:
        epsilon = float(payload["epsilon"])
        n_trials = int(payload["n_trials"])
    except KeyError as exc:
        raise TomographyVerificationError(f"claim.json missing field: {exc}") from exc
    except (TypeError, ValueError) as exc:
        raise TomographyVerificationError("claim.json has invalid epsilon/n_trials") from exc

    if epsilon <= 0:
        raise TomographyVerificationError("epsilon must be positive")
    if n_trials <= 0:
        raise TomographyVerificationError("n_trials must be positive")

    return TomographyClaim(epsilon=epsilon, n_trials=n_trials)


def _required_trials(epsilon: float, scale: int = 16) -> int:
    # Simple monotone proxy: O(1/epsilon^2)
    return int(math.ceil(scale / (epsilon * epsilon)))


def _count_trials_csv(path: Path) -> int:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            raise TomographyVerificationError("trials.csv missing header")
        count = 0
        for _ in reader:
            count += 1
        return count


def verify_tomography(
    run_dir: Path,
    trust_manifest_path: Path,
    *,
    claim_name: str = "claim.json",
    receipt_name: str = "tomography.receipt.json",
    trials_name: str = "trials.csv",
) -> Mapping[str, object]:
    run_dir = Path(run_dir)
    claim_path = run_dir / claim_name
    receipt_path = run_dir / receipt_name
    trials_path = run_dir / trials_name

    claim = _parse_claim(claim_path)

    try:
        receipt = verify_trs10_receipt(
            receipt_path,
            files_dir=run_dir,
            trust_manifest_path=Path(trust_manifest_path),
        )
        ensure_in_receipt(receipt, [claim_name, trials_name])
    except ReceiptProtocolError as exc:
        raise TomographyVerificationError(str(exc)) from exc

    if not trials_path.exists():
        raise TomographyVerificationError("Missing trials.csv")

    observed_trials = _count_trials_csv(trials_path)
    if observed_trials != claim.n_trials:
        raise TomographyVerificationError(
            f"Claimed n_trials={claim.n_trials} but trials.csv has {observed_trials} rows"
        )

    required = _required_trials(claim.epsilon)
    if claim.n_trials < required:
        raise TomographyVerificationError(
            f"Underpaid: need n_trials >= {required} for epsilon={claim.epsilon}, got {claim.n_trials}"
        )

    return {
        "ok": True,
        "epsilon": claim.epsilon,
        "n_trials": claim.n_trials,
        "required_trials": required,
        "required_disclosure_bits": 0,
        "provided_disclosure_bits": 0,
        "receipt": receipt_path.name,
    }
