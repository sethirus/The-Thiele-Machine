"""Receipt-defined verifier for C-ENTROPY (coarse-graining made explicit).

This verifier treats entropy as *priced knowledge*: any entropy claim must declare a
coarse-graining (partition) in a receipted artifact, and stronger claims require
more explicit disclosure bits.

This is deliberately conservative and repo-internal:
- it verifies a signed TRS-1.0 manifest over the run artifacts
- it rejects entropy claims without a declared coarse-graining
- it enforces a simple monotone disclosure rule
"""

from __future__ import annotations

import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Mapping, cast

from verifier.receipt_protocol import ReceiptProtocolError, ensure_in_receipt, verify_trs10_receipt


class EntropyVerificationError(Exception):
    """Raised when C-ENTROPY verification fails."""


@dataclass(frozen=True)
class EntropyClaim:
    h_lower_bound_bits: float
    n_samples: int


def _load_json_obj(path: Path) -> Dict[str, object]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise EntropyVerificationError(f"Missing required file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise EntropyVerificationError(f"Invalid JSON: {path}") from exc
    if not isinstance(data, dict):
        raise EntropyVerificationError(f"Expected JSON object in {path}")
    return data


def _parse_claim(path: Path) -> EntropyClaim:
    payload = _load_json_obj(path)
    try:
        h_raw = cast(Any, payload["h_lower_bound_bits"])
        n_raw = cast(Any, payload["n_samples"])
    except KeyError as exc:
        raise EntropyVerificationError(f"claim.json missing field: {exc}") from exc

    try:
        h = float(h_raw)
        n = int(n_raw)
    except (TypeError, ValueError) as exc:
        raise EntropyVerificationError("claim.json has invalid h_lower_bound_bits/n_samples") from exc

    if h < 0:
        raise EntropyVerificationError("h_lower_bound_bits must be non-negative")
    if n <= 0:
        raise EntropyVerificationError("n_samples must be positive")

    return EntropyClaim(h_lower_bound_bits=h, n_samples=n)


def _count_samples_csv(path: Path) -> int:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            raise EntropyVerificationError("samples.csv missing header")
        count = 0
        for _ in reader:
            count += 1
        return count


def _required_disclosure_bits(h_lower_bound_bits: float, scale: int = 1024) -> int:
    if h_lower_bound_bits <= 0:
        return 0
    return int(math.ceil(scale * float(h_lower_bound_bits)))


def verify_entropy2(
    run_dir: Path,
    trust_manifest_path: Path,
    *,
    claim_name: str = "claim.json",
    receipt_name: str = "entropy.receipt.json",
    samples_name: str = "samples.csv",
    coarse_name: str = "coarse_graining.json",
) -> Mapping[str, object]:
    run_dir = Path(run_dir)
    claim_path = run_dir / claim_name
    receipt_path = run_dir / receipt_name
    samples_path = run_dir / samples_name
    coarse_path = run_dir / coarse_name

    claim = _parse_claim(claim_path)

    try:
        receipt = verify_trs10_receipt(
            receipt_path,
            files_dir=run_dir,
            trust_manifest_path=Path(trust_manifest_path),
        )
        # Coarse-graining is mandatory for any entropy claim.
        ensure_in_receipt(receipt, [claim_name, samples_name, coarse_name])
    except ReceiptProtocolError as exc:
        raise EntropyVerificationError(str(exc)) from exc

    if not samples_path.exists():
        raise EntropyVerificationError("Missing samples.csv")

    observed = _count_samples_csv(samples_path)
    if observed != claim.n_samples:
        raise EntropyVerificationError(
            f"Claimed n_samples={claim.n_samples} but samples.csv has {observed} rows"
        )

    if not coarse_path.exists():
        raise EntropyVerificationError("Missing coarse_graining.json")

    coarse = _load_json_obj(coarse_path)
    partition_id = coarse.get("partition_id")
    disclosure_bits = coarse.get("disclosure_bits")
    if not (isinstance(partition_id, str) and partition_id):
        raise EntropyVerificationError("coarse_graining.json must include non-empty partition_id")
    if not isinstance(disclosure_bits, int) or disclosure_bits < 0:
        raise EntropyVerificationError("coarse_graining.json must include non-negative integer disclosure_bits")

    required = _required_disclosure_bits(claim.h_lower_bound_bits)
    if disclosure_bits < required:
        raise EntropyVerificationError(
            f"Insufficient disclosure_bits: need >= {required}, got {disclosure_bits}"
        )

    return {
        "ok": True,
        "h_lower_bound_bits": claim.h_lower_bound_bits,
        "n_samples": claim.n_samples,
        "partition_id": partition_id,
        "required_disclosure_bits": required,
        "provided_disclosure_bits": int(disclosure_bits),
        "receipt": receipt_path.name,
    }
