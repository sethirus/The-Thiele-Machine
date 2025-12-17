"""Receipt-defined verifier for C-RAND (device-independent certified randomness).

This is intentionally a *provenance + pricing* gate, not a randomness extractor.
It enforces:
- every input used must be in the TRS-1.0 receipt
- certified min-entropy claims require explicit nonlocality/disclosure evidence
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Mapping

from verifier.receipt_protocol import (
    ReceiptProtocolError,
    ensure_in_receipt,
    verify_trs10_receipt,
)


class RandomnessVerificationError(Exception):
    """Raised when C-RAND verification fails."""


@dataclass(frozen=True)
class RandomnessClaim:
    n_bits: int
    min_entropy_per_bit: float

    @property
    def total_min_entropy(self) -> float:
        return float(self.n_bits) * float(self.min_entropy_per_bit)


def _load_json_obj(path: Path) -> Dict[str, object]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RandomnessVerificationError(f"Missing required file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise RandomnessVerificationError(f"Invalid JSON: {path}") from exc
    if not isinstance(data, dict):
        raise RandomnessVerificationError(f"Expected JSON object in {path}")
    return data


def _parse_claim(path: Path) -> RandomnessClaim:
    payload = _load_json_obj(path)
    try:
        n_bits = int(payload["n_bits"])
        min_entropy_per_bit = float(payload["min_entropy_per_bit"])
    except KeyError as exc:
        raise RandomnessVerificationError(f"claim.json missing field: {exc}") from exc
    except (TypeError, ValueError) as exc:
        raise RandomnessVerificationError("claim.json has invalid n_bits/min_entropy_per_bit") from exc

    if n_bits <= 0:
        raise RandomnessVerificationError("n_bits must be positive")
    if min_entropy_per_bit < 0:
        raise RandomnessVerificationError("min_entropy_per_bit must be non-negative")
    if min_entropy_per_bit > 1.0:
        raise RandomnessVerificationError("min_entropy_per_bit cannot exceed 1")

    return RandomnessClaim(n_bits=n_bits, min_entropy_per_bit=min_entropy_per_bit)


def _min_disclosure_bits(total_min_entropy: float, scale: int = 1024) -> int:
    if total_min_entropy <= 0:
        return 0
    return int(math.ceil(scale * total_min_entropy))


def verify_randomness(
    run_dir: Path,
    trust_manifest_path: Path,
    *,
    claim_name: str = "claim.json",
    receipt_name: str = "randomness.receipt.json",
    bits_name: str = "randomness.bin",
    disclosure_name: str = "nonlocality.json",
) -> Mapping[str, object]:
    run_dir = Path(run_dir)
    claim_path = run_dir / claim_name
    receipt_path = run_dir / receipt_name
    bits_path = run_dir / bits_name
    disclosure_path = run_dir / disclosure_name

    claim = _parse_claim(claim_path)

    try:
        receipt = verify_trs10_receipt(
            receipt_path,
            files_dir=run_dir,
            trust_manifest_path=Path(trust_manifest_path),
        )
        ensure_in_receipt(receipt, [claim_name, bits_name])
    except ReceiptProtocolError as exc:
        raise RandomnessVerificationError(str(exc)) from exc

    if not bits_path.exists():
        raise RandomnessVerificationError(f"Missing bits file: {bits_name}")

    available_bits = bits_path.stat().st_size * 8
    if available_bits < claim.n_bits:
        raise RandomnessVerificationError(
            f"randomness.bin provides {available_bits} bits, but claim requires {claim.n_bits}"
        )

    required = _min_disclosure_bits(claim.total_min_entropy)
    provided = 0

    if required > 0:
        try:
            ensure_in_receipt(receipt, [disclosure_name])
        except ReceiptProtocolError as exc:
            raise RandomnessVerificationError(str(exc)) from exc

        if not disclosure_path.exists():
            raise RandomnessVerificationError("nonlocality.json missing")

        disclosure = _load_json_obj(disclosure_path)
        bits = disclosure.get("disclosure_bits")
        if not isinstance(bits, int):
            raise RandomnessVerificationError("nonlocality.json must include integer disclosure_bits")
        if bits < required:
            raise RandomnessVerificationError(
                f"Insufficient disclosure_bits: need >= {required}, got {bits}"
            )
        provided = bits

    return {
        "ok": True,
        "n_bits": claim.n_bits,
        "min_entropy_per_bit": claim.min_entropy_per_bit,
        "min_entropy_lower_bound": claim.total_min_entropy,
        "required_disclosure_bits": required,
        "provided_disclosure_bits": provided,
        "receipt": receipt_path.name,
    }
