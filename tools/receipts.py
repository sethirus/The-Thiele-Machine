# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Receipt canonicalisation and verification utilities.

The historical versions of the repository shipped receipts that advertised
cryptographic integrity, but the helper scripts never enforced those claims.
This module provides a single, well-tested implementation that can be reused
by command-line tools and tests alike.  It performs the following checks:

* canonical SHA-256 hashing of each step (with deterministic JSON encoding),
* aggregation of the global digest as the hash of the ordered step hashes,
* Ed25519 signature verification over the digest, and
* optional certificate hash checks for legacy receipts.

The :class:`ReceiptValidator` returns the accumulated μ-bit charge so that
callers can perform additional consistency checks or summarise totals.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Mapping, Sequence

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

CANONICAL_SEPARATORS = (",", ":")


class ReceiptValidationError(ValueError):
    """Raised when a receipt fails an integrity check."""


def _canonical_step_payload(step: Mapping[str, object]) -> bytes:
    """Encode ``step`` using canonical JSON without the ``step_hash`` field."""

    material = {k: v for k, v in step.items() if k != "step_hash"}
    return json.dumps(
        material,
        sort_keys=True,
        ensure_ascii=False,
        separators=CANONICAL_SEPARATORS,
    ).encode("utf-8")


def compute_step_hash(step: Mapping[str, object]) -> str:
    """Return the canonical SHA-256 hash of ``step``."""

    return hashlib.sha256(_canonical_step_payload(step)).hexdigest()


def compute_global_digest(step_hashes: Sequence[str]) -> str:
    """Hash the ordered ``step_hashes`` to obtain the global digest."""

    digest = hashlib.sha256()
    for value in step_hashes:
        try:
            digest.update(bytes.fromhex(value))
        except ValueError as exc:  # pragma: no cover - defensive branch
            raise ReceiptValidationError(f"invalid step hash encoding: {value!r}") from exc
    return digest.hexdigest()


def _normalise_mu(value: object, step_index: int) -> float:
    """Convert a μ-bit delta to a float, rejecting negative or infinite values."""

    if isinstance(value, (int, float)):
        mu = float(value)
    elif isinstance(value, str):
        if value.upper() == "INF":
            raise ReceiptValidationError(
                f"step {step_index}: μ charge marked infinite; manual review required"
            )
        try:
            mu = float(value)
        except ValueError as exc:
            raise ReceiptValidationError(
                f"step {step_index}: μ charge {value!r} is not numeric"
            ) from exc
    else:
        raise ReceiptValidationError(
            f"step {step_index}: μ charge must be numeric, got {type(value).__name__}"
        )

    if mu < 0:
        raise ReceiptValidationError(f"step {step_index}: μ charge cannot be negative")
    return mu


def _check_certificate_hash(step: Mapping[str, object], step_index: int) -> None:
    """Validate ``certificate_hash`` for legacy receipts when present."""

    if "certificate_hash" not in step:
        return

    certificate = step.get("certificate", "")
    if isinstance(certificate, str):
        payload = certificate.encode("utf-8")
    else:
        payload = json.dumps(certificate, sort_keys=True).encode("utf-8")
    expected = hashlib.sha256(payload).hexdigest()
    recorded = step.get("certificate_hash")
    if recorded != expected:
        raise ReceiptValidationError(
            f"step {step_index}: certificate hash mismatch (expected {expected}, got {recorded})"
        )


def _verify_signature(pubkey_hex: str, signature_hex: str, digest_hex: str) -> None:
    """Raise :class:`ReceiptValidationError` if the Ed25519 signature is invalid."""

    try:
        pubkey_bytes = bytes.fromhex(pubkey_hex)
        signature_bytes = bytes.fromhex(signature_hex)
        digest_bytes = bytes.fromhex(digest_hex)
    except ValueError as exc:
        raise ReceiptValidationError("receipt contains non-hexadecimal fields") from exc

    if len(pubkey_bytes) != 32:
        raise ReceiptValidationError(
            f"kernel_pubkey must be 32 bytes for Ed25519, got {len(pubkey_bytes)}"
        )
    if len(signature_bytes) != 64:
        raise ReceiptValidationError(
            f"signature must be 64 bytes for Ed25519, got {len(signature_bytes)}"
        )

    try:
        Ed25519PublicKey.from_public_bytes(pubkey_bytes).verify(signature_bytes, digest_bytes)
    except InvalidSignature as exc:
        raise ReceiptValidationError("signature verification failed") from exc


@dataclass
class ReceiptValidator:
    """Validate receipts and return their μ-bit totals."""

    require_signature: bool = True

    def validate(self, receipt: Mapping[str, object]) -> float:
        if not isinstance(receipt, Mapping):
            raise ReceiptValidationError("receipt must be a mapping")

        spec_version = receipt.get("spec_version")
        if spec_version != "1.0":
            raise ReceiptValidationError(
                f"unsupported spec_version {spec_version!r}; expected '1.0'"
            )

        steps_obj = receipt.get("steps")
        if not isinstance(steps_obj, Sequence) or not steps_obj:
            raise ReceiptValidationError("receipt must contain at least one step")

        step_hashes = []
        mu_total = 0.0
        for idx, raw_step in enumerate(steps_obj):
            if not isinstance(raw_step, Mapping):
                raise ReceiptValidationError(f"step {idx} is not a mapping")

            stored_hash = raw_step.get("step_hash")
            computed_hash = compute_step_hash(raw_step)
            if stored_hash != computed_hash:
                raise ReceiptValidationError(
                    f"step {idx}: hash mismatch (expected {computed_hash}, got {stored_hash})"
                )

            _check_certificate_hash(raw_step, idx)
            mu_total += _normalise_mu(raw_step.get("mu_delta"), idx)
            step_hashes.append(computed_hash)

        computed_digest = compute_global_digest(step_hashes)
        recorded_digest = receipt.get("global_digest")
        if recorded_digest != computed_digest:
            raise ReceiptValidationError(
                f"global digest mismatch (expected {computed_digest}, got {recorded_digest})"
            )

        if self.require_signature:
            pubkey_hex = receipt.get("kernel_pubkey")
            signature_hex = receipt.get("signature")
            if not isinstance(pubkey_hex, str) or not isinstance(signature_hex, str):
                raise ReceiptValidationError("receipt missing signature fields")
            _verify_signature(pubkey_hex, signature_hex, computed_digest)

        return mu_total


__all__ = [
    "ReceiptValidationError",
    "ReceiptValidator",
    "compute_step_hash",
    "compute_global_digest",
]

