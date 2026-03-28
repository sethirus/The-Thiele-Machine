from __future__ import annotations

from pathlib import Path

from .crypto import verify_digest_signature
from .execution import ExecutionVerifierAdapters, default_execution_adapters, verify_execution_receipt
from .fileset import verify_fileset_entries
from .protocol import extract_signed_payload, payload_digest


def verify_receipt_dict(
    receipt: dict,
    *,
    trusted_public_key_hex: str,
    base_dir: Path | None = None,
    execution_adapters: ExecutionVerifierAdapters | None = None,
) -> None:
    payload = extract_signed_payload(receipt)
    expected_digest = payload_digest(payload)
    if receipt["global_digest"] != expected_digest:
        raise ValueError("Receipt global_digest does not match canonical payload digest")

    verify_digest_signature(
        public_key_hex=trusted_public_key_hex,
        signature_hex=receipt["signature"],
        digest_hex=expected_digest,
    )

    if payload["kind"] == "fileset":
        if base_dir is not None:
            verify_fileset_entries(receipt, base_dir=base_dir)
        return

    if payload["kind"] == "execution":
        if base_dir is None:
            raise ValueError("Execution receipt verification requires a base_dir")
        if execution_adapters is None:
            execution_adapters = default_execution_adapters()
        verify_execution_receipt(receipt, base_dir=base_dir, adapters=execution_adapters)
        return

    raise ValueError(f"Unsupported receipt kind: {payload['kind']!r}")