"""Shared receipt protocol helpers for verifier tools.

This module is the shared "spine" for C-module verification artifacts:
- TRS-1.0 receipt creation + verification (file manifest + Ed25519 signature)
- trust_manifest.json writer
- standardized verification.json payload shape (TM-VERIFY-1)

Design rule: verifiers must use *receipt-defined* observables only.
"""

from __future__ import annotations

import datetime as _dt
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from verifier.signature_utils import (
    SignatureVerificationError,
    TrustManifest,
    TrustManifestError,
    load_trust_manifest,
    verify_ed25519_signature,
)

try:  # Prefer PyNaCl when available.
    from nacl import signing as nacl_signing
except ImportError:  # pragma: no cover
    nacl_signing = None

try:  # Fallback to cryptography.
    from cryptography.hazmat.primitives.asymmetric import ed25519 as crypto_ed25519
except ImportError:  # pragma: no cover
    crypto_ed25519 = None


class ReceiptProtocolError(Exception):
    """Raised when receipt verification or artifact writing fails."""


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(obj: Mapping[str, object]) -> bytes:
    return json.dumps(dict(obj), sort_keys=True, separators=(",", ":")).encode("utf-8")


def compute_file_object_hash(file_obj: Mapping[str, object]) -> str:
    return sha256_hex(canonical_json_bytes(file_obj))


def compute_trs10_global_digest(files: Sequence[Mapping[str, object]]) -> str:
    file_hashes = [compute_file_object_hash(f) for f in files]
    concatenated = "".join(file_hashes)
    return sha256_hex(bytes.fromhex(concatenated))


def _load_json_obj(path: Path) -> Dict[str, object]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ReceiptProtocolError(f"Missing required file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ReceiptProtocolError(f"Invalid JSON: {path}") from exc

    if not isinstance(data, dict):
        raise ReceiptProtocolError(f"Expected JSON object in {path}")
    return data


def verify_trs10_receipt(
    receipt_path: Path,
    *,
    files_dir: Optional[Path] = None,
    trust_manifest_path: Optional[Path] = None,
) -> Mapping[str, object]:
    """Verify a TRS-1.0 receipt (hashes + signature).

    Returns the parsed receipt dict on success.
    """

    receipt_path = Path(receipt_path)
    files_dir = receipt_path.parent if files_dir is None else Path(files_dir)

    receipt = _load_json_obj(receipt_path)
    version = receipt.get("version")
    if not (isinstance(version, str) and version.startswith("TRS-1")):
        raise ReceiptProtocolError(f"Unsupported receipt version: {version!r}")

    files = receipt.get("files")
    if not isinstance(files, list) or not all(isinstance(f, dict) for f in files):
        raise ReceiptProtocolError("Receipt must contain a 'files' array of objects")

    global_digest = receipt.get("global_digest")
    if not isinstance(global_digest, str) or not global_digest:
        raise ReceiptProtocolError("Receipt missing 'global_digest'")

    # Verify file digests.
    for file_entry in files:
        path_value = file_entry.get("path")
        sha_value = file_entry.get("sha256")
        if not isinstance(path_value, str) or not isinstance(sha_value, str):
            raise ReceiptProtocolError("Receipt file entries must have 'path' and 'sha256' strings")

        candidate_path = files_dir / path_value
        if not candidate_path.exists():
            raise ReceiptProtocolError(f"Receipt references missing file: {path_value}")

        actual = sha256_hex(candidate_path.read_bytes())
        if actual != sha_value:
            raise ReceiptProtocolError(f"Hash mismatch for {path_value}: expected {sha_value}, got {actual}")

    computed = compute_trs10_global_digest(files)
    if computed != global_digest:
        raise ReceiptProtocolError(f"Global digest mismatch: expected {global_digest}, got {computed}")

    sig_scheme = receipt.get("sig_scheme")
    if sig_scheme != "ed25519":
        raise ReceiptProtocolError("Receipt must be signed with Ed25519 (sig_scheme=ed25519)")

    signature_hex = receipt.get("signature")
    if not isinstance(signature_hex, str) or not signature_hex:
        raise ReceiptProtocolError("Receipt missing Ed25519 signature")

    if trust_manifest_path is None:
        raise ReceiptProtocolError("Verifier requires a trust manifest for TRS-1.0 receipts")

    trust_manifest = load_trust_manifest(Path(trust_manifest_path))

    try:
        entry = trust_manifest.select_entry(receipt_path, receipt)
        verify_ed25519_signature(global_digest, signature_hex, entry.public_key)
    except (TrustManifestError, SignatureVerificationError) as exc:
        raise ReceiptProtocolError(f"Receipt signature invalid: {exc}") from exc

    return receipt


def receipt_paths(receipt: Mapping[str, object]) -> List[str]:
    files = receipt.get("files")
    if not isinstance(files, list):
        return []
    out: List[str] = []
    for entry in files:
        if isinstance(entry, dict) and isinstance(entry.get("path"), str):
            out.append(str(entry["path"]))
    return out


def ensure_in_receipt(receipt: Mapping[str, object], required_paths: Iterable[str]) -> None:
    present = set(receipt_paths(receipt))
    missing = [p for p in required_paths if p not in present]
    if missing:
        raise ReceiptProtocolError(f"Receipt missing required files: {missing}")


def _relpath(base_dir: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(base_dir.resolve()).as_posix()
    except ValueError:
        return path.name


def _sign_message(private_key: object, message: bytes) -> bytes:
    if nacl_signing is not None and isinstance(private_key, nacl_signing.SigningKey):
        return private_key.sign(message).signature

    if crypto_ed25519 is not None and isinstance(private_key, crypto_ed25519.Ed25519PrivateKey):
        return private_key.sign(message)

    raise ReceiptProtocolError("No Ed25519 signing backend available")


def ed25519_keypair() -> Tuple[object, str]:
    """Return (private_key, public_key_hex)."""

    if nacl_signing is not None:
        sk = nacl_signing.SigningKey.generate()
        pk_hex = sk.verify_key.encode().hex()
        return sk, pk_hex

    if crypto_ed25519 is not None:
        sk = crypto_ed25519.Ed25519PrivateKey.generate()
        pk_hex = sk.public_key().public_bytes_raw().hex()
        return sk, pk_hex

    raise ReceiptProtocolError("No Ed25519 backend available; install PyNaCl or cryptography")


def write_trust_manifest(path: Path, *, key_id: str, public_key_hex: str, patterns: Optional[List[str]] = None) -> None:
    patterns = patterns or ["*"]
    payload = {
        "trusted_keys": {
            key_id: {
                "public_key": public_key_hex,
                "patterns": patterns,
                "comment": "generated by verifier/receipt_protocol.py",
            }
        }
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_trs10_receipt(
    *,
    receipt_path: Path,
    base_dir: Path,
    files: Sequence[Path],
    private_key: object,
    public_key_hex: str,
    key_id: Optional[str] = None,
    metadata: Optional[Mapping[str, object]] = None,
) -> Mapping[str, object]:
    base_dir = Path(base_dir)
    entries: List[Dict[str, object]] = []
    for file_path in files:
        file_path = Path(file_path)
        rel = _relpath(base_dir, file_path)
        entries.append({"path": rel, "size": file_path.stat().st_size, "sha256": sha256_hex(file_path.read_bytes())})

    global_digest = compute_trs10_global_digest(entries)
    receipt: Dict[str, object] = {
        "version": "TRS-1.0",
        "files": entries,
        "global_digest": global_digest,
        "kernel_sha256": entries[0]["sha256"] if len(entries) == 1 else global_digest,
        "timestamp": _dt.datetime.now().astimezone().isoformat(),
        "sig_scheme": "ed25519",
        "signature": _sign_message(private_key, global_digest.encode("utf-8")).hex(),
        "public_key": public_key_hex,
    }
    if key_id:
        receipt["key_id"] = key_id
    if metadata:
        receipt["metadata"] = dict(metadata)

    receipt_path = Path(receipt_path)
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return receipt


def validate_verification_payload(payload: Mapping[str, object]) -> None:
    """Lightweight enforcement of TM-VERIFY-1 without external deps."""

    required_top = [
        "schema_version",
        "module",
        "status",
        "ok",
        "inputs",
        "results",
        "falsifiers",
        "mu_summary",
        "metadata",
    ]
    for key in required_top:
        if key not in payload:
            raise ReceiptProtocolError(f"verification.json missing field: {key}")

    if payload.get("schema_version") != "TM-VERIFY-1":
        raise ReceiptProtocolError("verification.json schema_version must be TM-VERIFY-1")

    status = payload.get("status")
    if status not in {"PASS", "FAIL", "UNCERTIFIED"}:
        raise ReceiptProtocolError("verification.json status must be PASS/FAIL/UNCERTIFIED")

    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        raise ReceiptProtocolError("verification.json inputs must be an object")
    for key in ("run_dir", "trust_manifest", "receipt"):
        if key not in inputs:
            raise ReceiptProtocolError(f"verification.json inputs missing: {key}")

    mu = payload.get("mu_summary")
    if not isinstance(mu, dict):
        raise ReceiptProtocolError("verification.json mu_summary must be an object")
    for key in ("required_disclosure_bits", "provided_disclosure_bits"):
        val = mu.get(key)
        if not isinstance(val, int) or val < 0:
            raise ReceiptProtocolError(f"verification.json mu_summary.{key} must be a non-negative integer")


def write_signed_verification_artifact(
    *,
    out_dir: Path,
    module: str,
    verification: Mapping[str, object],
    private_key: object,
    public_key_hex: str,
    key_id: str,
    trust_manifest_path: Path,
) -> Tuple[Path, Path]:
    """Write verification.json and a TRS-1.0 receipt over it + trust manifest."""

    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    payload = dict(verification)
    payload.setdefault("schema_version", "TM-VERIFY-1")
    payload.setdefault("module", module)

    validate_verification_payload(payload)

    verification_path = out_dir / "verification.json"
    verification_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    receipt_path = out_dir / "verification.receipt.json"
    write_trs10_receipt(
        receipt_path=receipt_path,
        base_dir=out_dir,
        files=[verification_path, trust_manifest_path],
        private_key=private_key,
        public_key_hex=public_key_hex,
        key_id=key_id,
        metadata={"purpose": f"Signed verifier output for {module}"},
    )

    return verification_path, receipt_path
