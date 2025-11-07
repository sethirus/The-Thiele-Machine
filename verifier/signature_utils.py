"""Shared helpers for verifying signed Thiele receipts."""

from __future__ import annotations

import fnmatch
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple


class SignatureVerificationError(Exception):
    """Raised when a receipt signature cannot be validated."""


class TrustManifestError(Exception):
    """Raised when the trust manifest cannot authorise a receipt."""


class TrustContextError(Exception):
    """Raised when the trust configuration is invalid."""


try:  # Prefer PyNaCl when available (shipped with the project requirements).
    from nacl import exceptions as nacl_exceptions
    from nacl import signing as nacl_signing
except ImportError:  # pragma: no cover - exercised when PyNaCl missing.
    nacl_exceptions = None
    nacl_signing = None

try:  # Fallback to cryptography if PyNaCl is unavailable.
    from cryptography.hazmat.primitives.asymmetric import ed25519 as crypto_ed25519
except ImportError:  # pragma: no cover - exercised when cryptography missing.
    crypto_ed25519 = None


def _decode_hex(label: str, value: str, expected_len: Optional[int] = None) -> bytes:
    """Decode hex-encoded ``value`` and enforce the optional ``expected_len``."""

    if not isinstance(value, str):
        raise SignatureVerificationError(f"{label} must be a hex string")

    try:
        raw = bytes.fromhex(value)
    except ValueError as exc:  # pragma: no cover - defensive branch.
        raise SignatureVerificationError(f"{label} is not valid hex") from exc

    if expected_len is not None and len(raw) != expected_len:
        raise SignatureVerificationError(
            f"{label} length mismatch: expected {expected_len} bytes, got {len(raw)}"
        )

    return raw


def verify_ed25519_signature(global_digest: str, signature_hex: str, public_key_hex: str) -> None:
    """Verify ``signature_hex`` over ``global_digest`` using ``public_key_hex``."""

    message = global_digest.encode("utf-8")
    signature = _decode_hex("signature", signature_hex, expected_len=64)
    public_key = _decode_hex("public key", public_key_hex, expected_len=32)

    if nacl_signing is not None:
        try:
            nacl_signing.VerifyKey(public_key).verify(message, signature)
            return
        except nacl_exceptions.BadSignatureError as exc:  # pragma: no cover - handled in tests.
            raise SignatureVerificationError("Ed25519 signature invalid") from exc

    if crypto_ed25519 is not None:
        try:
            key = crypto_ed25519.Ed25519PublicKey.from_public_bytes(public_key)
            key.verify(signature, message)
            return
        except Exception as exc:  # pragma: no cover - exercised via tests when crypto backend used.
            raise SignatureVerificationError("Ed25519 signature invalid") from exc

    raise SignatureVerificationError(
        "No Ed25519 verification backend available; install PyNaCl or cryptography"
    )


@dataclass(frozen=True)
class TrustEntry:
    """Single trust rule from the manifest."""

    key_id: str
    public_key: str
    patterns: List[str]
    comment: Optional[str] = None

    def matches(self, candidate: str) -> bool:
        return any(fnmatch.fnmatch(candidate, pattern) for pattern in self.patterns)


class TrustManifest:
    """In-memory representation of ``trust_manifest.json``."""

    def __init__(self, path: Path, entries: Iterable[TrustEntry]):
        self.path = path
        self.entries: List[TrustEntry] = list(entries)
        self._entries_by_id: Dict[str, TrustEntry] = {
            entry.key_id: entry for entry in self.entries if entry.key_id
        }

    @property
    def base_dir(self) -> Path:
        return self.path.parent

    def matching_entries(self, receipt_path: Path) -> List[TrustEntry]:
        """Return entries whose patterns apply to ``receipt_path``."""

        matches: List[TrustEntry] = []
        receipt_path = receipt_path.resolve()

        try:
            relative = receipt_path.relative_to(self.base_dir.resolve()).as_posix()
        except ValueError:
            relative = None

        candidate_names = {receipt_path.name}
        if relative:
            candidate_names.add(relative)

        for entry in self.entries:
            patterns = entry.patterns or ["*"]
            for candidate in candidate_names:
                if entry.matches(candidate):
                    matches.append(entry)
                    break

        return matches

    def select_entry(self, receipt_path: Path, receipt: Dict[str, object]) -> TrustEntry:
        """Resolve the trust entry for ``receipt`` at ``receipt_path``."""

        key_id = str(receipt.get("key_id", "")) if receipt.get("key_id") else None

        if key_id:
            entry = self._entries_by_id.get(key_id)
            if entry is None:
                raise TrustManifestError(
                    f"Key id '{key_id}' in receipt is not present in trust manifest"
                )

            if not entry.matches(receipt_path.name) and not entry.matches(
                receipt_path.resolve().as_posix()
            ):
                # Also consider manifest-relative matches.
                try:
                    relative = receipt_path.resolve().relative_to(self.base_dir.resolve()).as_posix()
                except ValueError:
                    relative = None

                if not (relative and entry.matches(relative)):
                    raise TrustManifestError(
                        f"Receipt path does not match patterns declared for key id '{key_id}'"
                    )

            return entry

        matches = self.matching_entries(receipt_path)
        if not matches:
            raise TrustManifestError(
                f"No trusted keys apply to receipt {receipt_path.name}"
            )

        if len(matches) == 1:
            return matches[0]

        receipt_pubkey = receipt.get("public_key")
        if isinstance(receipt_pubkey, str):
            for entry in matches:
                if entry.public_key.lower() == receipt_pubkey.lower():
                    return entry

        raise TrustManifestError(
            f"Multiple trust entries match {receipt_path.name}; add 'key_id' to receipt"
        )


def load_trust_manifest(path: Path) -> TrustManifest:
    """Parse ``trust_manifest.json``."""

    if not path.exists():
        raise FileNotFoundError(path)

    with open(path, "r", encoding="utf-8") as handle:
        data = json.load(handle)

    trusted_keys = data.get("trusted_keys")
    if not isinstance(trusted_keys, dict):
        raise TrustManifestError("trust_manifest.json must contain a 'trusted_keys' object")

    entries: List[TrustEntry] = []
    for key_id, payload in trusted_keys.items():
        if not isinstance(payload, dict):
            raise TrustManifestError(f"trusted_keys['{key_id}'] must be an object")

        public_key = payload.get("public_key")
        if not isinstance(public_key, str):
            raise TrustManifestError(f"trusted_keys['{key_id}'].public_key must be a hex string")

        patterns = payload.get("patterns") or payload.get("paths") or ["*"]
        if isinstance(patterns, str):
            patterns = [patterns]
        if not isinstance(patterns, list) or not all(isinstance(p, str) for p in patterns):
            raise TrustManifestError(
                f"trusted_keys['{key_id}'].patterns must be a list of glob strings"
            )

        entries.append(
            TrustEntry(
                key_id=key_id,
                public_key=public_key,
                patterns=[p if p else "*" for p in patterns],
                comment=payload.get("comment"),
            )
        )

    return TrustManifest(path, entries)


def resolve_trust(
    manifest_path: Optional[str], trusted_pubkey: Optional[str]
) -> Tuple[Optional[TrustManifest], Optional[str]]:
    """Load the trust manifest and/or explicit trusted public key."""

    manifest: Optional[TrustManifest] = None
    if manifest_path:
        try:
            manifest = load_trust_manifest(Path(manifest_path))
        except FileNotFoundError as exc:
            raise TrustContextError(f"trust manifest not found: {manifest_path}") from exc
        except TrustManifestError as exc:
            raise TrustContextError(str(exc)) from exc

    pubkey = None
    if trusted_pubkey:
        try:
            pubkey_bytes = bytes.fromhex(trusted_pubkey)
        except ValueError as exc:
            raise TrustContextError("trusted public key must be hex-encoded") from exc

        if len(pubkey_bytes) != 32:
            raise TrustContextError("trusted public key must be 32 bytes (64 hex chars)")

        pubkey = trusted_pubkey.lower()

    return manifest, pubkey

