from __future__ import annotations

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey


def load_public_key_from_hex(hex_text: str) -> Ed25519PublicKey:
    raw = bytes.fromhex(hex_text.strip())
    if len(raw) != 32:
        raise ValueError("Ed25519 public key hex must encode exactly 32 bytes")
    return Ed25519PublicKey.from_public_bytes(raw)


def verify_digest_signature(*, public_key_hex: str, signature_hex: str, digest_hex: str) -> None:
    public_key = load_public_key_from_hex(public_key_hex)
    public_key.verify(bytes.fromhex(signature_hex), digest_hex.encode("utf-8"))