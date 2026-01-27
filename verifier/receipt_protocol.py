import json
import hashlib
from pathlib import Path
from typing import Tuple
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization


def ed25519_keypair() -> Tuple[Ed25519PrivateKey, str]:
    private_key = Ed25519PrivateKey.generate()
    public_hex = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()
    return private_key, public_hex


def _sha256_hex(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_trs10_receipt(receipt_path: Path, base_dir: Path, files: list, private_key: Ed25519PrivateKey, public_key_hex: str, key_id: str) -> None:
    file_entries = []
    for p in files:
        rel = Path(p).name
        file_entries.append({"path": rel, "sha256": _sha256_hex(p)})

    # Create a canonical digest
    canonical = json.dumps(sorted(file_entries, key=lambda f: f["path"]), sort_keys=True)
    global_digest = hashlib.sha256(canonical.encode("utf-8")).hexdigest()
    signature = private_key.sign(global_digest.encode("utf-8")).hex()

    receipt = {
        "version": "TRS-1.0",
        "files": file_entries,
        "global_digest": global_digest,
        "sig_scheme": "ed25519",
        "signature": signature,
        "public_key": public_key_hex,
        "key_id": key_id,
    }

    receipt_path.write_text(json.dumps(receipt, sort_keys=True) + "\n", encoding="utf-8")


def write_trust_manifest(path: Path, key_id: str, public_key_hex: str) -> None:
    manifest = {"trusted_keys": {key_id: {"public_key": public_key_hex, "patterns": ["*"]}}}
    path.write_text(json.dumps(manifest), encoding="utf-8")
