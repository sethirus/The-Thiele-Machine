# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Receipt helpers for instrumented Thiele Machine executions."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import string
import subprocess
import sys
from typing import Any, Dict, Optional

from nacl import signing
from nacl.exceptions import BadSignatureError

SIGNING_KEY_ENV = "THIELE_KERNEL_SIGNING_KEY"
VERIFY_KEY_ENV = "THIELE_KERNEL_VERIFY_KEY"
DEFAULT_SIGNING_KEY_PATH = "kernel_secret.key"
DEFAULT_VERIFY_KEY_PATH = "kernel_public.key"


def _canonical_json(data: Dict[str, Any]) -> str:
    """Return a stable JSON encoding for hashing and signing."""
    return json.dumps(data, sort_keys=True, separators=(",", ":"))


def hash_snapshot(snapshot: Dict[str, Any]) -> str:
    """Compute a SHA-256 hash over a state snapshot."""
    payload = _canonical_json(snapshot).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _resolve_signing_key(path: Optional[str | os.PathLike[str]] = None) -> Path:
    candidate = path if path is not None else os.environ.get(SIGNING_KEY_ENV, DEFAULT_SIGNING_KEY_PATH)
    return Path(candidate).expanduser()


def _resolve_verify_key(path: Optional[str | os.PathLike[str]] = None) -> Path:
    candidate = path if path is not None else os.environ.get(VERIFY_KEY_ENV, DEFAULT_VERIFY_KEY_PATH)
    return Path(candidate).expanduser()


def _load_verify_key_bytes(path: Path) -> bytes:
    """Load the verification key, supporting both binary and hex-encoded files."""

    raw = path.read_bytes()
    stripped = raw.strip()
    if not stripped:
        raise ValueError(f"Verification key at {path} is empty")

    try:
        text = stripped.decode("ascii")
    except UnicodeDecodeError:
        return stripped

    if len(text) % 2 == 0 and all(ch in string.hexdigits for ch in text):
        try:
            return bytes.fromhex(text)
        except ValueError:
            pass

    return stripped


def ensure_kernel_keys(
    *,
    signing_key_path: Optional[str | os.PathLike[str]] = None,
    verifying_key_path: Optional[str | os.PathLike[str]] = None,
) -> None:
    """Ensure the deterministic kernel signing keypair is healthy on disk."""

    secret_path = _resolve_signing_key(signing_key_path)
    public_path = _resolve_verify_key(verifying_key_path)

    regenerate = False
    signing_key_bytes: Optional[bytes] = None

    if not secret_path.exists() or not public_path.exists():
        regenerate = True
    else:
        try:
            signing_key_bytes = secret_path.read_bytes()
        except OSError:
            regenerate = True
        else:
            if len(signing_key_bytes) != 32:
                regenerate = True
            else:
                try:
                    signing_key = signing.SigningKey(signing_key_bytes)
                except Exception:  # pragma: no cover - defensive: corrupted key material
                    regenerate = True
                else:
                    derived_verify = signing_key.verify_key.encode()
                    try:
                        stored_verify = _load_verify_key_bytes(public_path)
                    except (OSError, ValueError):
                        regenerate = True
                    else:
                        if stored_verify != derived_verify:
                            regenerate = True

    if not regenerate:
        return

    # In production mode, do not auto-generate key material. Operators must
    # provision signing keys explicitly to avoid accidental key rotation or
    # test-key reuse. Set THIELE_PRODUCTION=1 in the environment to enable
    # this behaviour. Tests and local dev will continue to auto-generate.
    if os.environ.get("THIELE_PRODUCTION", "0") == "1":
        raise RuntimeError(
            "Kernel keypair missing or invalid and THIELE_PRODUCTION=1: refusing to auto-generate keys"
        )

    generator = Path(__file__).resolve().parent.parent / "scripts" / "generate_kernel_keys.py"
    cmd = [
        sys.executable,
        str(generator),
        "--secret-path",
        str(secret_path),
        "--public-path",
        str(public_path),
        "--deterministic-test-key",
        "--force",
    ]
    subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    print(
        "INFO: Default deterministic keypair was missing or corrupt. Regenerated to ensure reproducibility."
    )


def sign_receipt(
    payload: Dict[str, Any],
    *,
    signing_key_path: Optional[str | os.PathLike[str]] = None,
) -> str:
    """Sign ``payload`` using the Ed25519 kernel signing key."""

    key_path = _resolve_signing_key(signing_key_path)
    message = _canonical_json(payload).encode("utf-8")
    signing_key = signing.SigningKey(key_path.read_bytes())
    signature = signing_key.sign(message).signature
    return signature.hex()


def verify_signature(
    payload: Dict[str, Any],
    signature: str,
    *,
    verifying_key_path: Optional[str | os.PathLike[str]] = None,
) -> bool:
    """Verify ``signature`` for ``payload`` using the kernel public key."""

    key_path = _resolve_verify_key(verifying_key_path)
    verify_material = _load_verify_key_bytes(key_path)
    verify_key = signing.VerifyKey(verify_material)
    message = _canonical_json(payload).encode("utf-8")
    try:
        verify_key.verify(message, bytes.fromhex(signature))
        return True
    except BadSignatureError:
        return False


@dataclass
class WitnessState:
    """Lightweight state mirrored by the Coq development."""

    pc: int = 0
    status: int = 0
    mu_acc: int = 0
    cert_addr: str = ""

    def snapshot(self) -> Dict[str, Any]:
        return {
            "pc": self.pc,
            "status": self.status,
            "mu_acc": self.mu_acc,
            "cert_addr": self.cert_addr,
        }


@dataclass
class StepObservation:
    """Observation accompanying a step receipt."""

    event: Optional[Dict[str, str]]
    mu_delta: float
    cert: Dict[str, Any]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "event": self.event,
            "mu_delta": self.mu_delta,
            "cert": self.cert,
        }


@dataclass
class InstructionWitness:
    """Normalised instruction used for receipts and Coq replay."""

    op: str
    payload: Any

    def to_dict(self) -> Dict[str, Any]:
        return {"op": self.op, "payload": self.payload}


@dataclass
class StepReceipt:
    """Full receipt for a single VM step."""

    step: int
    instruction: InstructionWitness
    pre_state: Dict[str, Any]
    post_state: Dict[str, Any]
    observation: StepObservation
    pre_state_hash: str
    post_state_hash: str
    signature: str

    @classmethod
    def assemble(
        cls,
        step: int,
        instruction: InstructionWitness,
        pre_state: WitnessState,
        post_state: WitnessState,
        observation: StepObservation,
        *,
        signing_key_path: Optional[str | os.PathLike[str]] = None,
    ) -> "StepReceipt":
        pre_snapshot = pre_state.snapshot()
        post_snapshot = post_state.snapshot()
        payload = {
            "step": step,
            "instruction": instruction.to_dict(),
            "pre_state": pre_snapshot,
            "post_state": post_snapshot,
            "observation": observation.to_dict(),
        }
        pre_hash = hash_snapshot(pre_snapshot)
        post_hash = hash_snapshot(post_snapshot)
        payload["pre_state_hash"] = pre_hash
        payload["post_state_hash"] = post_hash
        signature = sign_receipt(payload, signing_key_path=signing_key_path)
        return cls(
            step=step,
            instruction=instruction,
            pre_state=pre_snapshot,
            post_state=post_snapshot,
            observation=observation,
            pre_state_hash=pre_hash,
            post_state_hash=post_hash,
            signature=signature,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "step": self.step,
            "instruction": self.instruction.to_dict(),
            "pre_state": self.pre_state,
            "post_state": self.post_state,
            "observation": self.observation.to_dict(),
            "pre_state_hash": self.pre_state_hash,
            "post_state_hash": self.post_state_hash,
            "signature": self.signature,
        }

    def verify(
        self,
        *,
        verifying_key_path: Optional[str | os.PathLike[str]] = None,
    ) -> bool:
        payload = {
            "step": self.step,
            "instruction": self.instruction.to_dict(),
            "pre_state": self.pre_state,
            "post_state": self.post_state,
            "observation": self.observation.to_dict(),
            "pre_state_hash": self.pre_state_hash,
            "post_state_hash": self.post_state_hash,
        }
        return verify_signature(
            payload,
            self.signature,
            verifying_key_path=verifying_key_path,
        )


def load_receipts(path: os.PathLike[str] | str) -> list[StepReceipt]:
    """Load receipts from disk."""
    with open(path, "r", encoding="utf-8") as handle:
        raw = json.load(handle)
    if isinstance(raw, dict) and "steps" in raw:
        entries = raw["steps"]
    else:
        entries = raw
    receipts: list[StepReceipt] = []
    for entry in entries:
        instruction = InstructionWitness(**entry["instruction"])
        observation = StepObservation(
            event=entry["observation"].get("event"),
            mu_delta=float(entry["observation"]["mu_delta"]),
            cert=entry["observation"]["cert"],
        )
        receipt = StepReceipt(
            step=int(entry["step"]),
            instruction=instruction,
            pre_state=entry["pre_state"],
            post_state=entry["post_state"],
            observation=observation,
            pre_state_hash=entry["pre_state_hash"],
            post_state_hash=entry["post_state_hash"],
            signature=entry["signature"],
        )
        receipts.append(receipt)
    return receipts


__all__ = [
    "WitnessState",
    "StepObservation",
    "InstructionWitness",
    "StepReceipt",
    "hash_snapshot",
    "ensure_kernel_keys",
    "sign_receipt",
    "verify_signature",
    "load_receipts",
]
