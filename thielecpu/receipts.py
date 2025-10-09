"""Receipt helpers for instrumented Thiele Machine executions."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import hmac
import json
import os
from typing import Any, Dict, Optional

DEFAULT_KERNEL_SECRET_ENV = "THIELE_KERNEL_SECRET"
DEFAULT_KERNEL_SECRET = b"THIELE_KERNEL_DEMO_SECRET"


def _canonical_json(data: Dict[str, Any]) -> str:
    """Return a stable JSON encoding for hashing and signing."""
    return json.dumps(data, sort_keys=True, separators=(",", ":"))


def hash_snapshot(snapshot: Dict[str, Any]) -> str:
    """Compute a SHA-256 hash over a state snapshot."""
    payload = _canonical_json(snapshot).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _load_kernel_secret(secret: Optional[bytes] = None) -> bytes:
    if secret is not None:
        return secret
    env_value = os.environ.get(DEFAULT_KERNEL_SECRET_ENV)
    if env_value:
        return env_value.encode("utf-8")
    return DEFAULT_KERNEL_SECRET


def sign_receipt(payload: Dict[str, Any], *, secret: Optional[bytes] = None) -> str:
    """Compute an HMAC signature for the given receipt payload."""
    key = _load_kernel_secret(secret)
    data = _canonical_json(payload).encode("utf-8")
    return hmac.new(key, data, hashlib.sha256).hexdigest()


def verify_signature(payload: Dict[str, Any], signature: str, *, secret: Optional[bytes] = None) -> bool:
    """Verify a signature against the payload."""
    expected = sign_receipt(payload, secret=secret)
    return hmac.compare_digest(expected, signature)


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
    mu_delta: int
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
        secret: Optional[bytes] = None,
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
        signature = sign_receipt(payload, secret=secret)
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

    def verify(self, *, secret: Optional[bytes] = None) -> bool:
        payload = {
            "step": self.step,
            "instruction": self.instruction.to_dict(),
            "pre_state": self.pre_state,
            "post_state": self.post_state,
            "observation": self.observation.to_dict(),
            "pre_state_hash": self.pre_state_hash,
            "post_state_hash": self.post_state_hash,
        }
        return verify_signature(payload, self.signature, secret=secret)


def load_receipts(path: os.PathLike[str] | str) -> list[StepReceipt]:
    """Load receipts from disk."""
    with open(path, "r", encoding="utf-8") as handle:
        raw = json.load(handle)
    receipts: list[StepReceipt] = []
    for entry in raw:
        instruction = InstructionWitness(**entry["instruction"])
        observation = StepObservation(
            event=entry["observation"].get("event"),
            mu_delta=int(entry["observation"]["mu_delta"]),
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
    "sign_receipt",
    "verify_signature",
    "load_receipts",
]
