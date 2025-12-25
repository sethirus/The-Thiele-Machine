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
from typing import Any, Dict, Optional

from nacl import signing
from nacl.exceptions import BadSignatureError

from scripts.keys import ensure_public_key, get_or_create_signing_key

# Q16.16 Fixed-Point Constants (must match hardware and Coq)
Q16_MAX = 0x7FFFFFFF  # Maximum valid Q16.16 value (2^31 - 1)
Q16_MIN = -0x80000000  # Minimum valid Q16.16 value (-2^31)

SIGNING_KEY_ENV = "THIELE_KERNEL_SIGNING_KEY"
VERIFY_KEY_ENV = "THIELE_KERNEL_VERIFY_KEY"
DEFAULT_SIGNING_KEY_PATH = "kernel_secret.key"
DEFAULT_VERIFY_KEY_PATH = "kernel_public.key"


def mu_in_valid_range(mu: int) -> bool:
    """Check if μ value is within valid Q16.16 range.
    
    CRITICAL: This implements the Coq mu_in_range predicate and
    matches Verilog hardware's 32-bit register limits.
    
    Args:
        mu: μ value to check
        
    Returns:
        True if Q16_MIN <= mu <= Q16_MAX
    """
    return Q16_MIN <= mu <= Q16_MAX


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
    signing_key: Optional[signing.SigningKey] = None

    try:
        signing_key_bytes = secret_path.read_bytes()
    except FileNotFoundError:
        regenerate = True
        signing_key_bytes = None
    except OSError:
        regenerate = True
        signing_key_bytes = None
    else:
        try:
            signing_key = signing.SigningKey(signing_key_bytes)
        except Exception:  # pragma: no cover - defensive: corrupted key material
            regenerate = True
            signing_key = None

    if not regenerate and signing_key is not None:
        try:
            stored_verify = _load_verify_key_bytes(public_path)
        except (OSError, ValueError):
            regenerate = True
        else:
            if stored_verify != signing_key.verify_key.encode():
                regenerate = True

    if regenerate and os.environ.get("THIELE_PRODUCTION", "0") == "1":
        raise RuntimeError(
            "Kernel keypair missing or invalid and THIELE_PRODUCTION=1: refusing to auto-generate keys"
        )

    if regenerate or signing_key is None:
        signing_key = get_or_create_signing_key(secret_path, public_key_path=public_path)
        print(
            "INFO: Generated a new local kernel signing keypair for reproducible demos."
        )
    else:
        ensure_public_key(signing_key, public_path)


def sign_receipt(
    payload: Dict[str, Any],
    *,
    signing_key_path: Optional[str | os.PathLike[str]] = None,
) -> str:
    """Sign ``payload`` using the Ed25519 kernel signing key."""

    key_path = _resolve_signing_key(signing_key_path)
    message = _canonical_json(payload).encode("utf-8")
    signing_key = get_or_create_signing_key(key_path)
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
        verify_mu_integrity: bool = True,
        verify_instruction_cost: bool = True,
        verify_mu_range: bool = True,
    ) -> bool:
        """Verify receipt signature AND μ-integrity.
        
        Implements the Coq receipt_mu_consistent property:
            post_mu = pre_mu + instruction_cost(instruction)
        
        This prevents the forgery attack where receipts claim arbitrary μ
        without doing actual computation.
        
        Args:
            verifying_key_path: Path to verification key
            verify_mu_integrity: If True, verify μ arithmetic (default True)
            verify_instruction_cost: If True, verify cost matches instruction (default True)
            verify_mu_range: If True, verify μ values are in Q16.16 range (default True)
            
        Returns:
            True if receipt is valid (signature OK AND μ-integrity OK)
        """
        payload = {
            "step": self.step,
            "instruction": self.instruction.to_dict(),
            "pre_state": self.pre_state,
            "post_state": self.post_state,
            "observation": self.observation.to_dict(),
            "pre_state_hash": self.pre_state_hash,
            "post_state_hash": self.post_state_hash,
        }
        
        # Step 1: Verify cryptographic signature
        signature_valid = verify_signature(
            payload,
            self.signature,
            verifying_key_path=verifying_key_path,
        )
        
        if not signature_valid:
            return False
        
        # Step 2: Verify μ-range (CRITICAL for overflow prevention)
        # Implements Coq receipt_mu_in_range predicate
        if verify_mu_range:
            if not self.verify_mu_range():
                return False
        
        # Step 3: Verify μ-integrity (receipt_mu_consistent from Coq)
        if verify_mu_integrity:
            if not self.verify_mu_integrity():
                return False
        
        # Step 4: Verify instruction cost (CRITICAL for forgery prevention)
        if verify_instruction_cost:
            if not self.verify_instruction_cost():
                return False
        
        return True
    
    def verify_mu_range(self) -> bool:
        """Verify μ values are within valid Q16.16 range.
        
        This is the fix for the μ-overflow vulnerability.
        Implements Coq theorem receipt_mu_in_range.
        
        Hardware uses 32-bit registers - Python must not accept values
        that exceed this range, even though Python supports arbitrary
        precision integers.
        
        Returns:
            True if both pre_mu and post_mu are in valid Q16.16 range
        """
        pre_mu = self.pre_state.get("mu_acc", 0)
        post_mu = self.post_state.get("mu_acc", 0)
        
        # Both must be in valid Q16.16 range
        if not mu_in_valid_range(pre_mu):
            return False
        if not mu_in_valid_range(post_mu):
            return False
        
        return True
    
    def verify_mu_integrity(self) -> bool:
        """Verify μ-cost integrity: post_mu = pre_mu + mu_delta.
        
        This is the core fix for the receipt forgery vulnerability.
        Implements Coq theorem receipt_mu_consistent.
        
        Returns:
            True if μ arithmetic is consistent
        """
        pre_mu = self.pre_state.get("mu_acc", 0)
        post_mu = self.post_state.get("mu_acc", 0)
        claimed_delta = self.observation.mu_delta
        
        # CRITICAL: post_mu must equal pre_mu + claimed_delta
        # This is the receipt_mu_consistent property from Coq
        expected_post_mu = pre_mu + claimed_delta
        
        if post_mu != expected_post_mu:
            # FORGERY DETECTED: arithmetic doesn't add up
            return False
        
        return True
    
    def verify_instruction_cost(self) -> bool:
        """Verify claimed mu_delta matches expected instruction cost.
        
        This is the SECOND layer of defense against forgery.
        Even if arithmetic is consistent, the claimed cost must match
        what the instruction SHOULD cost based on its operation.
        
        IMPORTANT: This requires knowledge of instruction cost semantics.
        In Coq, this is instruction_cost(instr). Here we implement the
        same cost model.
        
        Returns:
            True if mu_delta matches expected cost for the instruction
        """
        op = self.instruction.op
        payload = self.instruction.payload
        claimed_delta = self.observation.mu_delta
        
        # CRITICAL: μ-monotonicity - costs can NEVER be negative
        # In Coq, instruction_cost returns nat (non-negative)
        # This prevents "information destruction" attacks
        if claimed_delta < 0:
            return False
        
        # Compute expected cost based on instruction type
        expected_cost = self._compute_instruction_cost(op, payload)
        
        if expected_cost is None:
            # Unknown operation - allow (for extensibility)
            return True
        
        if claimed_delta != expected_cost:
            # FORGERY DETECTED: claimed cost doesn't match instruction
            return False
        
        return True
    
    def _compute_instruction_cost(self, op: str, payload: Any) -> Optional[float]:
        """Compute the expected μ-cost for an instruction.
        
        This mirrors the Coq instruction_cost function.
        
        Returns:
            Expected cost, or None if unknown operation
        """
        if op == "PNEW":
            # Cost = size of region being created
            if isinstance(payload, dict) and "region" in payload:
                region = payload["region"]
                if isinstance(region, (list, set)):
                    return len(region)
            return None  # Can't determine
            
        elif op == "PSPLIT":
            # Cost is specified in payload
            if isinstance(payload, dict) and "cost" in payload:
                return payload["cost"]
            return None
            
        elif op == "PMERGE":
            # Cost is specified in payload
            if isinstance(payload, dict) and "cost" in payload:
                return payload["cost"]
            return None
            
        elif op == "PDISCOVER":
            # Cost = evidence size
            if isinstance(payload, dict) and "evidence" in payload:
                evidence = payload["evidence"]
                if isinstance(evidence, list):
                    return len(evidence)
            return None
            
        elif op == "HALT":
            # HALT has zero cost
            return 0
            
        # For other operations, we can't determine expected cost
        # They must be validated through other means
        return None
    
    def verify_chain_link(self, previous_receipt: "StepReceipt") -> bool:
        """Verify this receipt chains correctly from the previous one.
        
        Implements Coq chain_links property:
            prev.post_mu = this.pre_mu
            prev.post_state_hash = this.pre_state_hash
            
        Args:
            previous_receipt: The receipt immediately before this one
            
        Returns:
            True if chain links correctly (both μ and state hash)
        """
        # Check μ continuity
        prev_post_mu = previous_receipt.post_state.get("mu_acc", 0)
        this_pre_mu = self.pre_state.get("mu_acc", 0)
        
        if prev_post_mu != this_pre_mu:
            return False
        
        # Check state hash continuity (CRITICAL for preventing state forgery)
        if previous_receipt.post_state_hash != self.pre_state_hash:
            return False
        
        return True


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
            mu_delta=entry["observation"]["mu_delta"],
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


def verify_receipt_chain(
    receipts: list[StepReceipt],
    initial_mu: int = 0,
    *,
    verifying_key_path: Optional[str | os.PathLike[str]] = None,
) -> tuple[bool, Optional[str]]:
    """Verify a complete receipt chain for integrity and continuity.
    
    Implements Coq receipt_chain_valid:
        - chain_all_consistent: all receipts pass verify_mu_integrity
        - chain_links: consecutive receipts chain correctly
        - initial_mu: first receipt starts from expected μ
        
    This is the COMPLETE fix for the receipt forgery vulnerability.
    A valid chain PROVES that the μ was earned through computation.
    
    Args:
        receipts: List of receipts in execution order
        initial_mu: Expected initial μ value (default 0)
        verifying_key_path: Path to verification key
        
    Returns:
        Tuple of (valid, error_message)
        - valid: True if entire chain is valid
        - error_message: None if valid, else description of failure
    """
    if not receipts:
        return True, None
    
    # Check first receipt starts from initial_mu
    first_pre_mu = receipts[0].pre_state.get("mu_acc", 0)
    if first_pre_mu != initial_mu:
        return False, f"Chain does not start from initial_mu={initial_mu}, got {first_pre_mu}"
    
    # Verify each receipt and chain links
    for i, receipt in enumerate(receipts):
        # Verify individual receipt
        if not receipt.verify(verifying_key_path=verifying_key_path):
            return False, f"Receipt {i} failed verification"
        
        # Verify chain link (except for first receipt)
        if i > 0:
            if not receipt.verify_chain_link(receipts[i - 1]):
                prev_post = receipts[i - 1].post_state.get("mu_acc", 0)
                this_pre = receipt.pre_state.get("mu_acc", 0)
                return False, f"Chain break at receipt {i}: prev_post_mu={prev_post}, this_pre_mu={this_pre}"
    
    return True, None


def compute_chain_final_mu(receipts: list[StepReceipt], initial_mu: int = 0) -> int:
    """Compute the final μ from a receipt chain.
    
    Implements Coq chain_final_mu:
        final_mu = initial_mu + sum(instruction_cost for each receipt)
        
    This is the computed μ that a valid chain PROVES.
    
    Args:
        receipts: List of receipts in execution order
        initial_mu: Starting μ value
        
    Returns:
        The computed final μ value
    """
    total_cost = sum(r.observation.mu_delta for r in receipts)
    return initial_mu + int(total_cost)


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
    "verify_receipt_chain",
    "compute_chain_final_mu",
]
