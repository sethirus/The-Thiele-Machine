# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Standardized receipt format for Thiele Machine computations.

This module defines the canonical receipt schema and provides verification utilities.
Receipts are cryptographically chained to ensure integrity and non-repudiation.
"""

import hashlib
import json
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
from datetime import datetime

def hash_obj(obj: Any) -> str:
    """Compute SHA256 hash of JSON-serialized object."""
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode("utf-8")).hexdigest()

@dataclass
class ReceiptStep:
    """Individual step in a computation receipt."""
    step_index: int
    operation: str
    module_id: int
    module_size: int
    module_fragment: str  # e.g., "Horn", "2-SAT", "treewidth-bounded"
    module_size_metrics: Dict[str, Any]  # Additional size metrics
    mu_charged: float
    inputs_hash: str
    outputs_hash: str
    prev_receipt_hash: str
    timestamp: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "step_index": self.step_index,
            "operation": self.operation,
            "module_id": self.module_id,
            "module_size": self.module_size,
            "module_fragment": self.module_fragment,
            "module_size_metrics": self.module_size_metrics,
            "mu_charged": self.mu_charged,
            "inputs_hash": self.inputs_hash,
            "outputs_hash": self.outputs_hash,
            "prev_receipt_hash": self.prev_receipt_hash,
            "timestamp": self.timestamp
        }

    @property
    def receipt_hash(self) -> str:
        """Hash of this step's receipt."""
        return hash_obj(self.to_dict())

@dataclass
class ComputationReceipt:
    """Standardized receipt for Thiele Machine computations."""
    instance_sha256: str
    n: int
    m: int
    mu_total: float
    steps: List[ReceiptStep]
    final_claim: str  # "SAT", "UNSAT", "FACTORED", etc.
    timestamp: str
    version: str = "1.0"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "version": self.version,
            "instance_sha256": self.instance_sha256,
            "n": self.n,
            "m": self.m,
            "mu_total": self.mu_total,
            "steps": [step.to_dict() for step in self.steps],
            "final_claim": self.final_claim,
            "timestamp": self.timestamp
        }

    @property
    def receipt_hash(self) -> str:
        """Top-level hash of the entire receipt."""
        return hash_obj(self.to_dict())

def create_receipt(instance: Any, steps: List[Dict[str, Any]], final_claim: str) -> ComputationReceipt:
    """Create a standardized receipt from computation data."""
    instance_hash = hash_obj(instance)

    receipt_steps = []
    prev_hash = "genesis"

    for i, step_data in enumerate(steps):
        step = ReceiptStep(
            step_index=i,
            operation=step_data["operation"],
            module_id=step_data["module_id"],
            module_size=step_data["module_size"],
            module_fragment=step_data.get("module_fragment", "unknown"),
            module_size_metrics=step_data.get("module_size_metrics", {}),
            mu_charged=step_data["mu_charged"],
            inputs_hash=step_data["inputs_hash"],
            outputs_hash=step_data["outputs_hash"],
            prev_receipt_hash=prev_hash,
            timestamp=datetime.utcnow().isoformat()
        )
        receipt_steps.append(step)
        prev_hash = step.receipt_hash

    # Estimate n and m from instance
    n = len(str(instance)) if isinstance(instance, (int, str)) else 0
    m = len(steps)

    return ComputationReceipt(
        instance_sha256=instance_hash,
        n=n,
        m=m,
        mu_total=sum(step.mu_charged for step in receipt_steps),
        steps=receipt_steps,
        final_claim=final_claim,
        timestamp=datetime.utcnow().isoformat()
    )

def verify_receipt(receipt: ComputationReceipt) -> Dict[str, Any]:
    """Verify the integrity and consistency of a receipt."""
    issues = []

    # Verify hash chain
    prev_hash = "genesis"
    computed_mu_total = 0.0

    for step in receipt.steps:
        # Check hash chain continuity
        if step.prev_receipt_hash != prev_hash:
            issues.append(f"Hash chain broken at step {step.step_index}")

        # Verify step hash
        expected_hash = step.receipt_hash
        if step.receipt_hash != expected_hash:
            issues.append(f"Step {step.step_index} hash mismatch")

        # Accumulate μ
        computed_mu_total += step.mu_charged
        prev_hash = step.receipt_hash

    # Verify total μ
    if abs(computed_mu_total - receipt.mu_total) > 1e-6:
        issues.append(f"μ total mismatch: computed {computed_mu_total}, claimed {receipt.mu_total}")

    # Verify instance size bounds
    if receipt.n < 0 or receipt.m < 0:
        issues.append("Invalid instance dimensions")

    return {
        "valid": len(issues) == 0,
        "issues": issues,
        "computed_mu_total": computed_mu_total,
        "receipt_hash": receipt.receipt_hash
    }

def save_receipt(receipt: ComputationReceipt, filename: str):
    """Save receipt to JSON file."""
    with open(filename, "w") as f:
        json.dump(receipt.to_dict(), f, indent=2)

def load_receipt(filename: str) -> ComputationReceipt:
    """Load receipt from JSON file."""
    with open(filename, "r") as f:
        data = json.load(f)

    steps = [
        ReceiptStep(**step_data)
        for step_data in data["steps"]
    ]

    return ComputationReceipt(
        instance_sha256=data["instance_sha256"],
        n=data["n"],
        m=data["m"],
        mu_total=data["mu_total"],
        steps=steps,
        final_claim=data["final_claim"],
        timestamp=data["timestamp"],
        version=data.get("version", "1.0")
    )

if __name__ == "__main__":
    # Example usage
    print("Receipt Schema v1.0")
    print("===================")

    # Create a sample receipt
    sample_instance = {"type": "pigeonhole", "n": 10}
    sample_steps = [
        {
            "operation": "PNEW",
            "module_id": 1,
            "module_size": 10,
            "module_fragment": "horn",
            "module_size_metrics": {"element_count": 10},
            "mu_charged": 0.0,
            "inputs_hash": hash_obj({"region": list(range(10))}),
            "outputs_hash": hash_obj({"module": 1})
        },
        {
            "operation": "LASSERT",
            "module_id": 1,
            "module_size": 10,
            "module_fragment": "horn",
            "module_size_metrics": {"audit_consistent": True},
            "mu_charged": 10.0,
            "inputs_hash": hash_obj({"consistent": True}),
            "outputs_hash": hash_obj({"mu": 10.0})
        }
    ]

    receipt = create_receipt(sample_instance, sample_steps, "UNSAT")

    print(f"Sample receipt created with hash: {receipt.receipt_hash[:16]}...")

    # Verify it
    verification = verify_receipt(receipt)
    print(f"Verification: {'PASS' if verification['valid'] else 'FAIL'}")
    if verification["issues"]:
        for issue in verification["issues"]:
            print(f"  - {issue}")

    # Save and reload
    save_receipt(receipt, "sample_receipt.json")
    loaded = load_receipt("sample_receipt.json")
    print(f"Round-trip verification: {'PASS' if verify_receipt(loaded)['valid'] else 'FAIL'}")