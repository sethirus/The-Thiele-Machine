#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Thiele Nonlocal Receipt

Extended receipt format for nonlocal box search with Thiele VM integration.
All searches must produce verifiable VM traces and μ-ledger data.

Receipt Format:
    - vm_mu_discovery: μ-cost for partition discovery
    - vm_mu_execution: μ-cost for instruction execution
    - partition_trace: Sequence of VM opcodes and masks
    - vm_canonical_hash: Hash of VM state trace
    - falsifiable: True if receipt can be independently verified
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

import numpy as np


@dataclass
class PartitionTraceEntry:
    """Single entry in partition trace."""
    opcode: str
    operands: Dict[str, Any]
    mu_discovery_delta: int
    mu_execution_delta: int
    partition_mask: int
    pc: int
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "opcode": self.opcode,
            "operands": self.operands,
            "mu_discovery_delta": self.mu_discovery_delta,
            "mu_execution_delta": self.mu_execution_delta,
            "partition_mask": self.partition_mask,
            "pc": self.pc
        }
    
    @staticmethod
    def from_dict(d: Dict[str, Any]) -> 'PartitionTraceEntry':
        return PartitionTraceEntry(
            opcode=d["opcode"],
            operands=d["operands"],
            mu_discovery_delta=d["mu_discovery_delta"],
            mu_execution_delta=d["mu_execution_delta"],
            partition_mask=d["partition_mask"],
            pc=d["pc"]
        )


@dataclass
class ThieleNonlocalReceipt:
    """Extended receipt for Thiele nonlocal box search."""
    
    # Required VM fields
    vm_mu_discovery: int
    vm_mu_execution: int
    partition_trace: List[PartitionTraceEntry]
    vm_canonical_hash: str
    
    # Box data
    shape: Tuple[int, int, int, int]
    box_hash: str
    bell_value: float
    is_extremal: bool
    
    # Search metadata
    seed: int
    timestamp: str
    runtime_seconds: float
    
    # Optional data
    classification: str = "unknown"
    structure_verdict: str = "unknown"
    geometric_signature: Optional[Dict[str, Any]] = None
    
    # Falsifiability flag
    falsifiable: bool = True
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "vm_mu_discovery": self.vm_mu_discovery,
            "vm_mu_execution": self.vm_mu_execution,
            "partition_trace": [e.to_dict() for e in self.partition_trace],
            "vm_canonical_hash": self.vm_canonical_hash,
            "shape": list(self.shape),
            "box_hash": self.box_hash,
            "bell_value": self.bell_value,
            "is_extremal": self.is_extremal,
            "seed": self.seed,
            "timestamp": self.timestamp,
            "runtime_seconds": self.runtime_seconds,
            "classification": self.classification,
            "structure_verdict": self.structure_verdict,
            "geometric_signature": self.geometric_signature,
            "falsifiable": self.falsifiable
        }
    
    @staticmethod
    def from_dict(d: Dict[str, Any]) -> 'ThieleNonlocalReceipt':
        return ThieleNonlocalReceipt(
            vm_mu_discovery=d["vm_mu_discovery"],
            vm_mu_execution=d["vm_mu_execution"],
            partition_trace=[PartitionTraceEntry.from_dict(e) for e in d["partition_trace"]],
            vm_canonical_hash=d["vm_canonical_hash"],
            shape=tuple(d["shape"]),
            box_hash=d["box_hash"],
            bell_value=d["bell_value"],
            is_extremal=d["is_extremal"],
            seed=d["seed"],
            timestamp=d["timestamp"],
            runtime_seconds=d["runtime_seconds"],
            classification=d.get("classification", "unknown"),
            structure_verdict=d.get("structure_verdict", "unknown"),
            geometric_signature=d.get("geometric_signature"),
            falsifiable=d.get("falsifiable", True)
        )
    
    def compute_trace_hash(self) -> str:
        """Compute canonical hash from partition trace."""
        trace_data = json.dumps([e.to_dict() for e in self.partition_trace], sort_keys=True)
        return hashlib.sha256(trace_data.encode()).hexdigest()[:16]
    
    def verify_integrity(self) -> Tuple[bool, str]:
        """Verify receipt integrity."""
        # Check that trace hash matches stored hash
        computed_hash = self.compute_trace_hash()
        if computed_hash != self.vm_canonical_hash:
            return False, f"Hash mismatch: expected {self.vm_canonical_hash}, got {computed_hash}"
        
        # Check that μ-costs sum correctly
        total_discovery = sum(e.mu_discovery_delta for e in self.partition_trace)
        total_execution = sum(e.mu_execution_delta for e in self.partition_trace)
        
        if total_discovery != self.vm_mu_discovery:
            return False, f"μ-discovery mismatch: expected {self.vm_mu_discovery}, got {total_discovery}"
        
        if total_execution != self.vm_mu_execution:
            return False, f"μ-execution mismatch: expected {self.vm_mu_execution}, got {total_execution}"
        
        return True, "Receipt integrity verified"


def save_receipt(receipt: ThieleNonlocalReceipt, filepath: str) -> None:
    """Save receipt to JSON file."""
    with open(filepath, 'w') as f:
        json.dump(receipt.to_dict(), f, indent=2)


def load_receipt(filepath: str) -> ThieleNonlocalReceipt:
    """Load receipt from JSON file."""
    with open(filepath, 'r') as f:
        data = json.load(f)
    return ThieleNonlocalReceipt.from_dict(data)
