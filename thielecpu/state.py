# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Machine state and partition operations.

This module implements the canonical state representation as defined in
spec/thiele_machine_spec.md for isomorphism with Verilog RTL and Coq proofs.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from typing import Callable, Set, Tuple, Dict, List, Any

try:
    from .isa import CSR
    from .memory import RegionGraph
    from ._types import ModuleId
except ImportError:
    # Handle running as script
    import sys
    import os
    sys.path.insert(0, os.path.dirname(__file__))
    from isa import CSR
    from memory import RegionGraph
    from _types import ModuleId


# =============================================================================
# Canonical Constants (must match spec/thiele_machine_spec.md)
# =============================================================================

MASK_WIDTH = 64  # Fixed width for hardware compatibility

# Maximum number of active modules (configurable for testing)
# Default: 64 (matches Verilog full configuration)
# Override via environment: THIELE_MAX_MODULES=8 for constrained testing
_DEFAULT_MAX_MODULES = 64
MAX_MODULES = int(os.environ.get("THIELE_MAX_MODULES", str(_DEFAULT_MAX_MODULES)))

# Validation: Must be power of 2 in reasonable range
if MAX_MODULES not in [4, 8, 16, 32, 64, 128, 256]:
    raise ValueError(
        f"MAX_MODULES must be power of 2 in [4, 256], got {MAX_MODULES}. "
        f"Set THIELE_MAX_MODULES environment variable to override."
    )

# Type alias for partition masks
PartitionMask = int  # 0..(1<<MASK_WIDTH)-1


# =============================================================================
# Bitmask Helper Functions
# =============================================================================

def mask_of_indices(indices: Set[int]) -> PartitionMask:
    """Convert a set of indices to a bitmask representation."""
    mask = 0
    for idx in indices:
        if 0 <= idx < MASK_WIDTH:
            mask |= (1 << idx)
    return mask


def indices_of_mask(mask: PartitionMask) -> Set[int]:
    """Convert a bitmask to a set of indices."""
    indices = set()
    for i in range(MASK_WIDTH):
        if mask & (1 << i):
            indices.add(i)
    return indices


def mask_union(a: PartitionMask, b: PartitionMask) -> PartitionMask:
    """Compute the union of two partition masks."""
    return a | b


def mask_intersection(a: PartitionMask, b: PartitionMask) -> PartitionMask:
    """Compute the intersection of two partition masks."""
    return a & b


def mask_disjoint(a: PartitionMask, b: PartitionMask) -> bool:
    """Check if two partition masks are disjoint (no overlap)."""
    return (a & b) == 0


def mask_popcount(mask: PartitionMask) -> int:
    """Count the number of set bits in a mask (population count)."""
    return bin(mask & ((1 << MASK_WIDTH) - 1)).count('1')


# =============================================================================
# μ-Ledger (Canonical Definition)
# =============================================================================

@dataclass
class MuLedger:
    """Tracks μ-bit costs for discovery and execution.

    This implements the canonical μ-ledger as defined in spec/thiele_machine_spec.md.
    All μ-values are monotonically non-decreasing.

    ISOMORPHISM GUARANTEE: This structure bisimulates Coq's vm_mu via the theorem
    python_mu_ledger_bisimulates_coq_vm_mu in coq/bridge/PythonMuLedgerBisimulation.v.

    Specifically: self.total ≡ vm_mu (modulo 2^32 hardware overflow semantics)

    The decomposition (mu_discovery, mu_execution, landauer_entropy) is a refinement
    that provides additional observability while preserving total μ-cost equivalence.
    """

    mu_discovery: int = 0   # Cost of partition discovery operations
    mu_execution: int = 0   # Cost of instruction execution
    landauer_entropy: int = 0  # Physical erasure accounting (side-channel)

    # HARDWARE CONSTANT: 32-bit width matching thiele_cpu.v
    MASK: int = 0xFFFFFFFF
    MAX_ENTROPY: int = 2**63 - 1

    @property
    def total(self) -> int:
        """Total μ-cost (discovery + execution)."""
        return (self.mu_discovery + self.mu_execution) & self.MASK

    def charge_execution(self, cost: int) -> None:
        """Atomic charge with hardware overflow semantics."""
        self.mu_execution = (self.mu_execution + cost) & self.MASK

    def charge_discovery(self, cost: int) -> None:
        """Atomic charge with hardware overflow semantics."""
        self.mu_discovery = (self.mu_discovery + cost) & self.MASK

    def track_entropy(self, bits: int) -> None:
        """Accumulate Landauer entropy without rollover."""
        if bits <= 0:
            return
        new_total = self.landauer_entropy + bits
        if new_total > self.MAX_ENTROPY:
            raise RuntimeError("Landauer entropy overflow")
        self.landauer_entropy = new_total

    def snapshot(self) -> Dict[str, int]:
        """Return a dictionary snapshot for tracing."""
        return {
            "mu_discovery": self.mu_discovery,
            "mu_execution": self.mu_execution,
            "mu_total": self.total,
            "landauer_entropy": self.landauer_entropy,
        }

    def copy(self) -> "MuLedger":
        """Create a copy of this ledger."""
        return MuLedger(
            mu_discovery=self.mu_discovery,
            mu_execution=self.mu_execution,
            landauer_entropy=self.landauer_entropy,
        )


Predicate = Callable[[int], bool]


@dataclass
class State:
    """Holds machine state ``S`` and partition table ``Π``.

    This implements the canonical state representation as defined in
    spec/thiele_machine_spec.md for isomorphism verification.

    IMPORTANT: This structure must align with CoreSemantics.State in Coq for
    cross-layer isomorphism verification.
    """

    mu_operational: float = 0.0  # Cost of operations (current mu) - legacy
    _mu_information: float = 0.0  # Cost of information revealed - legacy (internal)
    _next_id: int = 1
    regions: RegionGraph = field(default_factory=RegionGraph)
    axioms: Dict[ModuleId, List[str]] = field(default_factory=dict)  # Axioms per module
    csr: dict[CSR, int | str] = field(
        default_factory=lambda: {CSR.CERT_ADDR: "", CSR.STATUS: 0, CSR.ERR: 0}
    )
    step_count: int = 0

    # Canonical μ-ledger (spec/thiele_machine_spec.md)
    mu_ledger: MuLedger = field(default_factory=MuLedger)

    # Bitmask-based partition storage for hardware isomorphism
    partition_masks: Dict[ModuleId, PartitionMask] = field(default_factory=dict)

    # Program being executed (matches CoreSemantics.State.program field in Coq)
    program: List[Any] = field(default_factory=list)

    # Optional bookkeeping used by higher-level VM helpers.
    last_pdiscover_result: Dict[str, Any] | None = None

    @property
    def mu_information(self) -> float:
        """Get information revelation cost (read-only, monotonic)."""
        return self._mu_information
    
    @mu_information.setter
    def mu_information(self, value: float) -> None:
        """Set information cost with monotonicity enforcement.
        
        Raises:
            ValueError: If attempting to decrease μ_information
        """
        if value < self._mu_information:
            raise ValueError(
                f"μ-monotonicity violation: Cannot decrease mu_information from "
                f"{self._mu_information} to {value}. μ-ledger is monotonically non-decreasing."
            )
        if value < 0:
            raise ValueError(
                f"Invalid mu_information: {value}. μ-cost cannot be negative."
            )
        self._mu_information = value
    
    @property
    def mu(self) -> float:
        """Total mu cost (operational + information)."""
        return self.mu_operational + self._mu_information
    
    @property
    def num_modules(self) -> int:
        """Return the number of active modules."""
        return len(self.partition_masks)

    def _alloc(self, region: Set[int], charge_discovery: bool = False) -> ModuleId:
        """Allocate a new module for region.
        
        Args:
            region: Set of indices for this module
            charge_discovery: If True, charge discovery cost (only for PNEW)
        """
        mid = self._next_id
        self._next_id += 1
        self.regions.add(mid, region)
        # Also update bitmask representation
        region_mask = mask_of_indices(region)
        self.partition_masks[ModuleId(mid)] = region_mask
        
        if charge_discovery:
            self.mu_ledger.charge_discovery(mask_popcount(region_mask))
        
        return ModuleId(mid)

    def pnew(self, region: Set[int], *, charge_discovery: bool = True) -> ModuleId:
        """Create a module for ``region`` if not already present.

        μ-update: mu_discovery += popcount(region) when ``charge_discovery`` is True.
        """
        existing = self.regions.find(region)
        if existing is not None:
            return ModuleId(existing)

        if self.num_modules >= MAX_MODULES:
            raise ValueError(f"Cannot create module: max modules ({MAX_MODULES}) reached")
        mid = self._alloc(region, charge_discovery=charge_discovery)
        self.axioms[mid] = []  # Initialize empty axioms for new module
        
        self._enforce_invariant()
        return mid

    def psplit(
        self,
        module: ModuleId,
        pred: Predicate,
        *,
        charge_execution: bool = True,
        cost: int = 64,  # Default matches typical MASK_WIDTH, but should be overridden
    ) -> Tuple[ModuleId, ModuleId]:
        """Split ``module``'s region using ``pred`` into two modules.

        μ-update: mu_execution += cost (from instruction encoding).

        Args:
            module: Module ID to split
            pred: Predicate function to partition elements
            charge_execution: If True, charge μ-cost
            cost: μ-bits to charge (MUST match instruction mu_delta for isomorphism)

        ISOMORPHISM REQUIREMENT: The cost parameter MUST match the mu_delta in
        the instruction encoding to maintain perfect three-layer isomorphism
        with Coq and Verilog implementations.
        """
        region = self.regions[module]
        part1 = {x for x in region if pred(x)}
        part2 = region - part1
        if not part1 or not part2:
            empty = self._alloc(set())
            self.axioms[empty] = []  # Empty module has no axioms
            self._enforce_invariant()
            return module, empty
        self.regions.remove(module)
        # Remove from bitmask representation
        self.partition_masks.pop(module, None)

        axioms = self.axioms.pop(module, [])  # Get axioms before removing
        m1 = self._alloc(part1)
        m2 = self._alloc(part2)
        # Copy axioms to both new modules
        self.axioms[m1] = axioms.copy()
        self.axioms[m2] = axioms.copy()
        if charge_execution:
            self.mu_ledger.charge_execution(cost)
        
        self._enforce_invariant()
        return m1, m2

    def psplit_explicit(
        self,
        module: ModuleId,
        left: Set[int],
        right: Set[int],
        *,
        charge_execution: bool = True,
        cost: int = 64,  # Default matches typical MASK_WIDTH, but should be overridden
    ) -> Tuple[ModuleId, ModuleId]:
        """Split ``module`` into explicit ``left`` and ``right`` regions.

        This matches the extracted trace form: PSPLIT mid {left} {right} cost.

        ISOMORPHISM REQUIREMENT: The cost parameter MUST match the mu_delta in
        the instruction encoding to maintain perfect three-layer isomorphism.
        """
        region = self.regions[module]
        if left & right:
            raise ValueError("psplit_explicit regions overlap")
        if (left | right) != region:
            raise ValueError("psplit_explicit regions must partition module region")

        self.regions.remove(module)
        self.partition_masks.pop(module, None)
        axioms = self.axioms.pop(module, [])

        m1 = self._alloc(left)
        m2 = self._alloc(right)
        self.axioms[m1] = axioms.copy()
        self.axioms[m2] = axioms.copy()

        if charge_execution:
            self.mu_ledger.charge_execution(cost)

        self._enforce_invariant()
        return m1, m2

    def pmerge(
        self,
        m1: ModuleId,
        m2: ModuleId,
        *,
        charge_execution: bool = True,
        cost: int = 4,  # Default, but should be overridden with instruction mu_delta
    ) -> ModuleId:
        """Merge two modules into one if their regions are disjoint.

        μ-update: mu_execution += cost (from instruction encoding).

        Args:
            m1, m2: Module IDs to merge
            charge_execution: If True, charge μ-cost
            cost: μ-bits to charge (MUST match instruction mu_delta for isomorphism)

        ISOMORPHISM REQUIREMENT: The cost parameter MUST match the mu_delta in
        the instruction encoding to maintain perfect three-layer isomorphism.
        """
        if m1 == m2:
            raise ValueError("cannot merge module with itself")
        r1 = self.regions[m1]
        r2 = self.regions[m2]
        if r1 & r2:
            raise ValueError("modules overlap; cannot merge")
        union = r1 | r2
        self.regions.remove(m1)
        self.regions.remove(m2)
        # Remove from bitmask representation
        self.partition_masks.pop(m1, None)
        self.partition_masks.pop(m2, None)
        
        axioms1 = self.axioms.pop(m1, [])
        axioms2 = self.axioms.pop(m2, [])
        existing = self.regions.find(union)
        if existing is not None:
            # Merge axioms if module already exists
            existing_id = ModuleId(existing)
            self.axioms[existing_id].extend(axioms1)
            self.axioms[existing_id].extend(axioms2)
            return existing_id
        mid = self._alloc(union)
        self.axioms[mid] = axioms1 + axioms2  # Combine axioms
        if charge_execution:
            self.mu_ledger.charge_execution(cost)
        
        self._enforce_invariant()
        return mid

    def _enforce_invariant(self):
        """Enforce global invariant: |π_j| ≤ poly(n) for all partition modules."""
        n = sum(len(region) for region in self.regions.modules.values())
        poly_bound = n**2  # Example polynomial bound
        for module, region in self.regions.modules.items():
            if len(region) > poly_bound:
                raise ValueError(f"Invariant violated: module {module} has size {len(region)} > poly({n}) = {poly_bound}")

    def add_axiom(self, module: ModuleId, axiom: str) -> None:
        """Add an axiom to a module."""
        if module not in self.axioms:
            self.axioms[module] = []
        self.axioms[module].append(axiom)

    def get_module_axioms(self, module: ModuleId) -> List[str]:
        """Get all axioms for a module."""
        return self.axioms.get(module, [])
    
    def get_state_snapshot(self) -> Dict[str, Any]:
        """Return a snapshot of the current state for tracing.

        This format is designed for isomorphism verification with
        Verilog RTL and Coq proofs.
        """
        return {
            "num_modules": self.num_modules,
            "partition_masks": [
                int(self.partition_masks.get(ModuleId(i + 1), 0))
                for i in range(MAX_MODULES)
            ],
            "mu": self.mu_ledger.snapshot(),
            "step_count": self.step_count,
            "program_length": len(self.program),
        }
