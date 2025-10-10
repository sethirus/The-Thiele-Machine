# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Machine state and partition operations."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Set, Tuple, Dict, List

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


Predicate = Callable[[int], bool]


@dataclass
class State:
    """Holds machine state ``S`` and partition table ``Π``."""

    mu_operational: float = 0.0  # Cost of operations (current mu)
    mu_information: float = 0.0  # Cost of information revealed
    _next_id: int = 1
    regions: RegionGraph = field(default_factory=RegionGraph)
    axioms: Dict[ModuleId, List[str]] = field(default_factory=dict)  # Axioms per module
    csr: dict[CSR, int | str] = field(
        default_factory=lambda: {CSR.CERT_ADDR: "", CSR.STATUS: 0, CSR.ERR: 0}
    )
    step_count: int = 0

    @property
    def mu(self) -> float:
        """Total mu cost (operational + information)."""
        return self.mu_operational + self.mu_information

    def _alloc(self, region: Set[int]) -> ModuleId:
        mid = self._next_id
        self._next_id += 1
        self.regions.add(mid, region)
        return ModuleId(mid)

    def pnew(self, region: Set[int]) -> ModuleId:
        """Create a module for ``region`` if not already present."""

        existing = self.regions.find(region)
        if existing is not None:
            return ModuleId(existing)
        mid = self._alloc(region)
        self.axioms[mid] = []  # Initialize empty axioms for new module
        self._enforce_invariant()
        return mid

    def psplit(self, module: ModuleId, pred: Predicate) -> Tuple[ModuleId, ModuleId]:
        """Split ``module``'s region using ``pred`` into two modules."""

        region = self.regions[module]
        part1 = {x for x in region if pred(x)}
        part2 = region - part1
        if not part1 or not part2:
            empty = self._alloc(set())
            self.axioms[empty] = []  # Empty module has no axioms
            self._enforce_invariant()
            return module, empty
        self.regions.remove(module)
        axioms = self.axioms.pop(module, [])  # Get axioms before removing
        m1 = self._alloc(part1)
        m2 = self._alloc(part2)
        # Copy axioms to both new modules
        self.axioms[m1] = axioms.copy()
        self.axioms[m2] = axioms.copy()
        self._enforce_invariant()
        return m1, m2

    def pmerge(self, m1: ModuleId, m2: ModuleId) -> ModuleId:
        """Merge two modules into one if their regions are disjoint."""

        if m1 == m2:
            raise ValueError("cannot merge module with itself")
        r1 = self.regions[m1]
        r2 = self.regions[m2]
        if r1 & r2:
            raise ValueError("modules overlap; cannot merge")
        union = r1 | r2
        self.regions.remove(m1)
        self.regions.remove(m2)
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
