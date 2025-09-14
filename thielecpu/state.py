"""Machine state and partition operations."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Set, Tuple

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

    mu: float = 0.0
    _next_id: int = 1
    regions: RegionGraph = field(default_factory=RegionGraph)
    csr: dict[CSR, int | str] = field(
        default_factory=lambda: {CSR.CERT_ADDR: "", CSR.STATUS: 0, CSR.ERR: 0}
    )
    step_count: int = 0

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
        self._enforce_invariant()
        return mid

    def psplit(self, module: ModuleId, pred: Predicate) -> Tuple[ModuleId, ModuleId]:
        """Split ``module``'s region using ``pred`` into two modules."""

        region = self.regions[module]
        part1 = {x for x in region if pred(x)}
        part2 = region - part1
        if not part1 or not part2:
            empty = self._alloc(set())
            self._enforce_invariant()
            return module, empty
        self.regions.remove(module)
        m1 = self._alloc(part1)
        m2 = self._alloc(part2)
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
        existing = self.regions.find(union)
        if existing is not None:
            return ModuleId(existing)
        mid = self._alloc(union)
        self._enforce_invariant()
        return mid

    def _enforce_invariant(self):
        """Enforce global invariant: |π_j| ≤ poly(n) for all partition modules."""
        n = sum(len(region) for region in self.regions.modules.values())
        poly_bound = n**2  # Example polynomial bound
        for module, region in self.regions.modules.items():
            if len(region) > poly_bound:
                raise ValueError(f"Invariant violated: module {module} has size {len(region)} > poly({n}) = {poly_bound}")
