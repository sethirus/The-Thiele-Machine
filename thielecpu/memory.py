# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Memory region graph management."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Optional, Set


@dataclass
class RegionGraph:
    """Tracks region sets owned by each module.
    
    Corresponds to PartitionGraph in Coq kernel/VMState.v
    """

    modules: Dict[int, Set[int]] = field(default_factory=dict)
    _next_id: int = field(default_factory=lambda: 1)

    def __contains__(self, module_id: int) -> bool:  # pragma: no cover - trivial
        return module_id in self.modules

    def __getitem__(self, module_id: int) -> Set[int]:  # pragma: no cover - trivial
        return self.modules[module_id]

    def add(self, module_id: int, region: Set[int]) -> None:
        """Register ``region`` for ``module_id``, ensuring disjointness."""

        for existing in self.modules.values():
            if existing & region:
                raise ValueError("region overlaps existing module")
        self.modules[module_id] = set(region)

    def remove(self, module_id: int) -> Set[int]:
        """Remove and return the region for ``module_id``."""

        return self.modules.pop(module_id)

    def find(self, region: Set[int]) -> Optional[int]:
        """Return module id owning ``region`` exactly, if any."""

        for mid, reg in self.modules.items():
            if reg == region:
                return mid
        return None
    
    def split(self, module_id: int, left: Set[int], right: Set[int]) -> Optional[tuple[int, int]]:
        """Split a module into two new modules (PSPLIT instruction).
        
        Corresponds to graph_psplit in Coq kernel/VMState.v
        
        Args:
            module_id: Module to split
            left: Left partition region
            right: Right partition region
            
        Returns:
            Tuple of (left_id, right_id) if successful, None if invalid split
        """
        if module_id not in self.modules:
            return None
        
        original = self.modules[module_id]
        
        # Validate partition: left and right must be subsets of original,
        # must be disjoint, and must cover original
        if not (left <= original and right <= original):
            return None
        if left & right:  # Not disjoint
            return None
        if left | right != original:  # Doesn't cover original
            return None
        
        # Handle empty partitions
        if not left or not right:
            # Create empty module and return original unchanged
            empty_id = self._next_id
            self._next_id += 1
            self.modules[empty_id] = set()
            return (module_id, empty_id) if not left else (empty_id, module_id)
        
        # Remove original module
        self.remove(module_id)
        
        # Add left and right as new modules
        left_id = self._next_id
        self._next_id += 1
        self.modules[left_id] = set(left)
        
        right_id = self._next_id
        self._next_id += 1
        self.modules[right_id] = set(right)
        
        return (left_id, right_id)
    
    def merge(self, m1: int, m2: int) -> Optional[int]:
        """Merge two modules into a single new module (PMERGE instruction).
        
        Corresponds to graph_pmerge in Coq kernel/VMState.v
        
        Args:
            m1: First module to merge
            m2: Second module to merge
            
        Returns:
            ID of merged module if successful, None if invalid merge
        """
        if m1 == m2:
            return None
        if m1 not in self.modules or m2 not in self.modules:
            return None
        
        region1 = self.modules[m1]
        region2 = self.modules[m2]
        
        # Regions must be disjoint to merge
        if region1 & region2:
            return None
        
        # Remove both modules
        self.remove(m1)
        self.remove(m2)
        
        # Create merged region
        merged_region = region1 | region2
        
        # Check if merged region already exists
        existing = self.find(merged_region)
        if existing is not None:
            return existing
        
        # Add new merged module
        merged_id = self._next_id
        self._next_id += 1
        self.modules[merged_id] = merged_region
        
        return merged_id
