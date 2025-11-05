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
    """Tracks region sets owned by each module."""

    modules: Dict[int, Set[int]] = field(default_factory=dict)

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
