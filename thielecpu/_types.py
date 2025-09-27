"""Type definitions for strict interfaces.

This module centralizes lightweight type aliases used across the Thiele CPU
package.  Having a dedicated module keeps the public API tidy while letting the
rest of the codebase share strongly typed identifiers without importing the
full ``typing`` machinery everywhere.
"""

from __future__ import annotations

from typing import NewType, TypedDict


#
# Identifier types
#

ModuleId = NewType("ModuleId", int)
"""Identifier for a partition/module in the region graph."""

RegionId = NewType("RegionId", int)
"""Identifier for a memory region."""


#
# Ledger structures
#


class LedgerEntry(TypedDict):
    """Row in the μ-bit ledger produced during execution."""

    step: int
    delta_mu_operational: int | float
    delta_mu_information: int | float
    total_mu_operational: int | float
    total_mu_information: int | float
    total_mu: int | float
    reason: str


__all__ = ["ModuleId", "RegionId", "LedgerEntry"]
