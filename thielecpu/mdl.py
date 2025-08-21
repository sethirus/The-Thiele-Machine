"""μ-bit accounting via MDL rules."""

from __future__ import annotations

from .isa import CSR
from .state import State
from ._types import ModuleId


def mdlacc(state: State, module: ModuleId, *, consistent: bool) -> int:
    """Update ``state.mu`` based on ``module`` size.

    ``consistent`` indicates whether the module's logic checks passed. When
    ``False`` the ``CSR.ERR`` register is set and ``μ`` becomes infinite.
    Otherwise ``μ`` increases proportionally to the module's region size.
    """

    region = state.regions[module]
    if not consistent:
        state.csr[CSR.ERR] = 1
        state.mu = float("inf")
    elif state.mu != float("inf"):
        state.mu += len(region) * 16
    return state.mu


__all__ = ["mdlacc"]
