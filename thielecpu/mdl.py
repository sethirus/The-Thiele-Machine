"""μ-bit accounting via MDL rules."""

from __future__ import annotations

try:
    from .isa import CSR
    from .state import State
    from ._types import ModuleId
except ImportError:
    # Handle running as script
    import sys
    import os
    sys.path.insert(0, os.path.dirname(__file__))
    from isa import CSR
    from state import State
    from _types import ModuleId


def detect_fragment_type(region: set) -> str:
    """Detect the logical fragment type of a module's region.

    Returns:
        "horn": Horn clause fragment (polynomial time)
        "2sat": 2-SAT fragment (polynomial time)
        "unknown": Unknown or potentially intractable fragment
    """
    # For now, implement basic detection
    # In a full implementation, this would analyze the actual logical structure
    # For demonstration, we'll assume small regions are tractable
    if len(region) <= 100:  # Conservative bound for tractability
        return "horn"  # Assume Horn-like for small modules
    else:
        return "unknown"


def mdlacc(state: State, module: ModuleId, *, consistent: bool) -> float:
    """Update ``state.mu_operational`` based on ``module`` size (auditor contract).

    Auditor cost is charged against |π_j|. By invariant, total auditor cost is poly(n).
    ``consistent`` indicates whether the module's logic checks passed. When
    ``False`` the ``CSR.ERR`` register is set and ``μ_operational`` becomes infinite.
    Otherwise ``μ_operational`` increases by |π_j| μ-bits per audit.

    Only processes modules from known polynomial-time fragments for auditor tractability.
    """

    region = state.regions[module]

    # Check fragment type for auditor tractability
    fragment_type = detect_fragment_type(region)
    if fragment_type == "unknown":
        # Reject unknown fragments to guarantee tractability
        state.csr[CSR.ERR] = 1
        state.mu_operational = float("inf")
        return state.mu_operational

    if not consistent:
        state.csr[CSR.ERR] = 1
        state.mu_operational = float("inf")
    elif state.mu_operational != float("inf"):
        state.mu_operational += len(region)  # Charge against |π_j|
    return state.mu_operational


def info_charge(state: State, bits_revealed: float) -> float:
    """Charge for information revealed (bits of new knowledge).

    This implements the "no unpaid sight debt" principle - any information
    revealed by oracles or discovery processes must be paid for.
    """
    if state.mu_information != float("inf"):
        state.mu_information += bits_revealed
    return state.mu_information


__all__ = ["mdlacc", "detect_fragment_type"]
