# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""μ-bit accounting via MDL rules."""

from __future__ import annotations

import math
import zlib

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
    """Update ``state.mu_operational`` based on true MDL calculation.

    MDL cost is a function of certificate complexity plus partition encoding cost.
    ``consistent`` indicates whether the module's logic checks passed. When
    ``False`` the ``CSR.ERR`` register is set and ``μ_operational`` becomes infinite.
    Otherwise ``μ_operational`` increases by the calculated MDL cost.

    Only processes modules from known polynomial-time fragments for auditor tractability.
    """

    region = state.regions[module]

    # Use a fixed saturation value for the canonical integer μ-ledger.
    MU_SATURATION = (1 << 64) - 1

    # Check fragment type for auditor tractability
    fragment_type = detect_fragment_type(region)
    if fragment_type == "unknown":
        # Reject unknown fragments to guarantee tractability
        state.csr[CSR.ERR] = 1
        state.mu_operational = float("inf")
        state.mu_ledger.mu_execution = MU_SATURATION
        return state.mu_operational

    if not consistent:
        state.csr[CSR.ERR] = 1
        state.mu_operational = float("inf")
        state.mu_ledger.mu_execution = MU_SATURATION
        return state.mu_operational

    if state.mu_operational == float("inf"):
        state.mu_ledger.mu_execution = MU_SATURATION
        return state.mu_operational

    # Calculate true MDL cost
    mdl_cost = 0.0

    # 1. Certificate complexity
    cert_path = state.csr.get(CSR.CERT_ADDR)
    if cert_path:
        try:
            from pathlib import Path
            cert_file = Path(str(cert_path))
            if cert_file.exists():
                # Read the certificate file
                cert_content = cert_file.read_bytes()
                # Complexity based on file size in bits
                cert_bits = len(zlib.compress(cert_content)) * 8
                mdl_cost += cert_bits

                # Additional complexity from unsat core if present
                cert_str = cert_content.decode('utf-8', errors='ignore')
                if 'unsat:' in cert_str:
                    # Estimate unsat core size
                    core_part = cert_str.split('unsat:')[1].strip()
                    core_bits = len(zlib.compress(core_part.encode('utf-8'))) * 8
                    mdl_cost += core_bits
        except (OSError, ValueError):
            # If can't read certificate, use a default cost
            mdl_cost += 1024  # 1KB default

    # 2. Cost of encoding the partition itself
    # Number of bits needed to encode the region set
    if region:
        max_element = max(region)
        # At least one bit is required even for singleton {0}; mirror the RTL fuzz harness.
        bit_length = max(1, max_element.bit_length())
        partition_bits = bit_length * len(region)  # bits per element * num elements
        mdl_cost += partition_bits
    else:
        mdl_cost += 1  # minimal cost for empty partition

    # 3. Add module axioms complexity
    module_axioms = state.get_module_axioms(module)
    axioms_complexity = sum(len(zlib.compress(axiom.encode('utf-8'))) * 8 for axiom in module_axioms)
    mdl_cost += axioms_complexity

    state.mu_operational += mdl_cost
    if state.mu_ledger.mu_execution != float("inf"):
        state.mu_ledger.mu_execution = (state.mu_ledger.mu_execution + int(mdl_cost)) & 0xFFFFFFFF
    return state.mu_operational


def info_charge(state: State, bits_revealed: float) -> float:
    """Charge for information revealed (bits of new knowledge).

    This implements the "no unpaid sight debt" principle - any information
    revealed by oracles or discovery processes must be paid for.
    
    Raises:
        ValueError: If bits_revealed is negative
    """
    if bits_revealed < 0:
        raise ValueError(f"Cannot charge negative information: {bits_revealed} bits")
    
    if bits_revealed == 0:
        return state.mu_information
    
    # Charge to legacy mu_information (enforces monotonicity via property setter)
    if state.mu_information != float("inf"):
        state.mu_information = state.mu_information + bits_revealed
    
    # Charge to canonical μ-ledger
    if state.mu_ledger.mu_execution != float("inf"):
        # μ must lower-bound the information bits revealed; round up to avoid
        # fractional deficits (no free insight).
        charge_amount = int(math.ceil(bits_revealed))
        state.mu_ledger.charge_execution(charge_amount)
    
    return state.mu_information


def compute_mu_cost_rom(features: 'np.ndarray',
                        A: 'np.ndarray',
                        dt: float,
                        dof: int,
                        include_state_storage: bool = True,
                        precision_bits: int = 64) -> float:
    """Compute μ-cost for a reduced-order model (ROM).

    This function centralizes μ-cost accounting for ROMs and can be used by
    multiple tools. Computation includes:
    - μ_discovery: encoding the dynamics matrix A
    - μ_execution: cost of executing the ROM in feature-space
    - μ_state_storage: optional cost to store/transmit coarse-grained state
    """
    import numpy as _np

    nt, n_feat = features.shape

    # μ_discovery: Cost to encode ROM parameters - 32 bits per param
    mu_discovery = n_feat * n_feat * 32

    # μ_execution: feature-space execution cost
    mu_execution = nt * (_np.log2(nt) + n_feat * 32)

    # μ_state_storage: cost to store coarse-grained DOF if included
    mu_state_storage = dof * nt * precision_bits if include_state_storage else 0

    mu_total = mu_discovery + mu_execution + mu_state_storage
    return float(mu_total)


__all__ = ["mdlacc", "detect_fragment_type", "compute_mu_cost_rom"]
