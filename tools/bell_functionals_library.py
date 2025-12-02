#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Bell Functionals Library

Library of known Bell functionals with documented bounds.

Includes:
- CHSH (2×2×2×2): Standard CHSH inequality
- I3322 (3×3×2×2): Collins-Gisin-Linden-Massar-Popescu inequality

Usage:
    from tools.bell_functionals_library import get_functional
    
    chsh = get_functional("CHSH")
    i3322 = get_functional("I3322")
"""

from dataclasses import dataclass, field
from typing import Any, Dict, Optional, Tuple

import numpy as np

# Add repository root to path
import sys
from pathlib import Path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from tools.search_bell_functionals import BellFunctional


def make_chsh_functional() -> BellFunctional:
    """
    Create the standard CHSH functional.
    
    CHSH = E(0,0) + E(0,1) + E(1,0) - E(1,1)
    where E(x,y) = P(a=b|x,y) - P(a≠b|x,y)
    
    Bounds:
    - Classical (local): 2.0
    - Quantum (Tsirelson): 2√2 ≈ 2.828
    - NS (no-signaling): 4.0
    """
    coefficients = np.zeros((2, 2, 2, 2))
    
    # E(x,y) = P(0,0|x,y) + P(1,1|x,y) - P(0,1|x,y) - P(1,0|x,y)
    for x in range(2):
        for y in range(2):
            sign = 1 if (x, y) != (1, 1) else -1
            coefficients[x, y, 0, 0] = sign
            coefficients[x, y, 1, 1] = sign
            coefficients[x, y, 0, 1] = -sign
            coefficients[x, y, 1, 0] = -sign
    
    return BellFunctional(
        coefficients=coefficients,
        shape=(2, 2, 2, 2),
        name="CHSH",
        classical_bound=2.0,
        quantum_bound=2.0 * np.sqrt(2),
        metadata={
            "ns_bound": 4.0,
            "reference": "Clauser, Horne, Shimony, Holt (1969)"
        }
    )


def make_i3322_functional() -> BellFunctional:
    """
    Create the I3322 functional (Collins-Gisin-Linden-Massar-Popescu).
    
    I3322 is a Bell inequality for 3×3×2×2 scenario that is tight for quantum mechanics.
    
    The functional is:
    I3322 = -P(0,0|0,0) - P(0,0|0,1) - P(0,0|0,2)
            -P(0,0|1,0) - P(0,0|1,1) + P(0,1|1,2) + P(1,0|1,2)
            -P(0,0|2,0) + P(0,1|2,1) + P(1,0|2,1) + P(0,1|2,2) + P(1,0|2,2)
    
    Bounds:
    - Classical (local): 0.0
    - Quantum: 0.25 (1/4)
    - NS (no-signaling): ~0.25 (needs LP verification)
    
    Reference: Collins et al., PRL 88, 040404 (2002)
    """
    coefficients = np.zeros((3, 3, 2, 2))
    
    # Based on the I3322 inequality structure
    # Row 0 (x=0): All -1 coefficients for P(0,0|0,y)
    for y in range(3):
        coefficients[0, y, 0, 0] = -1.0
    
    # Row 1 (x=1):
    coefficients[1, 0, 0, 0] = -1.0
    coefficients[1, 1, 0, 0] = -1.0
    coefficients[1, 2, 0, 1] = 1.0
    coefficients[1, 2, 1, 0] = 1.0
    
    # Row 2 (x=2):
    coefficients[2, 0, 0, 0] = -1.0
    coefficients[2, 1, 0, 1] = 1.0
    coefficients[2, 1, 1, 0] = 1.0
    coefficients[2, 2, 0, 1] = 1.0
    coefficients[2, 2, 1, 0] = 1.0
    
    return BellFunctional(
        coefficients=coefficients,
        shape=(3, 3, 2, 2),
        name="I3322",
        classical_bound=0.0,
        quantum_bound=0.25,
        metadata={
            "ns_bound": 0.25,  # Needs LP verification
            "reference": "Collins, Gisin, Linden, Massar, Popescu, PRL 88, 040404 (2002)",
            "tight_for_quantum": True
        }
    )


def get_functional(name: str) -> Optional[BellFunctional]:
    """
    Get a functional by name from the library.
    
    Args:
        name: Name of functional (case-insensitive)
    
    Returns:
        BellFunctional or None if not found
    """
    name_lower = name.lower()
    
    if name_lower == "chsh":
        return make_chsh_functional()
    elif name_lower == "i3322":
        return make_i3322_functional()
    else:
        return None


def list_functionals() -> Dict[str, Dict[str, Any]]:
    """
    List all functionals in the library with metadata.
    
    Returns:
        Dictionary mapping names to metadata
    """
    return {
        "CHSH": {
            "shape": (2, 2, 2, 2),
            "classical_bound": 2.0,
            "quantum_bound": 2.0 * np.sqrt(2),
            "ns_bound": 4.0,
            "description": "Standard CHSH inequality"
        },
        "I3322": {
            "shape": (3, 3, 2, 2),
            "classical_bound": 0.0,
            "quantum_bound": 0.25,
            "ns_bound": 0.25,
            "description": "Collins-Gisin-Linden-Massar-Popescu inequality"
        }
    }


if __name__ == "__main__":
    # Demo usage
    print("Bell Functionals Library")
    print("=" * 60)
    
    for name, info in list_functionals().items():
        print(f"\n{name}:")
        print(f"  Shape: {info['shape']}")
        print(f"  Classical bound: {info['classical_bound']}")
        print(f"  Quantum bound: {info['quantum_bound']:.6f}")
        print(f"  NS bound: {info['ns_bound']}")
        print(f"  Description: {info['description']}")
