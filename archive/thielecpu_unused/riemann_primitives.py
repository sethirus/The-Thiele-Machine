#!/usr/bin/env python3
"""
Riemann Hypothesis Search Primitives

This module extends the primitive library with operations for searching
for counterexamples to the Riemann Hypothesis.

The Riemann Hypothesis states that all non-trivial zeros of the Riemann
zeta function have real part = 0.5. To disprove it, we need to find a
single zero with real part != 0.5.
"""

import numpy as np
from typing import Tuple, List, Dict, Any
import mpmath
from dataclasses import dataclass


# Set high precision for mpmath
mpmath.mp.dps = 50  # 50 decimal places


@dataclass
class ComplexPoint:
    """Represents a point in the complex plane."""
    real: float
    imag: float
    
    def __repr__(self):
        return f"{self.real} + {self.imag}i"


def prim_zeta(s: complex) -> complex:
    """
    Compute the Riemann zeta function at complex point s.
    
    Uses mpmath for high-precision calculation.
    """
    try:
        result = mpmath.zeta(s)
        return complex(result)
    except:
        return complex(float('inf'), float('inf'))


def prim_zeta_magnitude(s: complex) -> float:
    """
    Compute |ζ(s)| - the magnitude of zeta at point s.
    
    A zero occurs when this magnitude is near 0.
    """
    zeta_val = prim_zeta(s)
    return abs(zeta_val)


def prim_grid_search(
    re_min: float,
    re_max: float,
    im_min: float,
    im_max: float,
    step: float = 0.1
) -> List[ComplexPoint]:
    """
    Perform grid search in a rectangular region of complex plane.
    
    Returns points where |ζ(s)| is small (potential zeros).
    """
    candidates = []
    
    re_vals = np.arange(re_min, re_max, step)
    im_vals = np.arange(im_min, im_max, step)
    
    threshold = 0.01  # Magnitude threshold for candidates
    
    for re in re_vals:
        for im in im_vals:
            s = complex(re, im)
            mag = prim_zeta_magnitude(s)
            
            if mag < threshold:
                candidates.append(ComplexPoint(re, im))
    
    return candidates


def prim_refine_zero(
    initial: ComplexPoint,
    tolerance: float = 1e-10,
    max_iterations: int = 100
) -> Tuple[ComplexPoint, float]:
    """
    Refine a candidate zero using Newton-Raphson iteration.
    
    Returns:
        (refined_point, final_magnitude)
    """
    s = complex(initial.real, initial.imag)
    
    for _ in range(max_iterations):
        zeta_val = prim_zeta(s)
        mag = abs(zeta_val)
        
        if mag < tolerance:
            return ComplexPoint(s.real, s.imag), mag
        
        # Numerical derivative for Newton-Raphson
        h = 1e-8
        zeta_prime = (prim_zeta(s + h) - prim_zeta(s - h)) / (2 * h)
        
        if abs(zeta_prime) < 1e-12:
            break
        
        # Newton step
        s = s - zeta_val / zeta_prime
    
    return ComplexPoint(s.real, s.imag), abs(prim_zeta(s))


def prim_is_on_critical_line(point: ComplexPoint, tolerance: float = 1e-6) -> bool:
    """
    Check if a point is on the critical line (Re(s) = 0.5).
    """
    return abs(point.real - 0.5) < tolerance


def prim_verify_counterexample(
    point: ComplexPoint,
    zero_tolerance: float = 1e-10,
    critical_line_tolerance: float = 1e-6
) -> Dict[str, Any]:
    """
    Verify if a point is a valid counterexample to the Riemann Hypothesis.
    
    A counterexample must be:
    1. A zero of the zeta function (|ζ(s)| ≈ 0)
    2. NOT on the critical line (Re(s) ≠ 0.5)
    3. In the critical strip (0 < Re(s) < 1)
    
    Returns verification report.
    """
    s = complex(point.real, point.imag)
    
    # Check if it's a zero
    mag = prim_zeta_magnitude(s)
    is_zero = mag < zero_tolerance
    
    # Check if it's on critical line
    on_critical_line = prim_is_on_critical_line(point, critical_line_tolerance)
    
    # Check if in critical strip
    in_critical_strip = 0 < point.real < 1
    
    # A valid counterexample is a zero NOT on the critical line
    is_counterexample = is_zero and not on_critical_line and in_critical_strip
    
    return {
        "point": str(point),
        "real_part": point.real,
        "imag_part": point.imag,
        "zeta_magnitude": mag,
        "is_zero": is_zero,
        "on_critical_line": on_critical_line,
        "in_critical_strip": in_critical_strip,
        "is_valid_counterexample": is_counterexample,
        "deviation_from_critical_line": abs(point.real - 0.5)
    }


def prim_adaptive_search(
    re_center: float,
    im_center: float,
    radius: float,
    resolution_levels: int = 3
) -> List[ComplexPoint]:
    """
    Perform adaptive multi-resolution search around a center point.
    
    Starts with coarse grid, refines in regions where |ζ(s)| is small.
    """
    candidates = []
    
    for level in range(resolution_levels):
        step = radius / (2 ** level) / 10
        re_min = re_center - radius / (2 ** level)
        re_max = re_center + radius / (2 ** level)
        im_min = im_center - radius / (2 ** level)
        im_max = im_center + radius / (2 ** level)
        
        level_candidates = prim_grid_search(re_min, re_max, im_min, im_max, step)
        
        if level_candidates:
            # Found potential zeros, refine further
            for candidate in level_candidates:
                refined, mag = prim_refine_zero(candidate)
                if mag < 1e-8:
                    candidates.append(refined)
    
    return candidates


def prim_structured_search(
    im_range_start: float,
    im_range_end: float,
    off_line_sigma: float = 0.51
) -> List[Dict[str, Any]]:
    """
    Structured search for zeros off the critical line.
    
    Searches along a line Re(s) = off_line_sigma (not 0.5).
    If we find a zero here, it's a counterexample.
    
    Args:
        im_range_start: Start of imaginary range to search
        im_range_end: End of imaginary range
        off_line_sigma: Real part to search along (should not be 0.5)
    
    Returns:
        List of verification reports for potential counterexamples
    """
    results = []
    
    # Search along the off-critical line
    step = 0.5
    im_vals = np.arange(im_range_start, im_range_end, step)
    
    for im in im_vals:
        point = ComplexPoint(off_line_sigma, im)
        s = complex(point.real, point.imag)
        mag = prim_zeta_magnitude(s)
        
        # If magnitude is small, investigate further
        if mag < 0.1:
            refined, final_mag = prim_refine_zero(point)
            
            if final_mag < 1e-8:
                # Verify if this is a counterexample
                verification = prim_verify_counterexample(refined)
                results.append(verification)
    
    return results


# Registry of Riemann primitives
RIEMANN_PRIMITIVES = {
    'ZETA': prim_zeta,
    'ZETA_MAG': prim_zeta_magnitude,
    'GRID_SEARCH': prim_grid_search,
    'REFINE_ZERO': prim_refine_zero,
    'IS_ON_CRITICAL_LINE': prim_is_on_critical_line,
    'VERIFY_COUNTEREXAMPLE': prim_verify_counterexample,
    'ADAPTIVE_SEARCH': prim_adaptive_search,
    'STRUCTURED_SEARCH': prim_structured_search,
}


def get_riemann_primitive(name: str):
    """Get a Riemann primitive by name."""
    if name not in RIEMANN_PRIMITIVES:
        raise ValueError(f"Unknown Riemann primitive: {name}")
    return RIEMANN_PRIMITIVES[name]


def list_riemann_primitives() -> List[str]:
    """List all available Riemann primitives."""
    return sorted(RIEMANN_PRIMITIVES.keys())
