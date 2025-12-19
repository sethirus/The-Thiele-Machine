"""Landauer prereg models.

This file defines the *parameter-free* finite-time correction term interface.

Important:
- The prereg harness treats these functions as part of the locked toolchain
  via tool hashing in MANIFEST_A.json.
- If you change this file, the manifest tool hash will change and the run must
  be re-initialized in a new output root.

Finite-time bound (Proesmans–Ehrich–Bechhoefer, 2020):

In the dimensionless time

  τ̂ = D τ / Var(x)

the minimal work obeys:

  W_min/(k_B T) ≥ ln 2 + 1/(2 τ̂)

So the additive correction term is:

  extra_term_over_kT(τ̂) = 1/(2 τ̂)

This is parameter-free. We include only a tiny numerical clip for stability.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Optional


@dataclass(frozen=True)
class ProtocolPoint:
    """A single datapoint of an erasure protocol.

    Values are expected to be normalized such that work is in units of kT.
    """

    # NOTE: Despite the name, this is a generic time coordinate.
    # For PREREG_A we primarily use tau_unit="D_tau_over_Var" meaning
    # tau_value = τ̂ = D τ / Var(x) (dimensionless).
    tau_s: float
    work_over_kT: float
    tau_unit: str = "s"
    work_err_over_kT: Optional[float] = None


def mu_protocol(point: ProtocolPoint) -> float:
    """Compute a µ descriptor for the protocol at a point.

    This is currently a stub.

    For a real prereg, replace this with a well-defined, parameter-free
    computation from protocol description (NOT from solver outcomes).
    """

    # Placeholder: no protocol structure accounting.
    return 0.0


def extra_term_over_kT(*, mu: float, point: ProtocolPoint) -> float:
    """Return the additive correction term in units of kT.

    Requirements:
    - Must be >= 0 for all points.
    - Must go to 0 in the reversible/ideal limit.

    For PREREG_A we implement the Proesmans–Ehrich–Bechhoefer (2020)
    finite-time lower bound term:

      extra = 1 / (2 τ̂)

    where τ̂ = D τ / Var(x). This is applied only when point.tau_unit is
    "D_tau_over_Var". Otherwise we return 0 (no claim about other scalings).
    """

    _ = mu  # reserved for future µ-structure terms

    if point.tau_unit != "D_tau_over_Var":
      return 0.0

    tau_hat = float(point.tau_s)
    if not math.isfinite(tau_hat):
      return 0.0

    # Numerical stability only; not a fitted parameter.
    tau_hat = max(tau_hat, 1e-12)
    extra = 0.5 / tau_hat
    if not math.isfinite(extra) or extra < 0.0:
      return 0.0
    return min(extra, 1e12)
