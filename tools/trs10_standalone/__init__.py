"""Standalone TRS-1.0 verifier package.

This package is intentionally separated from the main receipt helper so the
first independent verifier can harden the protocol surface through its own
implementation path.
"""

from .api import verify_receipt_dict
from .execution import default_execution_adapters

__all__ = ["default_execution_adapters", "verify_receipt_dict"]