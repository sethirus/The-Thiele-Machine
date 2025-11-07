"""Verifier package utilities for Thiele receipts.

This file makes the :mod:`verifier` directory importable so that helper
modules (for example :mod:`verifier.signature_utils`) can be reused by
multiple command line tools without duplicating logic.
"""

__all__ = [
    "signature_utils",
]

