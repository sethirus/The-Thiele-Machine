# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Physics module for the Thiele Machine.

This module contains physics simulations that demonstrate the relationship
between Information and Energy as predicted by the Thiele Machine framework.

Modules:
    brownian_ratchet: Maxwell-Thiele Ratchet demonstrating Information → Work
    landauer: Landauer erasure models and finite-time corrections
"""

from . import brownian_ratchet
from . import landauer

__all__ = ['brownian_ratchet', 'landauer']
