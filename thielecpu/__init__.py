# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Thiele CPU package."""

# ============================================================================
# 🚨 CRITICAL SECURITY WARNING 🚨
# ============================================================================
#
# This package implements the Thiele CPU - a partition-native virtual machine
# that could be weaponized for cryptanalysis of RSA and other systems.
#
# ETHICAL USE REQUIREMENTS:
# - Defensive security research only
# - No offensive cryptanalysis
# - Contact maintainers for security applications
# - Monitor for responsible use
#
# ============================================================================

import warnings
import multiprocessing

# Only warn in the main process to avoid spam in multiprocessing
if multiprocessing.current_process().name == 'MainProcess':
    warnings.warn(
        "⚠️  SECURITY WARNING: Importing thielecpu package. This implements "
        "partition-native computation that could break RSA encryption. Use only "
        "for defensive security research.",
        UserWarning,
        stacklevel=2
    )

# Initialize security monitoring
from .security_monitor import log_usage
from .vm import VM

__all__ = ["VM"]
