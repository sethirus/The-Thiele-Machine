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
