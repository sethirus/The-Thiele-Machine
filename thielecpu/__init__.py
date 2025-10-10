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

from .security_monitor import log_usage, display_security_warning


def __getattr__(name: str):
	"""Lazy attribute loader for package-level convenience.

	Accessing ``thielecpu.VM`` will import the heavy ``thielecpu.vm``
	module on demand, avoiding noisy import-time side-effects when the
	package is imported for type-checking or inspection.
	"""
	if name == "VM":
		from .vm import VM  # local import to avoid import-time effects

		return VM
	if name in ("log_usage", "display_security_warning"):
		return globals()[name]
	raise AttributeError(f"module {__name__} has no attribute {name}")


__all__ = ["log_usage", "display_security_warning"]
