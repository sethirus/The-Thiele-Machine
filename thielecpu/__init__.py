# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Extraction-only Thiele CPU package.

The kept package surface is intentionally narrow:
	coq/Extraction.v -> build/thiele_core.ml -> thielecpu/vm.py
	coq/kami_hw/ThieleCPUCore.v -> thielecpu/hardware/rtl/thiele_cpu_kami.v
"""

from typing import TYPE_CHECKING


if TYPE_CHECKING:
	from .vm import VM


def __getattr__(name: str):
	"""Lazy attribute loader for the extracted VM wrapper."""
	if name == "VM":
		from .vm import VM

		return VM
	raise AttributeError(f"module {__name__} has no attribute {name}")


__all__ = ["VM"]
