"""Compatibility shim for the relocated demonstrate_isomorphism module."""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

_MODULE_PATH = Path(__file__).resolve().parent / "demos" / "research-demos" / "architecture" / "demonstrate_isomorphism.py"
_SPEC = importlib.util.spec_from_file_location(
    "demos.research_demos.architecture.demonstrate_isomorphism", str(_MODULE_PATH)
)
if _SPEC is None or _SPEC.loader is None:
    raise ImportError(f"Unable to load demonstrate_isomorphism from {_MODULE_PATH}")

_MODULE = importlib.util.module_from_spec(_SPEC)
# Ensure future imports reuse the loaded module
sys.modules.setdefault(_SPEC.name, _MODULE)
_SPEC.loader.exec_module(_MODULE)

# Replace this shim's module entry with the loaded implementation
sys.modules[__name__] = _MODULE

globals().update(_MODULE.__dict__)
