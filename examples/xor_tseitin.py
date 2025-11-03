"""Compatibility shim exposing the relocated xor_tseitin demo."""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

_MODULE_PATH = Path(__file__).resolve().parents[1] / "demos" / "research-demos" / "partition" / "xor_tseitin.py"
_SPEC = importlib.util.spec_from_file_location("demos.research_demos.partition.xor_tseitin", str(_MODULE_PATH))
if _SPEC is None or _SPEC.loader is None:
    raise ImportError(f"Unable to load xor_tseitin demo from {_MODULE_PATH}")

_MODULE = importlib.util.module_from_spec(_SPEC)
sys.modules.setdefault(_SPEC.name, _MODULE)
_SPEC.loader.exec_module(_MODULE)

sys.modules[__name__] = _MODULE
globals().update(_MODULE.__dict__)
