"""Turbulence proofpack utilities."""

from importlib import import_module
from typing import Dict, Tuple

__all__ = [
    "PROTOCOLS",
    "ProtocolConfig",
    "ProtocolSummary",
    "TurbulenceSample",
    "execute_protocol",
    "load_sample",
    "run_dataset",
]

_EXPORTS: Dict[str, Tuple[str, str]] = {
    "PROTOCOLS": (".protocol", "PROTOCOLS"),
    "ProtocolConfig": (".protocol", "ProtocolConfig"),
    "ProtocolSummary": (".protocol", "ProtocolSummary"),
    "TurbulenceSample": (".protocol", "TurbulenceSample"),
    "execute_protocol": (".protocol", "execute_protocol"),
    "load_sample": (".protocol", "load_sample"),
    "run_dataset": (".protocol", "run_dataset"),
}


def __getattr__(name: str):
    if name not in _EXPORTS:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    module_name, attr_name = _EXPORTS[name]
    module = import_module(module_name, __name__)
    value = getattr(module, attr_name)
    globals()[name] = value
    return value
