#!/usr/bin/env python3
"""Compatibility shim for the relocated demonstrate_isomorphism module."""
from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

# Check if we're being run as the main script before module operations
_IS_MAIN = __name__ == "__main__"

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

if _IS_MAIN:
    # Parse arguments and invoke main() when run as a script
    parser = argparse.ArgumentParser()
    parser.add_argument("--act-vi", choices=("live", "offline"), help="Run Operation Cosmic Witness (Act VI) in the specified mode")
    parser.add_argument("--allow-network", action="store_true", help="Allow live network fetches for Act VI")
    parser.add_argument("--cmb-file", type=str, help="Path to an offline CMB sample (CSV).")
    parser.add_argument("--output-dir", type=str, help="Directory to write Act VI artifacts into")
    parser.add_argument("--data-source", choices=("offline", "planck", "healpix"), default="offline", help="Data source for Act VI")
    parser.add_argument("--skip-act-vi", action="store_true", help="Skip Act VI when running the full six-act demonstration")
    parser.add_argument("--full-act-vi-mode", choices=("offline", "live"), default="offline", help="Act VI mode when running the full demonstration")
    args = parser.parse_args()
    if args.act_vi:
        _MODULE.run_act_vi(
            mode=args.act_vi,
            allow_network=args.allow_network,
            cmb_file=args.cmb_file,
            output_dir=args.output_dir,
            data_source=args.data_source,
        )
    else:
        _MODULE.main(
            include_act_vi=not args.skip_act_vi,
            act_vi_mode=args.full_act_vi_mode,
            allow_network=args.allow_network,
            cmb_file=args.cmb_file,
            output_dir=args.output_dir,
            data_source=args.data_source,
        )
