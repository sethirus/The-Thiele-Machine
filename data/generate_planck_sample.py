# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""Deterministically generate a small FITS sample from the committed CSV.

This script is intended to be used in CI to produce a canonical FITS sample
that downstream HEALPix/astropy code can consume. It deterministically reads
`data/cmb_sample.csv` and writes `data/planck_sample.fits` using the same
conversion used by the main Act VI code.
"""
from pathlib import Path
from demonstrate_isomorphism import write_fits_from_csv

if __name__ == "__main__":
    repo = Path(__file__).resolve().parent
    csv_path = repo / "cmb_sample.csv"
    out = repo / "planck_sample.fits"
    try:
        write_fits_from_csv(csv_path, out)
        print(f"Wrote canonical FITS to {out}")
    except ImportError:
        print("astropy/numpy not available in this environment; skipping FITS generation.")
        print("In CI the FITS will be generated using the committed CSV and astropy.")
