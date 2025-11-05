Canonical data utilities

Use `generate_planck_sample.py` to deterministically generate a small FITS
sample from the committed CSV canonical sample. This is useful in CI or when
Healpix/astropy-based tools are required but network access is not available.

Usage:

  python data/generate_planck_sample.py

The script writes `data/planck_sample.fits` in the repository. The CSV source
`data/cmb_sample.csv` is the canonical input and is committed for reproducibility.
