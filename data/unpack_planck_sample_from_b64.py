#!/usr/bin/env python3
from pathlib import Path
import base64

b64_path = Path(__file__).resolve().parent / 'planck_sample.fits.b64'
out_path = Path(__file__).resolve().parent / 'planck_sample.fits'
with b64_path.open('r', encoding='ascii') as fh:
    s = fh.read().strip()
    b = base64.b64decode(s)
    out_path.write_bytes(b)
print(f"Unpacked {b64_path} -> {out_path}")
