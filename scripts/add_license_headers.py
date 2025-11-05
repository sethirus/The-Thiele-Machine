#!/usr/bin/env python3
"""Add Apache-2.0 license header to source files that lack one.

Usage: python scripts/add_license_headers.py
"""
from pathlib import Path
HEADER_PY = '''# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
'''
HEADER_VERILOG = '''// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
// See the LICENSE file in the repository root for full terms.
'''
HEADER_TEX = '''% Licensed under the Apache License, Version 2.0 (the "License");
% you may not use this file except in compliance with the License.
% Copyright 2025 Devon Thiele
% See the LICENSE file in the repository root for full terms.
'''

EXTENSIONS = {
    '.py': HEADER_PY,
    '.v': HEADER_VERILOG,
    '.sv': HEADER_VERILOG,
    '.tex': HEADER_TEX,
    '.sh': HEADER_PY,
}

ROOT = Path(__file__).resolve().parents[1]

def has_header(text):
    return 'Licensed under the Apache License' in text or 'Copyright 2025 Devon' in text

def main():
    count = 0
    for ext, header in EXTENSIONS.items():
        for path in ROOT.rglob(f'*{ext}'):
            # Skip files in .git, artifacts, and build outputs
            if any(p in path.parts for p in ('.git', 'artifacts', 'coq', 'node_modules')):
                continue
            try:
                text = path.read_text(encoding='utf-8')
            except Exception:
                continue
            if has_header(text):
                continue
            # Prepend header
            path.write_text(header + '\n' + text, encoding='utf-8')
            print(f'Prepended header to {path}')
            count += 1
    print(f'Headers added to {count} files')

if __name__ == '__main__':
    main()
