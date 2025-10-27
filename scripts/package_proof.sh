#!/bin/bash
set -e

# Package proof pack
OUTPUT_DIR="/tmp/thiele_proofpack"
python run_composition_experiments.py --output "$OUTPUT_DIR"

# Copy protocol.json
cp protocol.json "$OUTPUT_DIR/"

# Create manifest.json
python -c "
import json
import hashlib
from pathlib import Path

files = []
for path in Path('$OUTPUT_DIR').rglob('*'):
    if path.is_file():
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        files.append({'path': str(path.relative_to('$OUTPUT_DIR')), 'sha256': digest})

manifest = {'ts': 'PUBLICATION', 'files': files}
with open('$OUTPUT_DIR/manifest.json', 'w') as f:
    json.dump(manifest, f, indent=2)
"

# Package into tar.gz
tar -czf proofpack_PUBLICATION.tar.gz -C "$OUTPUT_DIR" .