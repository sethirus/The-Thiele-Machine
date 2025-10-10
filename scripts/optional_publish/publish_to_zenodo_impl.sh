#!/usr/bin/env bash
set -euo pipefail

# Original implementation moved here. This script is the real implementation
# invoked by publish_to_zenodo.sh wrapper in this directory.

if [ -z "${ZENODO_TOKEN:-}" ]; then
  echo "ERROR: ZENODO_TOKEN environment variable is not set. Create one at https://zenodo.org/account/settings/applications/"
  exit 1
fi

DEPOSITION_ID=${1:-}
TAR_PATH=${2:-The-Thiele-Machine-v1.0.2.tar.gz}

# Files we publish by default (change as needed)
FILES=("$TAR_PATH" "CITATION.cff" "artifacts/MANIFEST.sha256" "documents/The_Thiele_Machine.pdf")

# Minimal metadata payload; users can edit or extend the generated metadata.json
cat > /tmp/zenodo_metadata.json <<EOF
{
  "metadata": {
    "title": "The Thiele Machine",
    "upload_type": "software",
    "publication_date": "2025-10-10",
    "creators": [ { "name": "Thiele, Devon" } ],
    "description": "The Thiele Machine (v1.0.2). See CITATION.cff for full metadata and preferred citation. This deposition contains the release tarball, manifest checksums, and the compiled paper PDF.",
    "keywords": ["Thiele Machine","formal-verification","Coq","Verilog","reproducibility"]
  }
}
EOF

ZENODO_API="https://zenodo.org/api/deposit/depositions"

if [ -z "$DEPOSITION_ID" ]; then
  echo "Creating a new Zenodo deposition..."
  RESPONSE=$(curl -s -X POST "$ZENODO_API?access_token=$ZENODO_TOKEN" -H "Content-Type: application/json" -d @/tmp/zenodo_metadata.json)
  DEPOSITION_ID=$(echo "$RESPONSE" | python -c "import sys, json; print(json.load(sys.stdin)['id'])")
  DOICODE=$(echo "$RESPONSE" | python -c "import sys, json; print(json.load(sys.stdin).get('doi',''))")
  echo "Created deposition id=$DEPOSITION_ID doi=$DOICODE"
else
  echo "Updating metadata for deposition id=$DEPOSITION_ID..."
  curl -s -X PUT "$ZENODO_API/$DEPOSITION_ID?access_token=$ZENODO_TOKEN" -H "Content-Type: application/json" -d @/tmp/zenodo_metadata.json >/dev/null
fi

# Upload files
for F in "${FILES[@]}"; do
  if [ ! -f "$F" ]; then
    echo "Warning: file $F not found, skipping"
    continue
  fi
  echo "Uploading $F to deposition $DEPOSITION_ID..."
  curl -s -X POST "$ZENODO_API/$DEPOSITION_ID/files?access_token=$ZENODO_TOKEN" -F "file=@$F" || { echo "Upload failed for $F"; exit 2; }

done

# Publish (optional) — if you want to publish immediately set PUBLISH=1
if [ "${PUBLISH:-0}" -ne 0 ]; then
  echo "Publishing deposition $DEPOSITION_ID..."
  curl -s -X POST "$ZENODO_API/$DEPOSITION_ID/actions/publish?access_token=$ZENODO_TOKEN"
fi

echo "Done. Deposition id: $DEPOSITION_ID"

exit 0
