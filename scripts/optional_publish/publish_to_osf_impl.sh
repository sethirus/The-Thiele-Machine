#!/usr/bin/env bash
set -euo pipefail

if [ -z "${OSF_NODE_ID:-}" ]; then
  echo "ERROR: OSF_NODE_ID must be set (the target project node id)."
  exit 1
fi

if ! command -v osf >/dev/null 2>&1; then
  echo "osfclient is not installed. Install it with: pip install osfclient"
  exit 2
fi

if [ -z "${OSF_TOKEN:-}" ]; then
  echo "ERROR: OSF_TOKEN environment variable is not set. Create a personal access token at https://osf.io/settings/tokens/"
  exit 1
fi

# Files to upload (customise as necessary)
FILES=("The-Thiele-Machine-v1.0.2.tar.gz" "CITATION.cff" "artifacts/MANIFEST.sha256" "documents/The_Thiele_Machine.pdf")

# We use the 'osf' CLI's upload facility. The CLI will use a configuration file
# stored at ~/.osfclient; we avoid interactive login by exporting OSF_TOKEN as
# the OSF_ACCESS_TOKEN environment variable used by osfclient.
export OSF_ACCESS_TOKEN="$OSF_TOKEN"

for f in "${FILES[@]}"; do
  if [ ! -f "$f" ]; then
    echo "Skipping $f (not found)"
    continue
  fi
  echo "Uploading $f to OSF node $OSF_NODE_ID..."
  osf upload $OSF_NODE_ID $f || { echo "osfclient upload failed for $f"; exit 3; }
done

echo "Done uploading to OSF."

exit 0
