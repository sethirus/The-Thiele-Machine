#!/usr/bin/env bash
set -euo pipefail

# Helper wrapper that will call the optional publishing scripts in this
# directory. Kept here in case maintainers want to publish in the future.

if [ -z "${ZENODO_TOKEN:-}" ] && [ -z "${OSF_TOKEN:-}" ]; then
  echo "No ZENODO_TOKEN or OSF_TOKEN provided. To publish, export one or both tokens and re-run this script."
  echo "Zenodo: export ZENODO_TOKEN=xxx"
  echo "OSF: export OSF_TOKEN=yyy and OSF_NODE_ID=<nodeid>"
  exit 1
fi

if [ -n "${ZENODO_TOKEN:-}" ]; then
  echo "Publishing to Zenodo..."
  ./publish_to_zenodo.sh || echo "Zenodo publish script failed"
fi

if [ -n "${OSF_TOKEN:-}" ]; then
  if [ -z "${OSF_NODE_ID:-}" ]; then
    echo "OSF_TOKEN present but OSF_NODE_ID is not set — cannot publish to OSF"
  else
    echo "Publishing to OSF..."
    ./publish_to_osf.sh || echo "OSF publish script failed"
  fi
fi

echo "Publish helper finished. If you used Zenodo, note the deposition id printed above."
