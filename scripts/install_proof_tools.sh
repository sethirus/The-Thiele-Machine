#!/usr/bin/env bash
set -euo pipefail

# Install proof tools required by the verification workflow (drat-trim, lrat-check)
# This script first attempts to install via apt, and on failure it exits non-zero.
# CI callers that require strict enforcement should fail the job if this script
# exits with a non-zero status.

echo "Attempting to install proof tools via apt-get (drat-trim lrat-check)"
retry=0
max_retries=2
while [ $retry -le $max_retries ]; do
  if sudo apt-get update -y && sudo apt-get install -y drat-trim lrat-check; then
    echo "Proof tools installed via apt-get"
    exit 0
  fi
  echo "apt-get install failed (attempt $retry), retrying..."
  sleep 2
  retry=$((retry+1))
done

echo "Failed to install proof tools via apt-get. This CI configuration requires drat-trim and lrat-check to be available."
exit 1
