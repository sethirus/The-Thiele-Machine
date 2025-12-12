#!/usr/bin/env bash
set -euo pipefail

# Install proof tools required by the verification workflow (drat-trim, lrat-check)
# This script first attempts to install via apt, and on failure builds from source.

echo "Attempting to install proof tools via apt-get (drat-trim lrat-check)"
retry=0
max_retries=2
installed=0
while [ $retry -le $max_retries ]; do
  if sudo apt-get update -y && sudo apt-get install -y drat-trim lrat-check 2>/dev/null; then
    echo "Proof tools installed via apt-get"
    installed=1
    break
  fi
  echo "apt-get install failed (attempt $retry), retrying..."
  sleep 2
  retry=$((retry+1))
done

if [ "$installed" -eq 1 ]; then
  echo "Proof tools available via apt"
  exit 0
fi

# If apt failed, build from source
echo "Building proof tools from source..."

# Install build dependencies
sudo apt-get install -y build-essential wget unzip || true

# Build drat-trim
echo "Building drat-trim..."
TMPDIR=$(mktemp -d)
cd "$TMPDIR"
wget -q https://github.com/marijnheule/drat-trim/archive/refs/heads/master.zip -O drat-trim.zip || {
  echo "Warning: Failed to download drat-trim. Tool will not be available." >&2
  cd -
  rm -rf "$TMPDIR"
  exit 0
}
unzip -q drat-trim.zip
cd drat-trim-master
make || {
  echo "Warning: Failed to build drat-trim. Tool will not be available." >&2
  cd -
  rm -rf "$TMPDIR"
  exit 0
}
sudo cp drat-trim /usr/local/bin/ || {
  echo "Warning: Failed to install drat-trim to /usr/local/bin/. Tool will not be available." >&2
}
cd -

# Build lrat-check  
echo "Building lrat-check..."
cd "$TMPDIR"
wget -q https://github.com/marijnheule/lrat-check/archive/refs/heads/master.zip -O lrat-check.zip || {
  echo "Warning: Failed to download lrat-check. Tool will not be available." >&2
  rm -rf "$TMPDIR"
  exit 0
}
unzip -q lrat-check.zip
cd lrat-check-master
make || {
  echo "Warning: Failed to build lrat-check. Tool will not be available." >&2
  rm -rf "$TMPDIR"
  exit 0
}
sudo cp lrat-check /usr/local/bin/ || {
  echo "Warning: Failed to install lrat-check to /usr/local/bin/. Tool will not be available." >&2
}
cd -

# Cleanup
rm -rf "$TMPDIR"

# Verify installation
if command -v drat-trim &> /dev/null && command -v lrat-check &> /dev/null; then
  echo "✓ Proof tools successfully built and installed"
  exit 0
else
  echo "Warning: Some proof tools may not be available. CI will continue." >&2
  exit 0
fi
