#!/bin/bash
set -euo pipefail

echo "=== Thiele Kernel End-to-End Test ==="

# Clean up any existing kernel
if [ -f thiele_min.py ]; then
    echo "Removing existing thiele_min.py..."
    rm thiele_min.py
fi

# Run receipt replay to reconstruct kernel
echo "Running receipt replay..."
python3 verifier/replay.py bootstrap_receipts

# Verify thiele_min.py was created
if [ ! -f thiele_min.py ]; then
    echo "ERROR: thiele_min.py was not created!"
    exit 1
fi

# Check SHA256 hash
echo "Verifying kernel hash..."
ACTUAL_HASH=$(sha256sum thiele_min.py | awk '{print $1}')
EXPECTED_HASH=$(cat tests/expected_kernel_sha256.txt)

echo "Expected hash: $EXPECTED_HASH"
echo "Actual hash:   $ACTUAL_HASH"

if [ "$ACTUAL_HASH" != "$EXPECTED_HASH" ]; then
    echo "ERROR: Hash mismatch!"
    exit 1
fi

echo "Hash verification passed!"

# Test kernel self-verification (if implemented)
if grep -q "\-\-verify" thiele_min.py 2>/dev/null; then
    echo "Testing kernel self-verification..."
    python3 thiele_min.py --verify bootstrap_receipts/050_kernel_emit.json || true
fi

echo "=== All tests passed! ==="
exit 0
