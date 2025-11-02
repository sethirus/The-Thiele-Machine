#!/bin/bash
# Simple hello world example for newcomers
# Demonstrates the minimal receipt verification workflow

set -e

echo "=== Thiele Receipt Verification - Hello World Example ==="
echo ""

# Clean up any existing hello.txt
if [ -f hello.txt ]; then
    echo "Removing existing hello.txt..."
    rm hello.txt
fi

# Create temporary directory with just hello receipt
TEMP_DIR=$(mktemp -d)
trap 'rm -rf "$TEMP_DIR"' EXIT
cp examples/000_hello.json "$TEMP_DIR/"

# Run verification
echo "Verifying hello.txt receipt..."
python3 verifier/replay.py "$TEMP_DIR"

# Show the result
if [ -f hello.txt ]; then
    echo ""
    echo "✓ Success! Generated file:"
    echo "---"
    cat hello.txt
    echo "---"
    echo ""
    echo "File hash: $(sha256sum hello.txt | awk '{print $1}')"
    echo "Expected:  bcfc4d9478773c2947d6301bd78d59c273c978a6f83871ca08281c7264d8877e"
    echo ""
    echo "This demonstrates the core concept:"
    echo "  1. Receipts are cryptographic proofs of construction"
    echo "  2. The verifier reconstructs files from receipts"
    echo "  3. Every byte is hash-verified"
    echo ""
    echo "Try the full kernel next:"
    echo "  python3 verifier/replay.py bootstrap_receipts"
else
    echo "ERROR: hello.txt was not created!"
    exit 1
fi
