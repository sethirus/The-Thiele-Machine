#!/bin/bash
# Example: Creating Receipts with Repository Ingestion
# Demonstrates the new archive fetching, directory scanning, and metadata auto-fill features

set -e

echo "========================================="
echo "Thiele Repository Ingestion Examples"
echo "========================================="
echo ""

# Example 1: Directory mode with include patterns
echo "Example 1: Create receipt for web directory (HTML + JS files only)"
echo "-------------------------------------------------------------------"
python3 create_receipt.py \
  --directory web \
  --include "*.html" "*.js" \
  --output /tmp/web_receipt.json

echo ""
echo "✓ Receipt created: /tmp/web_receipt.json"
echo ""

# Example 2: Repository mode (auto-discover build artifacts)
echo "Example 2: Auto-discover build artifacts (if any)"
echo "--------------------------------------------------"
if [ -d "dist" ] || [ -d "build" ] || [ -d "target" ]; then
  python3 create_receipt.py \
    --project . \
    --output /tmp/receipts
  echo "✓ Receipts created in /tmp/receipts/"
else
  echo "⚠ No build directories found, skipping"
fi

echo ""

# Example 3: Show what metadata auto-fill would extract
echo "Example 3: Metadata auto-fill from package manifest"
echo "----------------------------------------------------"
if [ -f "pyproject.toml" ]; then
  echo "Found pyproject.toml - would extract:"
  grep -E "^name|^version|^description" pyproject.toml | head -3 || echo "(metadata fields)"
elif [ -f "package.json" ]; then
  echo "Found package.json - would extract:"
  cat package.json | python3 -m json.tool | grep -E "\"name\"|\"version\"|\"description\"" | head -3 || echo "(metadata fields)"
else
  echo "No package manifest found"
fi

echo ""
echo "========================================="
echo "Examples complete!"
echo "========================================="
echo ""
echo "To verify any receipt:"
echo "  python3 verifier/replay.py /tmp/web_receipt.json"
echo ""
echo "For more information:"
echo "  See REPO_INGESTION_GUIDE.md"
