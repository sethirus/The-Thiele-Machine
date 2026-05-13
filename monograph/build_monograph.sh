#!/bin/bash

set -euo pipefail

cd "$(dirname "$0")"

echo "=== Thiele Machine Monograph Build ==="
echo

echo "[1/3] Cleaning previous monograph artifacts..."
rm -f monograph.pdf monograph.aux monograph.log monograph.out monograph.toc
echo "✓ Clean complete"
echo

echo "[2/3] Running pdflatex..."
if ! pdflatex -interaction=nonstopmode -halt-on-error monograph.tex > /tmp/monograph_build_pass1.log 2>&1; then
    echo "✗ pdflatex failed. Error log:"
    tail -50 /tmp/monograph_build_pass1.log
    exit 1
fi
echo "✓ First pass complete"
echo

echo "[3/3] Finalizing pdflatex pass..."
if ! pdflatex -interaction=nonstopmode -halt-on-error monograph.tex > /tmp/monograph_build_pass2.log 2>&1; then
    echo "✗ final pdflatex failed. Error log:"
    tail -50 /tmp/monograph_build_pass2.log
    exit 1
fi
echo "✓ Final pass complete"
echo

if [ -f monograph.pdf ]; then
    PAGE_COUNT=$(pdfinfo monograph.pdf 2>/dev/null | grep "Pages:" | awk '{print $2}')
    FILE_SIZE=$(ls -lh monograph.pdf | awk '{print $5}')
    echo "=== Build Successful ==="
    echo "Output: monograph.pdf"
    echo "Pages: ${PAGE_COUNT:-unknown}"
    echo "Size: $FILE_SIZE"
else
    echo "✗ Build failed - no PDF generated"
    exit 1
fi
