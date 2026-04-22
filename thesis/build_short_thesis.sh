#!/bin/bash

set -euo pipefail

cd "$(dirname "$0")"

echo "=== Thiele Machine Short Thesis Build ==="
echo

echo "[1/3] Cleaning previous short thesis artifacts..."
rm -f short_thesis.pdf short_thesis.aux short_thesis.log short_thesis.out short_thesis.toc
echo "✓ Clean complete"
echo

echo "[2/3] Running pdflatex..."
if ! pdflatex -interaction=nonstopmode -halt-on-error short_thesis.tex > /tmp/short_thesis_build_pass1.log 2>&1; then
    echo "✗ pdflatex failed. Error log:"
    tail -50 /tmp/short_thesis_build_pass1.log
    exit 1
fi
echo "✓ First pass complete"
echo

echo "[3/3] Finalizing pdflatex pass..."
if ! pdflatex -interaction=nonstopmode -halt-on-error short_thesis.tex > /tmp/short_thesis_build_pass2.log 2>&1; then
    echo "✗ final pdflatex failed. Error log:"
    tail -50 /tmp/short_thesis_build_pass2.log
    exit 1
fi
echo "✓ Final pass complete"
echo

if [ -f short_thesis.pdf ]; then
    PAGE_COUNT=$(pdfinfo short_thesis.pdf 2>/dev/null | grep "Pages:" | awk '{print $2}')
    FILE_SIZE=$(ls -lh short_thesis.pdf | awk '{print $5}')
    echo "=== Build Successful ==="
    echo "Output: short_thesis.pdf"
    echo "Pages: ${PAGE_COUNT:-unknown}"
    echo "Size: $FILE_SIZE"
else
    echo "✗ Build failed - no PDF generated"
    exit 1
fi