#!/bin/bash

set -euo pipefail

cd "$(dirname "$0")"

echo "=== Thiele Machine Monograph Build ==="
echo

echo "[1/5] Cleaning previous monograph artifacts..."
rm -f monograph.pdf monograph.aux monograph.log monograph.out monograph.toc
echo "✓ Clean complete"
echo

echo "[2/5] Running pdflatex (pass 1/3)..."
if ! pdflatex -interaction=nonstopmode -halt-on-error monograph.tex > /tmp/monograph_build_pass1.log 2>&1; then
    echo "✗ pdflatex pass 1 failed. Error log:"
    tail -50 /tmp/monograph_build_pass1.log
    exit 1
fi
echo "✓ First pass complete"
echo

echo "[3/5] Running pdflatex (pass 2/3)..."
if ! pdflatex -interaction=nonstopmode -halt-on-error monograph.tex > /tmp/monograph_build_pass2.log 2>&1; then
    echo "✗ pdflatex pass 2 failed. Error log:"
    tail -50 /tmp/monograph_build_pass2.log
    exit 1
fi
echo "✓ Second pass complete"
echo

# Third pass is not optional: a TOC + cross-references + hyperref outlines need
# three passes to settle whenever an edit shifts pagination. Two passes can leave
# stale "Rerun to get cross-references right" page numbers in the committed PDF.
echo "[4/5] Running pdflatex (pass 3/3, settling cross-references)..."
if ! pdflatex -interaction=nonstopmode -halt-on-error monograph.tex > /tmp/monograph_build_pass3.log 2>&1; then
    echo "✗ pdflatex pass 3 failed. Error log:"
    tail -50 /tmp/monograph_build_pass3.log
    exit 1
fi
if grep -qiE "Rerun to get (cross-references|outlines)" monograph.log; then
    echo "⚠ cross-references still unsettled after 3 passes; run the build once more"
else
    echo "✓ Cross-references settled"
fi
echo

echo "[5/5] Generating plaintext (monograph.txt)..."
if [ ! -f monograph.pdf ]; then
    echo "✗ monograph.pdf not found; cannot generate plaintext"
    exit 1
fi
if ! command -v pdftotext > /dev/null 2>&1; then
    echo "✗ pdftotext not found (install poppler-utils); monograph.txt would go stale"
    exit 1
fi
pdftotext -layout monograph.pdf monograph.txt
echo "✓ Plaintext regenerated: monograph.txt"
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
