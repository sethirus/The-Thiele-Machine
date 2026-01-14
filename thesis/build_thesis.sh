#!/bin/bash
# Thesis build script with proper error handling

set -e  # Exit on error

cd "$(dirname "$0")"

echo "=== Thiele Machine Thesis Build ==="
echo ""

# Clean previous build
echo "[1/5] Cleaning previous build artifacts..."
rm -f main.pdf main.aux main.log main.out main.toc main.bbl main.blg
rm -f *.aux chapters/*.aux appendices/*.aux
echo "✓ Clean complete"
echo ""

# First pass - resolve references
echo "[2/5] First pdflatex pass (resolving references)..."
if ! pdflatex -interaction=nonstopmode -halt-on-error main.tex > /tmp/thesis_build_pass1.log 2>&1; then
    echo "✗ First pass failed. Error log:"
    tail -50 /tmp/thesis_build_pass1.log
    exit 1
fi
echo "✓ First pass complete"
echo ""

# BibTeX pass
echo "[3/5] Running bibtex..."
if [ -f references.bib ]; then
    if ! bibtex main > /tmp/thesis_build_bibtex.log 2>&1; then
        echo "⚠ BibTeX warnings (non-fatal):"
        tail -20 /tmp/thesis_build_bibtex.log
    else
        echo "✓ BibTeX complete"
    fi
else
    echo "⚠ No references.bib found, skipping"
fi
echo ""

# Second pass - incorporate references
echo "[4/5] Second pdflatex pass (incorporating references)..."
if ! pdflatex -interaction=nonstopmode -halt-on-error main.tex > /tmp/thesis_build_pass2.log 2>&1; then
    echo "✗ Second pass failed. Error log:"
    tail -50 /tmp/thesis_build_pass2.log
    exit 1
fi
echo "✓ Second pass complete"
echo ""

# Final pass - finalize
echo "[5/5] Final pdflatex pass (finalizing)..."
if ! pdflatex -interaction=nonstopmode -halt-on-error main.tex > /tmp/thesis_build_pass3.log 2>&1; then
    echo "✗ Final pass failed. Error log:"
    tail -50 /tmp/thesis_build_pass3.log
    exit 1
fi
echo "✓ Final pass complete"
echo ""

# Check output
if [ -f main.pdf ]; then
    PAGE_COUNT=$(pdfinfo main.pdf 2>/dev/null | grep "Pages:" | awk '{print $2}')
    FILE_SIZE=$(ls -lh main.pdf | awk '{print $5}')
    echo "=== Build Successful ==="
    echo "Output: main.pdf"
    echo "Pages: ${PAGE_COUNT:-unknown}"
    echo "Size: $FILE_SIZE"
    echo ""
    echo "Full build logs in /tmp/thesis_build_*.log"
else
    echo "✗ Build failed - no PDF generated"
    exit 1
fi
