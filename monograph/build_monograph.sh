#!/bin/bash

set -euo pipefail

cd "$(dirname "$0")"

echo "=== Thiele Machine publications build ==="
echo

# The book is set with LuaLaTeX (its fonts are vendored in fonts/); the
# specification still builds with pdflatex.
for engine in lualatex pdflatex; do
    if ! command -v "$engine" > /dev/null 2>&1; then
        echo "✗ $engine not found"
        exit 1
    fi
done
if ! command -v pdftotext > /dev/null 2>&1; then
    echo "✗ pdftotext not found (install poppler-utils)"
    exit 1
fi

build_document() {
    local engine="$1"
    local stem="$2"
    local text_output="$3"

    echo "--- Building ${stem}.tex ---"
    rm -f "${stem}.pdf" "${stem}.aux" "${stem}.log" "${stem}.out" "${stem}.toc"

    for pass in 1 2 3; do
        echo "Running ${engine} (pass ${pass}/3)..."
        if ! "${engine}" -interaction=nonstopmode -halt-on-error "${stem}.tex" \
            > "/tmp/${stem}_build_pass${pass}.log" 2>&1; then
            echo "✗ ${engine} pass ${pass} failed. Error log:"
            tail -50 "/tmp/${stem}_build_pass${pass}.log"
            exit 1
        fi
    done

    if grep -qiE "Rerun to get (cross-references|outlines)" "${stem}.log"; then
        echo "⚠ ${stem}: cross-references remain unsettled after three passes"
    fi
    pdftotext -layout "${stem}.pdf" "${text_output}"
    local pages
    pages=$(pdfinfo "${stem}.pdf" 2>/dev/null | awk '/Pages:/ {print $2}')
    echo "✓ ${stem}.pdf and ${text_output} (${pages:-unknown} pages)"
    echo
}

python3 ../scripts/book_figures.py --check || {
    echo "✗ monograph/figures/ is stale; run python3 scripts/book_figures.py"
    exit 1
}
build_document lualatex monograph monograph.txt
build_document pdflatex thiele_machine_math_spec math_spec_plaintext.txt

echo "=== Publications build successful ==="
