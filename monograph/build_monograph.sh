#!/bin/bash

set -euo pipefail

cd "$(dirname "$0")"

echo "=== Thiele Machine publications build ==="
echo

if ! command -v pdflatex > /dev/null 2>&1; then
    echo "✗ pdflatex not found"
    exit 1
fi
if ! command -v pdftotext > /dev/null 2>&1; then
    echo "✗ pdftotext not found (install poppler-utils)"
    exit 1
fi

build_document() {
    local stem="$1"
    local text_output="$2"

    echo "--- Building ${stem}.tex ---"
    rm -f "${stem}.pdf" "${stem}.aux" "${stem}.log" "${stem}.out" "${stem}.toc"

    for pass in 1 2 3; do
        echo "Running pdflatex (pass ${pass}/3)..."
        if ! pdflatex -interaction=nonstopmode -halt-on-error "${stem}.tex" \
            > "/tmp/${stem}_build_pass${pass}.log" 2>&1; then
            echo "✗ pdflatex pass ${pass} failed. Error log:"
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

build_document monograph monograph.txt
build_document thiele_machine_math_spec math_spec_plaintext.txt

echo "=== Publications build successful ==="
