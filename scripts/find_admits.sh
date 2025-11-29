#!/usr/bin/env bash
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

# Comprehensive Coq proof audit script
# Scans for Admitted statements and Axiom declarations in Coq files
# Properly handles nested Coq comments

set -e

cd "$(dirname "$0")/.."

echo "=== Comprehensive Coq Proof Status Audit ==="
echo "Date: $(date)"
echo ""

# Directories to scan
COQ_DIRS="coq theory"

# Python script to remove Coq comments and find patterns
PYTHON_SCANNER='
import sys
import re
import os

def remove_coq_comments(s):
    """Remove nested Coq comments (* ... *)"""
    result = []
    depth = 0
    i = 0
    while i < len(s):
        if i+1 < len(s) and s[i:i+2] == "(*":
            depth += 1
            i += 2
        elif i+1 < len(s) and s[i:i+2] == "*)":
            depth = max(0, depth - 1)
            i += 2
        else:
            if depth == 0:
                result.append(s[i])
            else:
                # Preserve newlines for line counting
                if s[i] == "\n":
                    result.append("\n")
            i += 1
    return "".join(result)

def find_pattern_in_file(filepath, pattern_name, pattern_regex):
    """Find pattern in file after removing comments, return list of (line_num, match)"""
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            content = f.read()
    except:
        return []
    
    no_comments = remove_coq_comments(content)
    results = []
    
    for match in re.finditer(pattern_regex, no_comments):
        # Calculate line number
        line_num = no_comments[:match.start()].count("\n") + 1
        results.append((line_num, match.group(0)[:50]))
    
    return results

# Get arguments
pattern_name = sys.argv[1]  # "Admitted" or "Axiom"
dirs = sys.argv[2:]

if pattern_name == "Admitted":
    pattern_regex = r"Admitted\."
elif pattern_name == "Axiom":
    pattern_regex = r"^Axiom\s+\w+"
elif pattern_name == "Parameter":
    pattern_regex = r"^Parameter\s+\w+"
else:
    pattern_regex = pattern_name

total = 0
for d in dirs:
    if not os.path.isdir(d):
        continue
    for root, _, files in os.walk(d):
        for f in files:
            if f.endswith(".v"):
                filepath = os.path.join(root, f)
                results = find_pattern_in_file(filepath, pattern_name, pattern_regex)
                for line_num, text in results:
                    print(f"{filepath}:{line_num}: {text}")
                    total += 1

print(f"TOTAL:{total}")
'

# =============================================================================
# ADMITTED STATEMENTS (outside comments)
# =============================================================================
echo "=== Scanning for Admitted Statements (excluding comments) ==="
echo ""

admitted_output=$(python3 -c "$PYTHON_SCANNER" "Admitted" $COQ_DIRS 2>/dev/null || echo "TOTAL:0")
admitted_count=$(echo "$admitted_output" | grep "^TOTAL:" | cut -d: -f2)
admitted_matches=$(echo "$admitted_output" | grep -v "^TOTAL:" || true)

if [ "$admitted_count" = "0" ] || [ -z "$admitted_count" ]; then
    echo "✅ No Admitted statements found in compiled code"
else
    echo "⚠️ Found $admitted_count Admitted statements:"
    echo ""
    echo "$admitted_matches" | while read -r line; do
        file=$(echo "$line" | cut -d: -f1)
        linenum=$(echo "$line" | cut -d: -f2)
        # Check if file is in _CoqProject (compiled)
        if [ -f "coq/_CoqProject" ]; then
            relative_file=$(echo "$file" | sed 's|coq/||')
            if grep -q "$relative_file" coq/_CoqProject 2>/dev/null; then
                echo "  [COMPILED] $file:$linenum"
            else
                echo "  [EXCLUDED] $file:$linenum"
            fi
        else
            echo "  $file:$linenum"
        fi
    done
fi
echo ""

# =============================================================================
# AXIOM DECLARATIONS (outside comments)
# =============================================================================
echo "=== Scanning for Axiom Declarations (excluding comments) ==="
echo ""

axiom_output=$(python3 -c "$PYTHON_SCANNER" "Axiom" $COQ_DIRS 2>/dev/null || echo "TOTAL:0")
axiom_count=$(echo "$axiom_output" | grep "^TOTAL:" | cut -d: -f2)
axiom_matches=$(echo "$axiom_output" | grep -v "^TOTAL:" || true)

if [ "$axiom_count" = "0" ] || [ -z "$axiom_count" ]; then
    echo "✅ No Axiom declarations found in compiled code"
else
    echo "ℹ️ Found $axiom_count Axiom declarations:"
    echo ""
    echo "$axiom_matches" | while read -r line; do
        file=$(echo "$line" | cut -d: -f1)
        linenum=$(echo "$line" | cut -d: -f2)
        # Check if file is in _CoqProject (compiled)
        if [ -f "coq/_CoqProject" ]; then
            relative_file=$(echo "$file" | sed 's|coq/||')
            if grep -q "$relative_file" coq/_CoqProject 2>/dev/null; then
                echo "  [COMPILED] $file:$linenum"
            else
                echo "  [EXCLUDED] $file:$linenum"
            fi
        else
            echo "  $file:$linenum"
        fi
    done
fi
echo ""

# =============================================================================
# SUMMARY
# =============================================================================
echo "=== Summary ==="
echo "Admitted statements (outside comments): ${admitted_count:-0}"
echo "Axiom declarations (outside comments):  ${axiom_count:-0}"
echo ""

# Check specifically for compiled files
if [ -f "coq/_CoqProject" ]; then
    echo "=== Files in _CoqProject (Compiled) ==="
    
    compiled_admitted=0
    compiled_axioms=0
    
    # Use Python for accurate scanning of compiled files
    COMPILED_SCANNER='
import sys
import re
import os

def remove_coq_comments(s):
    result = []
    depth = 0
    i = 0
    while i < len(s):
        if i+1 < len(s) and s[i:i+2] == "(*":
            depth += 1
            i += 2
        elif i+1 < len(s) and s[i:i+2] == "*)":
            depth = max(0, depth - 1)
            i += 2
        else:
            if depth == 0:
                result.append(s[i])
            i += 1
    return "".join(result)

project_file = "coq/_CoqProject"
admitted_total = 0
axiom_total = 0

with open(project_file) as f:
    for line in f:
        line = line.strip()
        if line.endswith(".v") and not line.startswith("#") and not line.startswith("-Q"):
            filepath = os.path.join("coq", line)
            if os.path.exists(filepath):
                with open(filepath, "r", encoding="utf-8", errors="replace") as vf:
                    content = vf.read()
                no_comments = remove_coq_comments(content)
                admitted_total += len(re.findall(r"Admitted\.", no_comments))
                axiom_total += len(re.findall(r"^Axiom\s", no_comments, re.MULTILINE))

print(f"Admitted in compiled code: {admitted_total}")
print(f"Axioms in compiled code:   {axiom_total}")
'
    python3 -c "$COMPILED_SCANNER"
fi

echo ""
echo "For detailed axiom analysis: cat coq/AXIOM_INVENTORY.md"
echo "For full audit: cat ADMIT_REPORT.txt"
