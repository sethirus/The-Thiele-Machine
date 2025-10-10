# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env bash

cd "$(dirname "$0")/.."

echo "=== Scanning Coq Proof Status ==="
echo ""

# Count Admitted statements (incomplete proofs)
admitted_matches=$(grep -r "Admitted" coq --include="*.v" 2>/dev/null || true)
if [ -z "$admitted_matches" ]; then
    admitted_count=0
else
    admitted_count=$(echo "$admitted_matches" | wc -l | tr -d ' ')
fi

echo "Admitted statements (incomplete proofs): $admitted_count"
if [ "$admitted_count" = "0" ]; then
    echo "  ✅ No incomplete proofs found"
else
    echo "  ⚠️ Found incomplete proofs:"
    echo "$admitted_matches"
fi
echo ""

# Count Axiom declarations (documented assumptions)
axiom_matches=$(grep -r "^Axiom " coq --include="*.v" 2>/dev/null || true)
if [ -z "$axiom_matches" ]; then
    axiom_count=0
else
    axiom_count=$(echo "$axiom_matches" | wc -l | tr -d ' ')
fi

echo "Axiom declarations (documented assumptions): $axiom_count"
if [ "$axiom_count" != "0" ]; then
    echo "  ℹ️ See coq/AXIOM_INVENTORY.md for full list with justifications"
    echo "  ℹ️ Axioms are documented assumptions, NOT incomplete proofs"
fi
echo ""

# Summary
echo "=== Summary ==="
echo "Admitted (incomplete): $admitted_count"
echo "Axioms (documented):   $axiom_count"
echo ""
echo "For detailed axiom analysis: cat coq/AXIOM_INVENTORY.md"
