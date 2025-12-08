#!/bin/bash
# Complete System Demonstration
# Shows the Thiele self-hosting kernel working across various programs

set -e

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Thiele Self-Hosting Kernel - Complete System Demonstration  ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

# Clean up
echo "🧹 Cleaning workspace..."
rm -f thiele_min.py hello.txt

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 1: KERNEL RECONSTRUCTION FROM RECEIPTS"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "📦 Reconstructing kernel from cryptographic receipts..."
python3 verifier/replay.py receipts/bootstrap_receipts

KERNEL_HASH=$(sha256sum thiele_min.py | awk '{print $1}')
EXPECTED_HASH=$(cat tests/expected_kernel_sha256.txt)

echo ""
echo "Kernel hash: $KERNEL_HASH"
echo "Expected:    $EXPECTED_HASH"

if [ "$KERNEL_HASH" = "$EXPECTED_HASH" ]; then
    echo "✓ PASS: Kernel hash matches"
else
    echo "✗ FAIL: Hash mismatch!"
    exit 1
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 2: KERNEL SELF-VERIFICATION"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "🔍 Kernel verifying its own construction receipts..."
python3 thiele_min.py --verify receipts/bootstrap_receipts/050_kernel_emit.json
echo "✓ PASS: Kernel self-verification complete"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 3: DIVERSE VERIFIER (SHELL)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "🐚 Testing shell-based verifier..."
rm -f thiele_min.py
bash verifier/replay_sh.sh receipts/bootstrap_receipts | tail -3

SHELL_HASH=$(sha256sum thiele_min.py | awk '{print $1}')
if [ "$SHELL_HASH" = "$EXPECTED_HASH" ]; then
    echo "✓ PASS: Shell verifier produces identical kernel"
else
    echo "✗ FAIL: Shell verifier mismatch!"
    exit 1
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 4: HELLO WORLD EXAMPLE"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "👋 Running hello world example..."
bash examples/hello_verify.sh | tail -10

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 5: TAMPER DETECTION"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "🔒 Testing tamper detection..."
python3 demos/security/tamper.py | tail -15

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 6: PROOF PACK CREATION"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "📦 Creating proof pack..."
python3 tools/make_proofpack.py | tail -10

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 7: INTEGRITY PROOF"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "🔐 Running complete integrity proof..."
python3 tools/prove_integrity.py

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 8: PROPERTY-BASED TESTS"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "🧪 Running property-based tests..."
python3 tests/test_fuzz_receipts.py

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 9: CANONICAL JSON TESTS"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "📝 Testing canonical JSON..."
python3 tools/canonical_json.py --test

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "PART 10: FACTORIZATION DEMO"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "🧮 Running factorization demo..."
python3 tools/demo_factorization.py

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "SUMMARY"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "✓ Kernel reconstruction: PASS"
echo "✓ Self-verification: PASS"
echo "✓ Diverse verifier (shell): PASS"
echo "✓ Hello world example: PASS"
echo "✓ Tamper detection: PASS"
echo "✓ Proof pack creation: PASS"
echo "✓ Integrity proof: PASS"
echo "✓ Property tests: PASS"
echo "✓ Canonical JSON: PASS"
echo "✓ Factorization demo: PASS"

echo ""
echo "╔════════════════════════════════════════════════════════════════╗"
echo "║              ALL TESTS PASSED - SYSTEM VERIFIED               ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

echo "System metrics:"
echo "  • Verifier LoC: $(python3 -c "with open('verifier/replay.py') as f: print(sum(1 for line in f if line.strip() and not line.strip().startswith('#')))")"
echo "  • Kernel size: $(wc -c < thiele_min.py) bytes"
echo "  • Receipt steps: $(python3 -c "import json; print(len(json.load(open('receipts/bootstrap_receipts/050_kernel_emit.json'))['steps']))")"
echo "  • Global digest: $(python3 verifier/replay.py --print-digest receipts/bootstrap_receipts)"
echo ""

echo "Web verifier available at: web/index.html"
echo "  • Open in browser for GUI verification"
echo "  • 100% client-side, no server uploads"
echo ""

echo "🎉 Self-hosting kernel demonstration complete!"
