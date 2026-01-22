#!/bin/bash
# Final verification script

echo "=== Final Verification of Thiele Machine Installation ==="
echo ""

# 1. Coq
echo "1. Coq Proof Assistant"
coqc --version | head -1 || echo "❌ Coq not found"
echo "   Compiled files: $(find coq -name '*.vo' | wc -l) .vo files"
echo ""

# 2. Yosys
echo "2. Yosys Synthesis"
yosys -V 2>&1 | head -1 || echo "❌ Yosys not found"
echo ""

# 3. Verilog
echo "3. Icarus Verilog"
iverilog -V 2>&1 | head -1 || echo "❌ iverilog not found"
echo ""

# 4. Python
echo "4. Python Environment"
python3 --version
export PYTHONPATH=/home/runner/work/The-Thiele-Machine/The-Thiele-Machine
python3 -c "import thielecpu; print('   ✅ thielecpu module imports')" || echo "❌ Failed"
echo ""

# 5. Critical files
echo "5. Critical Kernel Proofs"
for file in Subsumption NoFreeInsight MuLedgerConservation BoxCHSH; do
    if [ -f "coq/kernel/${file}.vo" ]; then
        echo "   ✅ ${file}.vo"
    else
        echo "   ❌ ${file}.vo missing"
    fi
done
echo ""

# 6. Synthesis test
echo "6. RTL Synthesis Test"
if [ -f "/tmp/mu_alu_synth.json" ]; then
    echo "   ✅ μ-ALU synthesis output exists"
else
    echo "   ⚠️  No synthesis output (run: yosys -s scripts/synth_mu_alu.ys)"
fi
echo ""

# 7. Inquisitor
echo "7. Inquisitor Report"
if [ -f "INQUISITOR_REPORT.md" ]; then
    HIGH=$(grep "^- HIGH:" INQUISITOR_REPORT.md | head -1)
    echo "   ✅ Report exists: $HIGH"
else
    echo "   ❌ INQUISITOR_REPORT.md not found"
fi
echo ""

echo "=== Verification Complete ==="
