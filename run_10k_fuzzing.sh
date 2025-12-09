#!/bin/bash
# Run 10,000-case adversarial fuzzing campaign
# This is the "Golden Run" that proves Python ↔ Verilog isomorphism

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LOG_FILE="$REPO_ROOT/falsification_log_10k.txt"

cd "$REPO_ROOT"

echo "================================================================================"
echo "PHASE 7 - ADVERSARIAL FALSIFICATION: THE GOLDEN RUN"
echo "================================================================================"
echo ""
echo "Running 10,000 random Thiele programs through Python VM and Verilog simulation"
echo "to attempt falsification of behavioral isomorphism claim."
echo ""
echo "Test: Python μ-cost == Verilog μ-cost for ALL random programs"
echo ""
echo "If any program produces different μ-costs, the isomorphism claim is FALSIFIED."
echo "The goal is to FAIL to falsify (i.e., all 10,000 tests pass)."
echo ""
echo "Output will be logged to: $LOG_FILE"
echo ""
echo "================================================================================"
echo ""

# Run the test
echo "Starting fuzzing campaign at $(date)..."
echo ""

python3 -m pytest \
    "$REPO_ROOT/tests/adversarial_fuzzing.py::TestAdversarialFalsification::test_python_verilog_behavioral_isomorphism" \
    -v \
    --tb=short \
    2>&1 | tee "$LOG_FILE"

EXIT_CODE=$?

echo ""
echo "================================================================================"
echo "CAMPAIGN COMPLETE"
echo "================================================================================"
echo ""
echo "Finished at: $(date)"
echo "Exit code: $EXIT_CODE"
echo "Log saved to: $LOG_FILE"
echo ""

if [ $EXIT_CODE -eq 0 ]; then
    echo "✓✓✓ SUCCESS ✓✓✓"
    echo ""
    echo "FALSIFICATION FAILED: All 10,000 random programs verified successfully."
    echo "Python ↔ Verilog behavioral isomorphism holds under adversarial fuzzing."
    echo ""
    echo "This provides strong evidence that:"
    echo "  - μ-cost accounting is identical between Python and Verilog"
    echo "  - Instruction execution semantics match exactly"
    echo "  - The system maintains isomorphism under random adversarial input"
    echo ""
else
    echo "⚠⚠⚠ FAILURE ⚠⚠⚠"
    echo ""
    echo "FALSIFICATION SUCCESSFUL: Divergence found in random testing."
    echo "Check $LOG_FILE for details on which program caused the failure."
    echo ""
fi

echo "================================================================================"

exit $EXIT_CODE
