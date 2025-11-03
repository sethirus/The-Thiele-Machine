#!/bin/bash
#
# CI script for calorimetry proofpack
#
# Executes analysis and checks all pass/fail gates.
# Returns exit code 0 if all gates pass, non-zero otherwise.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOFPACK_DIR="$(dirname "$SCRIPT_DIR")"
ANALYSIS_DIR="$PROOFPACK_DIR/analysis"
REPORT_PATH="$ANALYSIS_DIR/report.json"

echo "========================================"
echo "Calorimetry Proofpack CI"
echo "========================================"
echo ""

# Check if data exists
if [ ! -f "$PROOFPACK_DIR/data/cal_data.csv" ]; then
    echo "ERROR: No calorimetry data found"
    echo "Please run experiments first or provide synthetic data"
    exit 1
fi

# Run analysis
echo "Running analysis..."
cd "$ANALYSIS_DIR"
python3 analyze_calorimetry.py

# Check if report was generated
if [ ! -f "$REPORT_PATH" ]; then
    echo "ERROR: Analysis did not produce report.json"
    exit 1
fi

# Parse report and check overall pass
echo ""
echo "Checking gates..."
OVERALL_PASS=$(python3 -c "import json; print(json.load(open('$REPORT_PATH'))['overall_pass'])")

if [ "$OVERALL_PASS" = "True" ]; then
    echo ""
    echo "========================================"
    echo "✓ CI PASSED - All gates satisfied"
    echo "========================================"
    exit 0
else
    echo ""
    echo "========================================"
    echo "✗ CI FAILED - Some gates not satisfied"
    echo "========================================"
    
    # Show which gates failed
    echo ""
    echo "Failed gates:"
    python3 -c "
import json
report = json.load(open('$REPORT_PATH'))

def check_gate(name, gate):
    if isinstance(gate, dict):
        if 'pass' in gate:
            if not gate['pass']:
                print(f'  - {name}')
        else:
            for k, v in gate.items():
                check_gate(f'{name}.{k}', v)

for key, value in report.items():
    if key != 'overall_pass':
        check_gate(key, value)
"
    
    exit 1
fi
