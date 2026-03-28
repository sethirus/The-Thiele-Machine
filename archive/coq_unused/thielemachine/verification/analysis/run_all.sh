#!/bin/bash
# Master script for ThieleUniversalBridge iterative proof development
# This orchestrates the complete workflow: extract -> analyze -> profile

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIFICATION_DIR="$(dirname "$SCRIPT_DIR")"

echo "======================================================================"
echo "ThieleUniversalBridge Iterative Proof Development - Master Script"
echo "======================================================================"
echo ""
echo "Date: $(date)"
echo "Coq Version: $(coqc --version | head -1)"
echo ""

# Function to run a step with status tracking
run_step() {
    local step_name="$1"
    local step_cmd="$2"
    
    echo "======================================================================"
    echo "STEP: $step_name"
    echo "======================================================================"
    echo ""
    
    if eval "$step_cmd"; then
        echo ""
        echo "✓ $step_name completed successfully"
        echo ""
        return 0
    else
        echo ""
        echo "✗ $step_name failed"
        echo ""
        return 1
    fi
}

# Step 1: Module Extraction
run_step "Module Extraction" \
    "python3 '$SCRIPT_DIR/extract_modules.py'"

# Step 2: Structure Analysis
run_step "Structure Analysis" \
    "bash '$SCRIPT_DIR/analyze_proof_terms.sh'"

# Step 3: Proof Profiling
run_step "Proof Profiling" \
    "python3 '$SCRIPT_DIR/profile_proofs.py'"

# Summary
echo "======================================================================"
echo "WORKFLOW COMPLETE"
echo "======================================================================"
echo ""
echo "Generated files:"
echo "  - modular/*.v              : 14 extracted module files"
echo "  - modular/README.md        : Module index and stats"
echo "  - analysis/profiling_results.json : Detailed timing data"
echo "  - analysis/PROFILING_REPORT.md    : Human-readable analysis"
echo ""
echo "Next steps:"
echo "  1. Review analysis/PROFILING_REPORT.md for bottlenecks"
echo "  2. Use 'make -f Makefile.modular <target>' to compile modules"
echo "  3. See ITERATIVE_DEVELOPMENT_GUIDE.md for workflow details"
echo ""
echo "To rebuild everything:"
echo "  make -f Makefile.modular clean"
echo "  make -f Makefile.modular all"
echo ""
