#!/bin/bash
# Analysis script to measure proof term sizes and compilation times
# for the ThieleUniversalBridge modular decomposition

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIFICATION_DIR="$(dirname "$SCRIPT_DIR")"
COQ_DIR="$(dirname "$(dirname "$VERIFICATION_DIR")")"
MODULE_DIR="$VERIFICATION_DIR/modular"

echo "=== ThieleUniversalBridge Proof Analysis ==="
echo "Date: $(date)"
echo "Coq Version: $(coqc --version | head -1)"
echo ""

# Function to compile a single module and measure time
compile_module() {
    local module_file="$1"
    local module_name=$(basename "$module_file" .v)
    
    echo "--- Compiling $module_name ---"
    
    # Time the compilation
    local start_time=$(date +%s.%N)
    
    if timeout 300 coqc -Q "$COQ_DIR" "" "$module_file" 2>&1 | tee "/tmp/${module_name}_compile.log"; then
        local end_time=$(date +%s.%N)
        local duration=$(echo "$end_time - $start_time" | bc)
        
        echo "✓ $module_name compiled successfully in ${duration}s"
        
        # Check .vo file size
        local vo_file="${module_file%.v}.vo"
        if [ -f "$vo_file" ]; then
            local vo_size=$(stat -f%z "$vo_file" 2>/dev/null || stat -c%s "$vo_file")
            echo "  .vo file size: $vo_size bytes"
        fi
        
        # Check for large proof terms in the log
        if grep -q "Warning.*proof term" "/tmp/${module_name}_compile.log"; then
            echo "  ⚠ Large proof term warnings detected"
        fi
        
        echo ""
        return 0
    else
        local end_time=$(date +%s.%N)
        local duration=$(echo "$end_time - $start_time" | bc)
        echo "✗ $module_name failed or timed out after ${duration}s"
        echo ""
        return 1
    fi
}

# Function to extract proof statistics from a module
analyze_module_structure() {
    local module_file="$1"
    local module_name=$(basename "$module_file" .v)
    
    echo "--- Analyzing $module_name structure ---"
    
    # Count definitions, lemmas, theorems
    local def_count=$(grep -c "^Definition\|^Fixpoint" "$module_file" || true)
    local lemma_count=$(grep -c "^Lemma\|^Time Lemma" "$module_file" || true)
    local theorem_count=$(grep -c "^Theorem\|^Time Theorem" "$module_file" || true)
    local admitted_count=$(grep -c "Admitted\." "$module_file" || true)
    local qed_count=$(grep -c "Qed\." "$module_file" || true)
    
    echo "  Definitions: $def_count"
    echo "  Lemmas: $lemma_count"
    echo "  Theorems: $theorem_count"
    echo "  Completed (Qed): $qed_count"
    echo "  Admitted: $admitted_count"
    
    if [ $admitted_count -gt 0 ]; then
        echo "  ⚠ Module has $admitted_count admitted proofs"
    fi
    
    echo ""
}

# Main analysis flow
echo "=== Phase 1: Module Structure Analysis ==="
echo ""

if [ -d "$MODULE_DIR" ]; then
    for module in "$MODULE_DIR"/*.v; do
        if [ -f "$module" ]; then
            analyze_module_structure "$module"
        fi
    done
else
    echo "Module directory not found: $MODULE_DIR"
    echo "Run the modularization script first."
fi

echo ""
echo "=== Phase 2: Module Compilation and Timing ==="
echo ""

if [ -d "$MODULE_DIR" ]; then
    # Compile modules in dependency order
    for module in "$MODULE_DIR"/*.v; do
        if [ -f "$module" ]; then
            compile_module "$module" || true
        fi
    done
else
    echo "Module directory not found: $MODULE_DIR"
fi

echo ""
echo "=== Analysis Complete ==="
echo "See /tmp/*_compile.log for detailed compilation logs"
