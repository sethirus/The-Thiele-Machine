#!/bin/bash
# Comprehensive Coq build script with dependency resolution
# Compiles all Coq files in proper dependency order

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_ROOT"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "=== Thiele Machine Coq Build System ==="
echo ""

# Clean old artifacts
echo "🧹 Cleaning old build artifacts..."
find coq -name "*.vo" -o -name "*.vok" -o -name "*.vos" -o -name "*.glob" -o -name ".*.aux" | xargs rm -f 2>/dev/null || true

# Use the generated Makefile
if [ ! -f "Makefile.coq" ]; then
    echo "📝 Generating Makefile.coq..."
    coq_makefile -f _CoqProject -o Makefile.coq
fi

echo ""
echo "🔨 Building all Coq files..."
echo "   (Using parallel compilation with $(nproc) cores)"
echo ""

# Build with make, showing progress
if make -f Makefile.coq -j$(nproc) 2>&1 | tee /tmp/coq_build.log; then
    echo ""
    echo -e "${GREEN}✅ SUCCESS: All Coq files compiled${NC}"
    
    # Count compiled files
    vo_count=$(find coq -name "*.vo" | wc -l)
    v_count=$(find coq -name "*.v" | wc -l)
    echo "   Compiled: $vo_count/$v_count files"
    
    # Run inquisitor check
    echo ""
    echo "🔍 Running inquisitor validation..."
    if python scripts/inquisitor.py --strict --coq-root coq; then
        echo -e "${GREEN}✅ INQUISITOR: PASS${NC}"
        echo "   Zero axioms, zero admits"
    else
        echo -e "${YELLOW}⚠️  INQUISITOR: Issues found${NC}"
        exit 1
    fi
    
else
    echo ""
    echo -e "${RED}❌ COMPILATION FAILED${NC}"
    echo ""
    echo "Errors found:"
    grep "Error:" /tmp/coq_build.log | head -20
    echo ""
    echo "Full log: /tmp/coq_build.log"
    exit 1
fi

echo ""
echo "=== Build Complete ==="
