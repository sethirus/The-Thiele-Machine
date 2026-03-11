#!/bin/bash
# Thiele Machine - Auto-organize script
# Moves build artifacts and cache files to appropriate directories

set -e

echo "🧹 Auto-organizing Thiele Machine workspace..."

# Create directories if they don't exist
mkdir -p .build_cache .test_artifacts .generated

# Move Coq compilation artifacts
find . -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" -o -name "*.aux" | xargs -I {} mv {} .build_cache/ 2>/dev/null || true

# Move Python cache
find . -name "__pycache__" -type d | xargs -I {} mv {} .build_cache/ 2>/dev/null || true

# Move test artifacts
find . -name "*.vcd" -o -name "*.log" -o -name "yosys_debug.log" | xargs -I {} mv {} .test_artifacts/ 2>/dev/null || true

# Move generated files
find . -name "*extracted.ml" -o -name "*extracted.mli" | xargs -I {} mv {} .generated/ 2>/dev/null || true

# Move build directories
if [ -d "build" ]; then
    mv build .generated/
fi

echo "✅ Workspace organized!"
echo "📁 .build_cache/ - Coq artifacts, Python cache"
echo "📁 .test_artifacts/ - VCD files, logs"
echo "📁 .generated/ - Extracted code, build outputs"