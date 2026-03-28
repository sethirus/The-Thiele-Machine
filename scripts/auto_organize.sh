#!/usr/bin/env bash
# Safe workspace organizer for The-Thiele-Machine.
# This script cleans transient cache files and writes a folder audit report
# without moving tracked source or proof artifacts.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

echo "[organize] starting safe workspace organization..."

mkdir -p artifacts/inventory

# Remove transient Python/test cache artifacts.
find . -type d \( -name "__pycache__" -o -name ".pytest_cache" -o -name ".mypy_cache" \) -prune -exec rm -rf {} + 2>/dev/null || true
find . -type f \( -name "*.pyc" -o -name "*.pyo" -o -name "*.vcd" \) -delete 2>/dev/null || true

# Remove known empty transient benchmark folder if present.
if [ -d "thielecpu/hardware/rtl/.benchmarks" ] && [ -z "$(ls -A "thielecpu/hardware/rtl/.benchmarks" 2>/dev/null)" ]; then
  rmdir "thielecpu/hardware/rtl/.benchmarks" || true
fi

REPORT="artifacts/inventory/workspace_folder_audit.md"
{
  echo "# Workspace Folder Audit"
  echo
  echo "Generated: $(date -u +"%Y-%m-%dT%H:%M:%SZ")"
  echo
  echo "This report lists top-level entries with file counts and tracked-file counts."
  echo
  echo "| Path | Kind | Files | Dirs | Tracked Files |"
  echo "|---|---:|---:|---:|---:|"

  while IFS= read -r name; do
    rel="./${name}"
    if [ -d "$rel" ]; then
      files="$(find "$rel" -type f 2>/dev/null | wc -l | tr -d ' ')"
      dirs="$(find "$rel" -type d 2>/dev/null | wc -l | tr -d ' ')"
      tracked="$(git ls-files "$name" 2>/dev/null | wc -l | tr -d ' ')"
      echo "| ${name} | dir | ${files} | ${dirs} | ${tracked} |"
    else
      tracked="$(git ls-files "$name" 2>/dev/null | wc -l | tr -d ' ')"
      echo "| ${name} | file | 1 | 0 | ${tracked} |"
    fi
  done < <(find . -maxdepth 1 -mindepth 1 -printf "%f\n" | sort)
} > "$REPORT"

echo "[organize] wrote ${REPORT}"
echo "[organize] done"
