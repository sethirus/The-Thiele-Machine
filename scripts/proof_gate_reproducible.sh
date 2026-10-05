#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COQ_DIR="$ROOT/coq"
MINIMAL_DIR="$ROOT/minimal"
ART_DIR="$ROOT/artifacts/proof_gate"
mkdir -p "$ART_DIR"

{
  echo "proof_gate_started=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "repo=$ROOT"
  echo "coq_dir=$COQ_DIR"
} > "$ART_DIR/metadata.txt"

cd "$ROOT"

echo "[proof] clean rebuild"
make coq-clean > "$ART_DIR/make_clean.log" 2>&1
rm -f "$COQ_DIR/Makefile" "$COQ_DIR/Makefile.conf" "$COQ_DIR/.Makefile.d"
find "$COQ_DIR" -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '*.aux' \) -delete
(
  cd "$COQ_DIR"
  coq_makefile -f _CoqProject -o Makefile
  # A clean rebuild is mandatory. Keep the parallel width bounded for CI
  # memory while allowing a runner to choose its own safe width.
  proof_jobs="${THIELE_PROOF_JOBS:-$(nproc 2>/dev/null || echo 2)}"
  if (( proof_jobs > 4 )); then proof_jobs=4; fi
  make V=1 -j"$proof_jobs"
) > "$ART_DIR/make_build.log" 2>&1

echo "[proof] zero Admitted gate"
# Use ^\s*Admitted\. to match only actual proof-hole tactics, not comments that
# say "Zero Admitted." (e.g., (* ... zero Admitted. *)) which are status notes.
admitted_count=$(grep -Rns --include='*.v' '^\s*Admitted\.' "$COQ_DIR" "$MINIMAL_DIR" | grep -v patches | wc -l || true)
echo "admitted_count=$admitted_count" | tee "$ART_DIR/admitted_count.txt"
if [[ "$admitted_count" != "0" ]]; then
  grep -Rns --include='*.v' '^\s*Admitted\.' "$COQ_DIR" "$MINIMAL_DIR" | grep -v patches > "$ART_DIR/admitted_hits.txt" || true
  echo "FAIL: found Admitted proofs"
  exit 1
fi

echo "[proof] coqchk reproducibility gate"
# Build the -R/-Q load-path arguments from _CoqProject so the gate stays in
# sync with the project layout (kernel sources live under
# coq/kernel/{foundation,nfi,quantum,...}, all mapped to logical namespace
# Kernel; the small machine is ../minimal, namespace Minimal).
COQCHK_LOADPATH=$(awk '/^-(R|Q)[ \t]/ {print $1, $2, $3}' "$COQ_DIR/_CoqProject" | tr '\n' ' ')
# Every module in the project, by its logical name, so coqchk re-checks the
# whole kept corpus and everything it loads.
COQCHK_MODULES=$(python3 - "$COQ_DIR/_CoqProject" <<'PY'
import os, re, sys
project = sys.argv[1]
coq_dir = os.path.dirname(project)
maps, files = [], []
for raw in open(project, encoding="utf-8").read().splitlines():
    line = raw.strip()
    m = re.match(r"-(R|Q)\s+(\S+)\s+(\S+)", line)
    if m:
        maps.append((os.path.normpath(m.group(2)), m.group(3)))
    elif line.endswith(".v") and not line.startswith("#"):
        files.append(os.path.normpath(line))
names = []
for f in files:
    best = None
    for d, ns in maps:
        if f.startswith(d + os.sep) and (best is None or len(d) > len(best[0])):
            best = (d, ns)
    if best is None:
        sys.exit("no load-path mapping for " + f)
    rel = f[len(best[0]) + 1:-2].replace(os.sep, ".")
    names.append(best[1] + "." + rel)
print(" ".join(sorted(names)))
PY
)
(
  cd "$COQ_DIR"
  coqchk $COQCHK_LOADPATH $COQCHK_MODULES
) > "$ART_DIR/coqchk_all.log" 2>&1

sha256sum "$ART_DIR"/*.log "$ART_DIR"/*.txt > "$ART_DIR/checksums.sha256"

echo "proof_gate_finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$ART_DIR/metadata.txt"
echo "[proof] PASS"
