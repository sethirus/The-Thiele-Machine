#!/usr/bin/env bash
# Regenerate the full-corpus Print Assumptions receipt from source.
#
# Requires coqc/coqtop and a fully built corpus (`make -C coq`).
# Generates the probe, executes every Print Assumptions query, validates
# result alignment, and publishes the aggregated receipt under artifacts/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if ! command -v coqtop >/dev/null 2>&1; then
    echo "[assumption-receipt] error: coqtop not found on PATH" >&2
    exit 2
fi

echo "[assumption-receipt] 1/3 generating probe from corpus..."
python3 build/probe/build_full_probe.py

# Build the load-path flags from coq/Makefile.conf's COQMF_COQLIBS_NOML, which
# is what coq_makefile actually passes to coqc. Reading _CoqProject directly is
# NOT equivalent: coq_makefile synthesises `-I .` and `-R . Top` for the root
# directory, and coq/ has ~15 root-level .v files (NecessityOfMuLedger.v,
# MuCodingTheorem.v, ThieleMachineComplete.v, ...) reachable only through that
# mapping. Without it coqtop emits
#   Error: Cannot find a physical path bound to logical path MuCodingTheorem.
# and silently drops Print Assumptions blocks, leaving the receipt short
# without any single query obviously failing -- which is why the aggregator
# hard-fails on block/query misalignment rather than trusting the count.
mapfile -t COQ_ARGS < <(
    python3 - <<'PY'
import pathlib, shlex, sys
coqroot = pathlib.Path("coq").resolve()
# coq/Makefile includes Makefile.conf -- NOT Makefile.coq.conf, which is a
# stale leftover from an older coq_makefile invocation and is missing at least
# `-R kernel/reductions Kernel`. Reading the wrong one made coqtop fail on
# Kernel.GasMetering and Kernel.PoSFinality. Read what the build reads.
conf = coqroot / "Makefile.conf"
libs = None
if conf.exists():
    for line in conf.read_text().splitlines():
        if line.startswith("COQMF_COQLIBS_NOML"):
            libs = line.split("=", 1)[1].strip()
            break
if libs is None:
    sys.exit("could not read COQMF_COQLIBS_NOML from coq/Makefile.conf; "
             "run `make -C coq` first so coq_makefile has generated it")
toks = shlex.split(libs)
i = 0
while i < len(toks):
    if toks[i] in ("-R", "-Q") and i + 2 < len(toks):
        # Drop `-R . Top`, exactly as coq/Makefile.local does before invoking
        # coqc. coq_makefile synthesises it, but the corpus is NOT compiled
        # with it: the root-level .vo files therefore contain bare libraries
        # (VerifierModel, MuCodingTheorem, ...), not Top.-prefixed ones.
        # Passing it to coqtop makes every root Require fail with
        #   "contains library X and not library Top.X"
        # which silently drops ~555 Print Assumptions blocks. Root modules are
        # reachable instead via coqtop's implicit cwd load path, which is why
        # this script runs from coq/.
        if not (toks[i + 1] == "." and toks[i + 2] == "Top"):
            phys = (coqroot / toks[i + 1]).resolve()
            print(toks[i]); print(str(phys)); print(toks[i + 2])
        i += 3
    elif toks[i] == "-I" and i + 1 < len(toks):
        print("-I"); print(str((coqroot / toks[i + 1]).resolve()))
        i += 2
    else:
        i += 1
PY
)

echo "[assumption-receipt] 2/3 running Print Assumptions over the corpus..."
mkdir -p build/probe
# Independent batches bound individual process duration and validate query/result
# alignment before publishing combined output. Every query is executed afresh.
python3 scripts/run_assumption_batches.py \
    --jobs "${THIELE_ASSUMPTION_JOBS:-2}" \
    --batch-size "${THIELE_ASSUMPTION_BATCH_SIZE:-2000}" -- "${COQ_ARGS[@]}"

echo "[assumption-receipt] 3/3 aggregating into artifacts/..."
python3 build/probe/aggregate_full_probe.py

echo "[assumption-receipt] done. Artifacts:"
ls -1 artifacts/print_assumptions_all_proofs.* 2>/dev/null || true
