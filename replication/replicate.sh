#!/usr/bin/env bash
set -euo pipefail

echo "Replication container entrypoint — running canonical pipeline"
cd /workspace

# Default run: generate receipts and verify them
python3 demonstrate_isomorphism.py || { echo "demonstrate_isomorphism.py failed"; exit 2; }
python3 scripts/challenge.py verify receipts || { echo "receipt verification failed"; exit 3; }
# Mechanised Coq replay of canonical receipts (best-effort inside container)
./scripts/verify_truth.sh examples/tsirelson_step_receipts.json || { echo "Coq replay failed"; exit 4; }

# Optionally run Coq proofs if RUN_COQ=true
if [ "${RUN_COQ:-false}" = "true" ] ; then
	echo "Running Coq verification step..."
	if [ -x ./coq/verify_subsumption.sh ]; then
		(cd coq && ./verify_subsumption.sh) || { echo "Coq verification failed"; exit 5; }
	else
		echo "Coq verification script not found or not executable"; exit 6
	fi
fi

# Optionally generate PDF docs if GEN_PDF=true (no-op now that narrative collateral is removed)
if [ "${GEN_PDF:-false}" = "true" ] ; then
        echo "GEN_PDF requested, but narrative PDFs were removed from the curated repository. Skipping."
fi

echo "Replication completed — results in /workspace/experiments" 
