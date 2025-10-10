#!/usr/bin/env bash
set -euo pipefail

echo "Replication container entrypoint — running canonical pipeline"
cd /workspace

# Default run: generate receipts, verify, run analysis
python3 demonstrate_isomorphism.py || { echo "demonstrate_isomorphism.py failed"; exit 2; }
python3 scripts/challenge.py verify receipts || { echo "receipt verification failed"; exit 3; }
# Mechanised Coq replay of canonical receipts (best-effort inside container)
./scripts/verify_truth.sh examples/tsirelson_step_receipts.json || { echo "Coq replay failed"; exit 4; }
# Run extended analysis by default
python3 experiments/run_analysis_extended.py || { echo "extended analysis failed"; exit 4; }

# Optionally run Coq proofs if RUN_COQ=true
if [ "${RUN_COQ:-false}" = "true" ] ; then
	echo "Running Coq verification step..."
	if [ -x ./coq/verify_subsumption.sh ]; then
		(cd coq && ./verify_subsumption.sh) || { echo "Coq verification failed"; exit 5; }
	else
		echo "Coq verification script not found or not executable"; exit 6
	fi
fi

# Generate dashboard
python3 experiments/generate_dashboard.py || { echo "dashboard generation failed"; exit 7; }

# Optionally generate PDF docs if GEN_PDF=true
if [ "${GEN_PDF:-false}" = "true" ] ; then
	echo "Generating PDF documents..."
	if command -v pandoc >/dev/null 2>&1 ; then
		pandoc EVIDENCE_AT_A_GLANCE.md DECLARATION_OF_INDEPENDENCE.md -o experiments/Declaration_Evidence.pdf || { echo "pandoc failed"; exit 8; }
	else
		echo "pandoc not found; skipping PDF generation";
	fi
fi

echo "Replication completed — results in /workspace/experiments" 
