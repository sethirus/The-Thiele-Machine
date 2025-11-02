.PHONY: run verify clean

run:
	@echo "Running Dialogue of the One experiment..."
	python3 ../../run_final_dialogue.py --emit-receipt
	@echo "✓ Experiment complete"

verify:
	@echo "Verifying receipts..."
	python3 ../../verifier/replay.py receipts/
	@echo "✓ Verification complete"

clean:
	rm -rf results/*.json
	rm -rf receipts/*.json
