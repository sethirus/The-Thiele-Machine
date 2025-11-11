.PHONY: experiments-small experiments-falsify experiments-budget experiments-full artifacts
.PHONY: experiments-small-save experiments-falsify-save experiments-budget-save experiments-full-save
.PHONY: proofpack-smoke proofpack-turbulence-high
.PHONY: vm-run rtl-run compare clean purge verify-end-to-end

# Quick experiments (no outputs saved)
experiments-small:
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 12 14 --seed-grid 0 1 2 --repeat 1 --emit-receipts

experiments-budget:
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 12 --seed-grid 0 1 2 3 4 --repeat 1 --budget-sensitivity --emit-receipts

experiments-falsify:
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --mispartition --emit-receipts
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --shuffle-constraints --emit-receipts
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --noise 0.1 --emit-receipts
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --noise 0.3 --emit-receipts
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --noise 0.5 --emit-receipts

experiments-full:
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 12 14 16 18 --seed-grid 0 1 2 3 4 5 6 7 8 9 --repeat 3 --emit-receipts

# Save outputs versions (creates experiment directories)
experiments-small-save:
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 12 14 --seed-grid 0 1 2 --repeat 1 --emit-receipts --save-outputs --experiment-name small

experiments-budget-save:
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 12 --seed-grid 0 1 2 3 4 --repeat 1 --budget-sensitivity --emit-receipts --save-outputs --experiment-name budget

experiments-falsify-save:
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --mispartition --emit-receipts --save-outputs --experiment-name falsify_mispartition
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --shuffle-constraints --emit-receipts --save-outputs --experiment-name falsify_shuffle
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --noise 0.1 --emit-receipts --save-outputs --experiment-name falsify_noise01
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --noise 0.3 --emit-receipts --save-outputs --experiment-name falsify_noise03
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 --repeat 1 --noise 0.5 --emit-receipts --save-outputs --experiment-name falsify_noise05

experiments-full-save:
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 6 8 10 12 14 16 18 --seed-grid 0 1 2 3 4 5 6 7 8 9 --repeat 3 --emit-receipts --save-outputs --experiment-name full

artifacts:
	@echo "Creating artifacts package..."
	@mkdir -p artifacts/package
	@# Find latest experiment directories
	@SMALL_DIR=$$(find experiments -name "*_small" -type d | sort | tail -1); \
	BUDGET_DIR=$$(find experiments -name "*_budget" -type d | sort | tail -1); \
	FULL_DIR=$$(find experiments -name "*_full" -type d | sort | tail -1); \
	FALSIFY_DIRS=$$(find experiments -name "*_falsify_*" -type d | sort); \
	echo "Using small: $$SMALL_DIR"; \
	echo "Using budget: $$BUDGET_DIR"; \
	echo "Using full: $$FULL_DIR"; \
	echo "Using falsify: $$FALSIFY_DIRS"; \
	[ -n "$$SMALL_DIR" ] && cp $$SMALL_DIR/*.json $$SMALL_DIR/*.png $$SMALL_DIR/inference.md $$SMALL_DIR/results_table.csv $$SMALL_DIR/manifest.json artifacts/package/ 2>/dev/null || true; \
	[ -n "$$BUDGET_DIR" ] && cp $$BUDGET_DIR/*.json $$BUDGET_DIR/*.png $$BUDGET_DIR/inference.md $$BUDGET_DIR/results_table.csv $$BUDGET_DIR/manifest.json artifacts/package/ 2>/dev/null || true; \
	[ -n "$$FULL_DIR" ] && cp $$FULL_DIR/*.json $$FULL_DIR/*.png $$FULL_DIR/inference.md $$FULL_DIR/results_table.csv $$FULL_DIR/manifest.json artifacts/package/ 2>/dev/null || true; \
	for dir in $$FALSIFY_DIRS; do \
		cp $$dir/*.json $$dir/*.png $$dir/inference.md $$dir/results_table.csv $$dir/manifest.json artifacts/package/ 2>/dev/null || true; \
	done
	@cd artifacts/package && sha256sum * > ../artifacts_manifest.sha256 2>/dev/null || echo "No artifacts to package"
	@echo "Top-level SHA256: $$(sha256sum artifacts/package/* | sha256sum | cut -d' ' -f1)" | tee artifacts/package_top_hash.txt
	@echo "Artifacts packaged in artifacts/package/ with manifest artifacts/artifacts_manifest.sha256"

vm-run:
	mkdir -p outputs/
	python scripts/experiments/run_partition_experiments.py --problem tseitin --partitions 4 --repeat 1 --seed-grid 0 --emit-receipts --save-outputs --experiment-name vm_test
	@VM_DIR=$$(find experiments -name "*_vm_test" -type d | sort | tail -1); \
	RECEIPT=$$(find $$VM_DIR -name "receipt_n4_seed0_*.json" | head -1); \
	cp $$RECEIPT outputs/vm_receipt.json; \
	echo "VM receipt saved to outputs/vm_receipt.json"

rtl-run:
	mkdir -p outputs/
	cd thielecpu/hardware && python test_hardware.py
	cp thielecpu/hardware/simulation_output.log outputs/rtl_log.log
	@echo "RTL log saved to outputs/rtl_log.log"

compare: vm-run rtl-run
	python scripts/compare_vm_rtl.py outputs/vm_receipt.json outputs/rtl_log.log

clean:
	rm -rf outputs/

purge:
	find experiments -type d -mtime +1 -exec rm -rf {} +

verify-end-to-end:
	python3 tools/verify_end_to_end.py

# Zero-trust proofpack smoke profile (runs quick pipeline + bundler)
proofpack-smoke:
	@run_tag=$${RUN_TAG:-ci-smoke}; \
	echo "Running proofpack pipeline smoke with run tag '$$run_tag'"; \
	rm -rf artifacts/experiments/$$run_tag; \
	PYTHONPATH=. python scripts/run_proofpack_pipeline.py --profile quick --signing-key kernel_secret.key --run-tag $$run_tag --note CI-smoke --created-at 1970-01-01T00:00:00Z

# Scheduled high-budget turbulence pipeline run (mirrors JHTDB fixtures)
proofpack-turbulence-high:
	@run_tag=$${RUN_TAG:-ci-turbulence}; \
	  echo "Running high-budget turbulence pipeline with run tag '$$run_tag'"; \
	  rm -rf artifacts/experiments/$$run_tag; \
	  PYTHONPATH=. python scripts/run_proofpack_pipeline.py --profile quick --signing-key kernel_secret.key --run-tag $$run_tag --note CI-turbulence --public-data-root archive --turbulence-dataset isotropic1024_8pt --turbulence-dataset isotropic1024_12pt --turbulence-protocol sighted --turbulence-protocol blind --turbulence-protocol destroyed --turbulence-seed 11
