.PHONY: experiments-small experiments-falsify experiments-budget experiments-full artifacts
.PHONY: experiments-small-save experiments-falsify-save experiments-budget-save experiments-full-save
.PHONY: proofpack-smoke proofpack-turbulence-high proofpack-phase3 bell law nusd headtohead turbulence-law turbulence-law-v2 turbulence-closure-v1 self-model-v1
.PHONY: vm-run rtl-run compare clean purge verify-end-to-end
.PHONY: showcase test-isomorphism test-alignment test-all

COQTOP ?= coqtop
BELL_SKIP_COQ ?= 0
LAW_SKIP_COQ ?= 0

# Showcase and alignment verification
showcase:
	python3 tools/run_thiele_showcase.py --verbose

showcase-quick:
	python3 tools/run_thiele_showcase.py --quick

test-isomorphism:
	pytest tests/test_isomorphism_complete.py -v

test-alignment:
	pytest tests/alignment/ -v

test-showcase:
	pytest tests/test_showcase_programs.py -v

test-all:
	pytest tests/test_vm.py tests/test_mu.py tests/test_showcase_programs.py tests/test_isomorphism_complete.py tests/alignment/ tests/test_opcode_alignment.py tests/test_hardware_alignment.py -v

coq/%.vo:
	$(MAKE) -C coq $(patsubst coq/%,%,$@)

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

bell: coq/thielemachine/coqproofs/BellCheck.vo
	python3 tools/make_bell_receipt.py --N 20000 --epsilon 0.01 --seed 1337
	python3 tools/verify_bell_receipt.py artifacts/bell_receipt.jsonl $(if $(filter 1,$(BELL_SKIP_COQ)),--skip-coq,) --coqtop $(COQTOP)
	python3 tools/verify_end_to_end.py --skip-hardware --skip-yosys

law: coq/thielemachine/coqproofs/LawCheck.vo
	python3 tools/make_law_receipt.py --sites 8 --steps 16 --seed 2025
	python3 tools/verify_law_receipt.py artifacts/law_receipt.jsonl $(if $(filter 1,$(LAW_SKIP_COQ)),--skip-coq,) --coq-binary $(COQTOP)

nusd:
	python3 tools/make_nusd_receipt.py --domain lattice --output artifacts/nusd_lattice.jsonl
	python3 tools/verify_nusd_receipt.py artifacts/nusd_lattice.jsonl
	python3 tools/make_nusd_receipt.py --domain tseitin --output artifacts/nusd_tseitin.jsonl
	python3 tools/verify_nusd_receipt.py artifacts/nusd_tseitin.jsonl
	python3 tools/make_nusd_receipt.py --domain automaton --output artifacts/nusd_automaton.jsonl
	python3 tools/verify_nusd_receipt.py artifacts/nusd_automaton.jsonl
	python3 tools/make_nusd_receipt.py --domain turbulence --output artifacts/nusd_turbulence.jsonl
	python3 tools/verify_nusd_receipt.py artifacts/nusd_turbulence.jsonl

headtohead:
	python3 tools/make_turbulence_head_to_head.py
	python3 tools/verify_turbulence_head_to_head.py artifacts/turbulence_head_to_head.jsonl

turbulence-law:
	python3 tools/make_turbulence_law_receipt.py --eval-dataset public_data/jhtdb/sample/jhtdb_samples.json
	python3 tools/verify_turbulence_law_receipt.py artifacts/turbulence_law_receipt.jsonl

turbulence-law-v2:
	python3 tools/discover_turbulence_law_v2.py --json-out artifacts/turbulence_law_v2_summary.json
	python3 tools/make_turbulence_law_v2_receipt.py --eval-dataset public_data/jhtdb/sample/jhtdb_samples.json
	python3 tools/verify_turbulence_law_v2_receipt.py artifacts/turbulence_law_v2_receipt.jsonl

turbulence-closure-v1:
	python3 tools/discover_turbulence_closure_v1.py --json-out artifacts/turbulence_closure_v1_summary.json
	python3 tools/make_turbulence_closure_v1_receipt.py
	python3 tools/verify_turbulence_closure_v1_receipt.py artifacts/turbulence_closure_v1_receipt.jsonl

self-model-v1:
	python3 tools/make_self_traces.py
	python3 tools/discover_self_model_v1.py --output artifacts/self_model_v1_summary.json
	python3 tools/make_self_model_v1_receipt.py
	python3 tools/verify_self_model_v1_receipt.py artifacts/self_model_v1_receipt.jsonl

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

proofpack-phase3: coq/thielemachine/coqproofs/PhaseThree.vo
	$(MAKE) bell
	$(MAKE) law
	$(MAKE) nusd
	$(MAKE) headtohead
	python3 tools/make_phase_three_proofpack.py
	python3 tools/verify_phase_three_proofpack.py artifacts/phase_three/phase_three_proofpack.tar.gz --coqc coqc
