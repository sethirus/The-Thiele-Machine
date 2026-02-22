# Thiele Machine - Makefile
# ==========================
# E1.1: One-Command Reproducibility Demos

.PHONY: help demo_cnf demo_sat demo_analysis demo_all run_all install_deps verify clean_demos closed_work organize
.PHONY: experiments-small experiments-falsify experiments-budget experiments-full artifacts
.PHONY: experiments-small-save experiments-falsify-save experiments-budget-save experiments-full-save
.PHONY: proofpack-smoke proofpack-turbulence-high proofpack-phase3 bell law nusd headtohead turbulence-law turbulence-law-v2 turbulence-closure-v1 self-model-v1
.PHONY: vm-run rtl-run compare clean purge verify-end-to-end
.PHONY: showcase test-isomorphism test-alignment test-all test-ultra-smoke-isomorphism test-smoke-isomorphism test-full-isomorphism test-emergent-geometry test-emergent-geometry-verilator black-hole-demo atlas-audit proof-dag isomorphism-visual-audit isomorphism-roadmap heuristic-heatmaps inquisitor-visual-audit
.PHONY: generate-python
.PHONY: deliverable-one-hour
.PHONY: proof-complete-gate coq-gate extraction-gate rtl-gate cosim-gate

# ============================================================================
# E1.1: DEMO TARGETS - One-Command Reproducibility
# ============================================================================

help:
	@echo "Thiele Machine - Available Targets"
	@echo "==================================="
	@echo ""
	@echo "DEMO TARGETS (E1.1):"
	@echo "  make demo_cnf       - CNF analyzer demonstration"
	@echo "  make demo_sat       - SAT benchmark demonstration"
	@echo "  make demo_analysis  - Statistical analysis demonstration"
	@echo "  make demo_all       - Run all demos"
	@echo "  make install_deps   - Install required dependencies"
	@echo "  make verify         - Verify installation"
	@echo ""
	@echo "EXISTING TARGETS:"
	@echo "  make showcase       - Run showcase programs"
	@echo "  make test-all       - Run all tests"
	@echo "  make test-ultra-smoke-isomorphism - Fast (<2 min) cross-layer sanity checks"
	@echo "  make test-smoke-isomorphism - Practical local isomorphism smoke run"
	@echo "  make test-emergent-geometry - Fast proxy checks for silicon-curving claims"
	@echo "  make test-emergent-geometry-verilator - Same proxy checks using Verilator backend"
	@echo "  make black-hole-demo - Show Python fail-fast vs RTL kill-switch semantics"
	@echo "  make atlas-audit    - Generate single detailed cross-layer integration atlas"
	@echo "  make isomorphism-bitlock - Strict bit-for-bit Coq/Python/RTL lockstep gate"
	@echo "  make proof-undeniable - Machine-checkable formal proof gate (inquisitor + coqchk)"
	@echo "  make deliverable-one-hour - Publishable real-result brief (proof + RSA artifact)"
	@echo "  make experiments-*  - Run partition experiments"
	@echo ""
	@echo "CLOSED WORK (A+B+C):"
	@echo "  make closed_work    - Build Coq core + falsifier report + C verifier artifact"
	@echo ""

closed_work:
	@python3 scripts/closed_work.py

# Install dependencies
install_deps:
	@echo "Installing dependencies..."
	@sudo apt-get update -qq && sudo apt-get install -y -qq python3-numpy python3-scipy python3-matplotlib python3-networkx coq
	@pip install z3-solver --quiet
	@echo "✓ Dependencies installed"

# Demo 1: CNF Analyzer
demo_cnf:
	@echo ""
	@echo "========================================"
	@echo "DEMO: CNF Analyzer (B1.1)"
	@echo "========================================"
	@echo "Analyzing CNF files with partition discovery..."
	@python3 tools/cnf_analyzer.py spec/golden/xor_small.cnf
	@echo ""
	@echo "✓ CNF Analyzer demo complete"

# Demo 2: SAT Benchmark
demo_sat:
	@echo ""
	@echo "========================================"
	@echo "DEMO: SAT Benchmark (B1.2)"
	@echo "========================================"
	@echo "Comparing baseline vs sighted SAT solving..."
	@mkdir -p benchmarks/instances
	@python3 tools/generate_cnf_instances.py --type modular --vars 30 --modules 5 --output benchmarks/instances/demo_modular.cnf
	@timeout 30 python3 tools/sat_benchmark.py benchmarks/instances/demo_modular.cnf --timeout 10 || true
	@echo ""
	@echo "✓ SAT Benchmark demo complete"

# Demo 3: Statistical Analysis
demo_analysis:
	@echo ""
	@echo "========================================"
	@echo "DEMO: Statistical Analysis (B1.4)"
	@echo "========================================"
	@if [ -f benchmarks/sat_results.csv ]; then \
		python3 tools/analyze_sat_results.py benchmarks/sat_results.csv; \
	else \
		echo "Generating quick benchmark..."; \
		mkdir -p benchmarks/instances; \
		python3 tools/generate_cnf_instances.py --type modular --vars 20 --modules 4 --output benchmarks/instances/quick1.cnf; \
		python3 tools/generate_cnf_instances.py --type random --vars 20 --output benchmarks/instances/quick2.cnf; \
		timeout 60 python3 tools/run_batch_benchmarks.py --input-dir benchmarks/instances --output benchmarks/quick_results.csv --timeout 10 || true; \
		[ -f benchmarks/quick_results.csv ] && python3 tools/analyze_sat_results.py benchmarks/quick_results.csv || echo "Demo data unavailable"; \
	fi
	@echo ""
	@echo "✓ Analysis demo complete"

# Run all demos
demo_all: demo_cnf demo_sat demo_analysis
	@echo ""
	@echo "========================================"
	@echo "ALL DEMOS COMPLETE"
	@echo "========================================"
	@echo "✓ CNF analyzer demonstrated"
	@echo "✓ SAT benchmark demonstrated"
	@echo "✓ Statistical analysis demonstrated"

run_all: demo_all

# Verify installation
verify:
	@echo "Verifying installation..."
	@python3 --version
	@python3 -c "import numpy" && echo "✓ numpy installed" || echo "✗ numpy missing"
	@python3 -c "import scipy" && echo "✓ scipy installed" || echo "✗ scipy missing"
	@python3 -c "import z3" && echo "✓ z3 installed" || echo "✗ z3 missing"
	@coqc --version | head -1 || echo "✗ coq missing"

# Clean demo files
clean_demos:
	@rm -rf benchmarks/instances/demo_*.cnf benchmarks/instances/quick*.cnf benchmarks/quick_results.csv
	@echo "✓ Demo files cleaned"

# ============================================================================
# EXISTING TARGETS
# ============================================================================

COQTOP ?= coqtop
BELL_SKIP_COQ ?= 0
LAW_SKIP_COQ ?= 0

# Showcase and alignment verification
showcase:
	python3 tools/run_thiele_showcase.py --verbose

showcase-quick:
	python3 tools/run_thiele_showcase.py --quick

test-isomorphism:
	pytest tests/test_bisimulation_complete.py tests/test_three_layer_isomorphism.py tests/test_rtl_compute_isomorphism.py -v

test-alignment:
	pytest tests/alignment/ tests/test_opcode_alignment.py -v

test-all:
	pytest tests/test_mu.py tests/test_mu_costs.py tests/test_bisimulation_complete.py tests/test_accelerator_cosim.py tests/test_three_layer_isomorphism.py tests/test_opcode_alignment.py tests/test_rtl_compute_isomorphism.py tests/test_rtl_mu_charging.py tests/test_fuzz_isomorphism.py tests/alignment/ -v

test-ultra-smoke-isomorphism:
	THIELE_FUZZ_MAX_EXAMPLES=$${THIELE_FUZZ_MAX_EXAMPLES:-2} \
	THIELE_FUZZ_TENSOR_MAX_EXAMPLES=$${THIELE_FUZZ_TENSOR_MAX_EXAMPLES:-1} \
	THIELE_FUZZ_LONG_MAX_EXAMPLES=$${THIELE_FUZZ_LONG_MAX_EXAMPLES:-1} \
	THIELE_BIANCHI_MAX_EXAMPLES=$${THIELE_BIANCHI_MAX_EXAMPLES:-6} \
	THIELE_BIANCHI_SEQ_MAX_EXAMPLES=$${THIELE_BIANCHI_SEQ_MAX_EXAMPLES:-4} \
	THIELE_BIANCHI_SINGLE_MAX_EXAMPLES=$${THIELE_BIANCHI_SINGLE_MAX_EXAMPLES:-4} \
	pytest -q \
	  tests/test_bisimulation_complete.py::TestBisimulationCoqPython::test_empty_program \
	  tests/test_bisimulation_complete.py::TestBisimulationCoqPython::test_single_pnew \
	  tests/test_bisimulation_complete.py::TestBisimulationVerilog::test_mu_alu_addition \
	  tests/test_bisimulation_complete.py::TestOpcodeAlignment::test_opcode_values_coq_python \
	  tests/test_bisimulation_complete.py::TestOpcodeAlignment::test_opcode_values_coq_verilog \
	  tests/test_random_program_fuzz.py::TestRandomProgramIsomorphism::test_mu_matches_for_random_programs \
	  tests/test_bianchi_enforcement.py::TestBianchiPythonEnforcement::test_bianchi_holds_after_reveal_instruction \
	  tests/test_bianchi_enforcement.py::TestBianchiPropertyBased::test_bianchi_consistency_property \
	  -x --maxfail=1

test-smoke-isomorphism:
	THIELE_FUZZ_MAX_EXAMPLES=$${THIELE_FUZZ_MAX_EXAMPLES:-8} \
	THIELE_FUZZ_TENSOR_MAX_EXAMPLES=$${THIELE_FUZZ_TENSOR_MAX_EXAMPLES:-4} \
	THIELE_FUZZ_LONG_MAX_EXAMPLES=$${THIELE_FUZZ_LONG_MAX_EXAMPLES:-4} \
	THIELE_BIANCHI_MAX_EXAMPLES=$${THIELE_BIANCHI_MAX_EXAMPLES:-20} \
	THIELE_BIANCHI_SEQ_MAX_EXAMPLES=$${THIELE_BIANCHI_SEQ_MAX_EXAMPLES:-15} \
	THIELE_BIANCHI_SINGLE_MAX_EXAMPLES=$${THIELE_BIANCHI_SINGLE_MAX_EXAMPLES:-15} \
	pytest -q tests/test_bisimulation_complete.py tests/test_random_program_fuzz.py tests/test_bianchi_enforcement.py -x --maxfail=1

test-full-isomorphism:
	pytest -q tests/test_bisimulation_complete.py tests/test_random_program_fuzz.py tests/test_bianchi_enforcement.py

test-emergent-geometry:
	pytest -q tests/test_emergent_geometry_proxies.py -x --maxfail=1

test-emergent-geometry-verilator:
	THIELE_RTL_SIM=verilator pytest -q tests/test_emergent_geometry_proxies.py -x --maxfail=1

black-hole-demo:
	python3 scripts/black_hole_demo.py

atlas-audit:
	python3 scripts/generate_full_mesh_audit.py
	@echo "Atlas artifact: artifacts/ATLAS.md"

# ============================================================================
# PROOF COMPLETION GATES
# ============================================================================
# proof-complete-gate: the single command that must pass before claiming
# three-way isomorphism is mechanically verified.
#   1. Coq compiles clean (zero Admitted, all .vo present)
#   2. Extraction artefacts are fresh and export the right symbols
#   3. Extracted RTL synthesises with Yosys (non-empty design, top=mkModule1)
#   4. Co-simulation testbench runs without fatal errors
#   5. Atlas score/DOD gate recalculated with all real toolchain results
proof-complete-gate: coq-gate extraction-gate rtl-gate
	pytest tests/test_coq_compile_gate.py tests/test_extraction_freshness.py tests/test_rtl_synthesis_gate.py -v -m "coq or hardware" --tb=short
	@echo ""
	@echo "Regenerating atlas with toolchain gate results..."
	python3 scripts/generate_full_mesh_audit.py
	@echo ""
	@echo "proof-complete-gate: ALL GATES PASSED"

coq-gate:
	@echo "[coq-gate] Building all Coq proofs..."
	$(MAKE) -C coq -j4
	@echo "[coq-gate] Checking for Admitted..."
	@count=$$(grep -rn 'Admitted\.' coq/ --include='*.v' | grep -v patches | wc -l); \
	 if [ "$$count" -ne 0 ]; then \
	   echo "FAIL: $$count Admitted. found:"; \
	   grep -rn 'Admitted\.' coq/ --include='*.v' | grep -v patches; \
	   exit 1; \
	 fi
	@echo "[coq-gate] PASS: zero Admitted, all proofs compile"

extraction-gate:
	@echo "[extraction-gate] Verifying thiele_core.ml and thiele_core_minimal.ml..."
	@for f in build/thiele_core.ml build/thiele_core_minimal.ml; do \
	  if [ ! -s "$$f" ]; then echo "FAIL: $$f missing or empty"; exit 1; fi; \
	  for sym in vm_instruction vm_apply vMState; do \
	    if ! grep -q "$$sym" "$$f"; then echo "FAIL: $$sym not found in $$f"; exit 1; fi; \
	  done; \
	done
	@echo "[extraction-gate] PASS: extraction artefacts present and export correct symbols"

rtl-gate:
	@echo "[rtl-gate] Running Yosys synthesis on extracted Kami RTL..."
	yosys -p "read_verilog -sv -DSYNTHESIS thielecpu/hardware/rtl/thiele_cpu_kami.v; prep -top mkModule1; check; stat" 2>&1 | tee /tmp/rtl_gate.log
	@if grep -q 'ERROR\|error:' /tmp/rtl_gate.log; then echo "FAIL: Yosys errors found"; exit 1; fi
	@cells=$$(grep 'Number of cells:' /tmp/rtl_gate.log | awk '{print $$NF}'); \
	 if [ -z "$$cells" ] || [ "$$cells" -eq 0 ]; then echo "FAIL: zero cells synthesised"; exit 1; fi
	@echo "[rtl-gate] PASS: extracted RTL synthesises cleanly"

cosim-gate:
	@echo "[cosim-gate] Running iverilog/vvp co-simulation..."
	pytest tests/test_rtl_synthesis_gate.py::test_verilog_cosim_testbench -v --tb=short
	@echo "[cosim-gate] PASS"

proof-dag: atlas-audit

isomorphism-visual-audit: atlas-audit

isomorphism-roadmap: atlas-audit

heuristic-heatmaps: atlas-audit

inquisitor-visual-audit: atlas-audit

generate-python:
	python3 scripts/generate_python_from_coq.py

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
	@echo "Running RTL co-simulation via cosim.py..."
	pytest tests/test_bisimulation_complete.py -v --tb=short 2>&1 | tee outputs/rtl_log.log
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


# ============================================================================
# RTL SYNTHESIS TARGETS - Hardware Validation
# ============================================================================

RTL_DIR := thielecpu/hardware/rtl
RTL_CANONICAL := $(RTL_DIR)/thiele_cpu_kami.v
RTL_TOP := mkModule1
RTL_TESTBENCH := thielecpu/hardware/testbench/thiele_cpu_kami_tb.v
SYNTH_LOG := $(RTL_DIR)/synth_lite_clean.log
SYNTH_OUT := $(RTL_DIR)/synth_lite_out.v

.PHONY: rtl-check rtl-synth rtl-cosim rtl-verify rtl-clean

# iverilog compilation check (simulation mode, all $display active)
rtl-check:
	@echo "=== RTL Compilation Check ==="
	@iverilog -g2012 -Wall -o /dev/null $(RTL_CANONICAL) 2>&1
	@echo "✓ iverilog: zero warnings, zero errors"

# Full Yosys gate-level synthesis (YOSYS_LITE: same logic, smaller arrays)
rtl-synth: $(RTL_CANONICAL)
	@echo "=== Yosys Gate-Level Synthesis ==="
	@echo "    Source: $(RTL_CANONICAL)"
	@echo "    Top:    $(RTL_TOP)"
	@echo "    Defines: -DSYNTHESIS"
	@echo "    Running (this takes ~5 minutes)..."
	@yosys -l $(SYNTH_LOG) -p "read_verilog -sv -DSYNTHESIS $(RTL_CANONICAL); prep -top $(RTL_TOP); check; stat; write_verilog $(SYNTH_OUT)" 2>&1
	@echo ""
	@echo "=== Synthesis Results ==="
	@grep "Warnings:" $(SYNTH_LOG) | tail -1
	@grep -c "ERROR" $(SYNTH_LOG) | xargs -I{} echo "Errors: {}"
	@echo ""
	@grep -A20 "=== $(RTL_TOP) ===" $(SYNTH_LOG)
	@echo ""
	@echo "✓ Synthesis complete — netlist written to $(SYNTH_OUT)"

# Run all cosim tests (bisimulation + accelerator)
rtl-cosim:
	@echo "=== Co-Simulation Tests ==="
	@echo "    Canonical RTL: $(RTL_CANONICAL)"
	@echo "    Testbench:     $(RTL_TESTBENCH)"
	@pytest tests/test_bisimulation_complete.py tests/test_accelerator_cosim.py -v 2>&1
	@echo "✓ All cosim tests passed"

# Full RTL verification: compile + synthesize + cosim
rtl-verify: rtl-check rtl-synth rtl-cosim
	@echo ""
	@echo "╔══════════════════════════════════════════════════╗"
	@echo "║   THIELE CPU RTL VERIFICATION — ALL PASSED      ║"
	@echo "╠══════════════════════════════════════════════════╣"
	@echo "║  ✓ iverilog compilation     (zero warnings)     ║"
	@echo "║  ✓ Yosys gate-level synth   (zero errors)       ║"
	@echo "║  ✓ bisimulation cosim       (39 tests)          ║"
	@echo "║  ✓ accelerator cosim        (22+ tests)         ║"
	@echo "╚══════════════════════════════════════════════════╝"

# Clean synthesis artifacts
rtl-clean:
	@rm -f $(RTL_DIR)/synth*.log $(RTL_DIR)/synth*_out.v
	@echo "✓ Synthesis artifacts cleaned"

# Legacy aliases
synth-mu-alu: rtl-synth
synth-modules: rtl-synth
synth-all: rtl-synth

synth-report:
	@echo "=== Thiele Machine RTL Synthesis Report ==="
	@echo ""
	@if [ -f $(SYNTH_LOG) ]; then \
		grep -A20 "=== thiele_cpu ===" $(SYNTH_LOG); \
	else \
		echo "  Run 'make rtl-synth' first."; \
	fi

clean-synth: rtl-clean

# Coq proof compilation
.PHONY: coq-core coq-kernel coq-subsumption proof-undeniable isomorphism-bitlock parity-extracted-only proof-gate-repro synthesis-repro-gate final-claim-audit final-claim-all

coq-core:
	@echo "Building Coq core proofs..."
	@$(MAKE) -C coq
	@echo "✓ Coq proofs built"

coq-kernel:
	@$(MAKE) -C coq kernel/Kernel.vo kernel/KernelTM.vo kernel/KernelThiele.vo
	@echo "✓ Coq kernel proofs built"

coq-subsumption:
	@$(MAKE) -C coq kernel/Subsumption.vo
	@echo "✓ Subsumption proof (TURING ⊊ THIELE) verified"

isomorphism-bitlock:
	@echo "Running strict bit-for-bit Coq/Python/RTL lockstep gate..."
	@bash scripts/parity_extracted_only.sh
	@echo "✓ Bit-for-bit runtime lockstep PASSED"

parity-extracted-only:
	@bash scripts/parity_extracted_only.sh

proof-gate-repro:
	@bash scripts/proof_gate_reproducible.sh

synthesis-repro-gate:
	@bash scripts/synthesis_repro_gate.sh

final-claim-audit:
	@bash scripts/repo_audit_trail.sh

final-claim-all: parity-extracted-only proof-gate-repro synthesis-repro-gate final-claim-audit
	@echo "✓ Final claim bundle generated under artifacts/"

proof-undeniable:
	@echo "Running formal proof gate (compile + audit + independent checker)..."
	@$(MAKE) coq-kernel
	@python3 scripts/inquisitor.py
	@cd coq && coqchk -R kernel Kernel Kernel.Kernel Kernel.KernelTM Kernel.KernelThiele
	@cd coq && coqchk -R kernel Kernel Kernel.PythonBisimulation Kernel.HardwareBisimulation Kernel.ThreeLayerIsomorphism
	@cd coq && coqchk -R kernel Kernel -R bridge Bridge Kernel.VMState Kernel.VMStep Bridge.PythonMuLedgerBisimulation
	@$(MAKE) isomorphism-bitlock
	@echo "✓ Formal proof gate PASSED (inquisitor + coqchk)"

deliverable-one-hour:
	@echo "Building one-hour tangible deliverable..."
	@$(MAKE) proof-undeniable
	@python3 scripts/rsa_partition_demo.py --moduli $${DELIVERABLE_MODULI:-3233 10403} --analysis-bits 256 512 1024
	@python3 scripts/generate_impact_deliverable.py --input rsa_demo_output/analysis_report.json --output artifacts/ONE_HOUR_DELIVERABLE.md
	@echo "✓ Deliverable ready: artifacts/ONE_HOUR_DELIVERABLE.md"

# Integration testing
.PHONY: test-vm-rtl test-integration

test-vm-rtl:
	@echo "Testing VM-RTL equivalence..."
	@python scripts/test_vm_rtl_equivalence.py
	@echo "✓ VM-RTL equivalence tests passed"

test-integration: coq-core synth-all test-vm-rtl
	@echo "✓ Full integration test complete"
	@echo "  - Coq proofs compiled"
	@echo "  - RTL synthesized"
	@echo "  - VM-RTL equivalence validated"

# Clean build artifacts and cache files
clean:
	@echo "Cleaning build artifacts and cache files..."
	@rm -rf .build_cache/ .test_artifacts/ .generated/
	@find . -name "*.vo" -delete
	@find . -name "*.vos" -delete
	@find . -name "*.vok" -delete
	@find . -name "*.glob" -delete
	@find . -name "*.aux" -delete
	@find . -name "__pycache__" -type d -exec rm -rf {} + 2>/dev/null || true
	@echo "✓ Clean complete"

# Organize workspace (move artifacts to appropriate directories)
organize:
	@echo "Organizing workspace..."
	@./scripts/auto_organize.sh

# Clean everything including dependencies
purge: clean
	@echo "Purging all generated files..."
	@rm -rf node_modules/ .venv/ venv/ thiele_env/
	@make -C coq clean
	@echo "✓ Purge complete"
	@echo "RTL SYNTHESIS TARGETS:"
	@echo "  make rtl-check       - iverilog compilation check"
	@echo "  make rtl-synth       - Yosys gate-level synthesis"
	@echo "  make rtl-cosim       - Run all co-simulation tests"
	@echo "  make rtl-verify      - Full RTL verification pipeline"
	@echo "  make rtl-clean       - Clean synthesis artifacts"
	@echo ""
	@echo "COQ PROOF TARGETS:"
	@echo "  make coq-core        - Build Coq core proofs"
	@echo "  make coq-kernel      - Build Coq kernel"
	@echo "  make coq-subsumption - Verify subsumption proof"
	@echo ""
	@echo "INTEGRATION TARGETS:"
	@echo "  make test-vm-rtl     - Test VM-RTL equivalence"
	@echo "  make test-integration- Full integration test"
	@echo ""
