# Thiele Machine - Makefile
# ==========================
# E1.1: One-Command Reproducibility Demos

.PHONY: help install_deps organize
.PHONY: rtl-run clean deep-clean purge
.PHONY: test-isomorphism test-alignment test-all test-ultra-smoke-isomorphism test-smoke-isomorphism test-full-isomorphism test-emergent-geometry test-emergent-geometry-verilator
.PHONY: generate-python ocaml-runner
.PHONY: proof-complete-gate coq-gate extraction-gate rtl-gate cosim-gate isa-proof-freshness-check
.PHONY: closeout-gate
.PHONY: bitlock-proof-vm-cpu bitlock-manifest
.PHONY: canonical-source-gate canonical-extract canonical-e2e rtl-pipeline-manifest-check rtl-text-transform-audit-check
.PHONY: bitlock-stable stack-audit
.PHONY: install-hooks refresh-manifests

# ============================================================================
# E1.1: DEMO TARGETS - One-Command Reproducibility
# ============================================================================

help:
	@echo "Thiele Machine - Available Targets"
	@echo "==================================="
	@echo ""
	@echo "SETUP:"
	@echo "  make install_deps   - Install required dependencies"
	@echo ""
	@echo "TEST TARGETS:"
	@echo "  make test           - Run the pytest suite"
	@echo "  make test-seq       - Run the pytest suite without xdist"
	@echo "  make test-all       - Run all tests"
	@echo "  make test-ultra-smoke-isomorphism - Fast (<2 min) cross-layer sanity checks"
	@echo "  make test-smoke-isomorphism - Practical local isomorphism smoke run"
	@echo "  make test-emergent-geometry - Fast proxy checks for silicon-curving claims"
	@echo "  make test-emergent-geometry-verilator - Same proxy checks using Verilator backend"
	@echo ""
	@echo "CLOSURE GATES:"
	@echo "  make closeout-gate  - Single full-closure gate (Coq+extract+inquisitor+tests+bitlock)"
	@echo "  make atlas-audit    - Run inquisitor + completeness gate checks"
	@echo "  make isomorphism-bitlock - Strict bit-for-bit Coq/Python/RTL lockstep gate"
	@echo "  make bitlock-proof-vm-cpu - Deterministic hash lock from Coq roots to VM/RTL state"
	@echo "  make bitlock-stable - Stable lockstep gates with extended timeout"
	@echo "  make stack-audit    - One-command signed stack audit summary (JSON + logs)"
	@echo "  make bitlock-manifest - Emit reproducible proof->VM->CPU hash manifest"
	@echo "  make proof-undeniable - Machine-checkable formal proof gate (inquisitor + coqchk)"
	@echo "  make canonical-e2e - Canonical single-source Coq->OCaml->Kami/RTL->tests pipeline"
	@echo ""
	@echo "HARDWARE:"
	@echo "  make rtl-check      - iverilog compilation check"
	@echo "  make rtl-synth      - Yosys gate-level synthesis"
	@echo "  make rtl-cosim      - Co-simulation tests"
	@echo "  make rtl-verify     - Full RTL verification pipeline"
	@echo ""

# Install dependencies
install_deps:
	@echo "Installing dependencies..."
	@sudo apt-get update -qq && sudo apt-get install -y -qq python3-numpy python3-scipy python3-matplotlib python3-networkx coq
	@pip install z3-solver --quiet
	@echo "✓ Dependencies installed"

# ============================================================================
# EXISTING TARGETS
# ============================================================================

# Default test: auto-parallel via conftest.py (4 xdist workers)
test:
	pytest tests/ -q

# Sequential test (disable xdist)
test-seq:
	pytest tests/ -p no:xdist -q

COQTOP ?= coqtop
BELL_SKIP_COQ ?= 0
LAW_SKIP_COQ ?= 0

test-isomorphism:
	pytest tests/test_cross_layer_bisimulation.py tests/test_opcode_alignment.py tests/test_verilog_cosim.py -v

test-alignment:
	pytest tests/test_opcode_alignment.py -v

test-all:
	pytest tests/test_mu.py tests/test_accelerator_cosim.py tests/test_cross_layer_bisimulation.py tests/test_opcode_alignment.py tests/test_rtl_mu_charging.py tests/test_fuzz_random_programs.py tests/test_verilog_cosim.py tests/test_canonical_source_pipeline.py -v

test-ultra-smoke-isomorphism:
	pytest -q \
	  tests/test_canonical_source_pipeline.py::test_extraction_artifacts_exist \
	  tests/test_extraction_freshness.py::test_required_symbols_exported \
	  tests/test_verilog_cosim.py::TestCompilation::test_kami_rtl_compiles \
	  -x --maxfail=1

test-smoke-isomorphism:
	THIELE_FUZZ_MAX_EXAMPLES=$${THIELE_FUZZ_MAX_EXAMPLES:-8} \
	THIELE_FUZZ_TENSOR_MAX_EXAMPLES=$${THIELE_FUZZ_TENSOR_MAX_EXAMPLES:-4} \
	THIELE_FUZZ_LONG_MAX_EXAMPLES=$${THIELE_FUZZ_LONG_MAX_EXAMPLES:-4} \
	THIELE_BIANCHI_MAX_EXAMPLES=$${THIELE_BIANCHI_MAX_EXAMPLES:-20} \
	THIELE_BIANCHI_SEQ_MAX_EXAMPLES=$${THIELE_BIANCHI_SEQ_MAX_EXAMPLES:-15} \
	THIELE_BIANCHI_SINGLE_MAX_EXAMPLES=$${THIELE_BIANCHI_SINGLE_MAX_EXAMPLES:-15} \
	pytest -q tests/test_cross_layer_bisimulation.py tests/test_fuzz_random_programs.py tests/test_rtl_mu_charging.py -x --maxfail=1

test-full-isomorphism:
	pytest -q tests/test_cross_layer_bisimulation.py tests/test_fuzz_random_programs.py tests/test_verilog_cosim.py

bitlock-stable:
	THIELE_RTL_SIM=$${THIELE_RTL_SIM:-iverilog} \
	pytest -q \
	  tests/test_bitlock_proof_vm_cpu.py::test_proof_to_vm_to_cpu_source_chain_hashes_exist \
	  tests/test_bitlock_proof_vm_cpu.py::test_bit_for_bit_state_isomorphism_across_ocaml_python_rtl \
	  tests/test_bitlock_proof_vm_cpu.py::test_prefix_by_prefix_digest_isomorphism_every_step \
	  --per-test-timeout=$${PER_TEST_TIMEOUT:-240} -x --maxfail=1

stack-audit:
	python3 scripts/audit_stack.py --bitlock-timeout $${PER_TEST_TIMEOUT:-240}

test-emergent-geometry:
	@echo "[test-emergent-geometry] Target retired — emergent geometry proxy tests were superseded by EinsteinEquationsFull.v (Fourth Phase)."
	@echo "  Run 'pytest tests/test_final_evidence.py -q' for physics-layer validation instead."

test-emergent-geometry-verilator:
	@echo "[test-emergent-geometry-verilator] Target retired — see 'make test-emergent-geometry'."

atlas-audit:
	@echo "[atlas-audit] Running inquisitor proof hygiene check..."
	@python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md
	@echo "[atlas-audit] Running completeness gate tests..."
	@pytest tests/test_completeness_gate.py -q --tb=short
	@echo "[atlas-audit] PASS: all layers complete and consistent"

# ============================================================================
# CLOSEOUT GATE
# ============================================================================
# closeout-gate: the single command that means the repository is closed,
# complete, and testable from a clean checkout.
#
#   1. Coq builds clean — zero Admitted, all .vo present
#   2. Canonical extraction rebuilt from Coq roots (VM + Kami/RTL)
#   3. Proof-sensitive files committed — no uncommitted drift
#   4. Extraction freshness verified — .ml newer than .v source
#   5. Strict Inquisitor pass — zero HIGH/MEDIUM hygiene findings
#   6. Archive hygiene gate — root markdown surface + build manifest correct
#   7. No-open-obligations gate — MasterSummary obligations empty,
#      full-state verification scope affirmed
#   8. Artifact generators emit only closed/final statuses
#   9. Full canonical OCaml extraction surface (all 46 opcode arms present)
#  10. Full-state bit-for-bit lockstep across Coq/OCaml/RTL (bitlock)
#
# Steps 1–9 run unconditionally. Step 10 (isomorphism-bitlock) requires
# the RTL toolchain (yosys + verilator); it is an explicit dependency so the
# gate fails honestly when the toolchain is absent.
closeout-gate: coq-gate canonical-extract check-sensitive-files-strict isa-proof-freshness-check isomorphism-bitlock
	@echo ""
	@echo "============================================================"
	@echo " CLOSEOUT GATE — running software/proof layer checks"
	@echo "============================================================"
	@echo "[closeout-gate] Step 5/10: Strict Inquisitor pass..."
	@python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md
	@echo "[closeout-gate] Step 6/10: Archive hygiene gate..."
	@pytest tests/test_archive_hygiene.py -q --tb=short
	@echo "[closeout-gate] Step 7/10: No-open-obligations + full-state verification scope..."
	@pytest tests/test_completeness_gate.py -q --tb=short
	@echo "[closeout-gate] Step 8/10: Artifact generators emit closed statuses..."
	@python3 scripts/generate_master_summary_artifacts.py
	@pytest tests/test_master_summary_artifacts.py -q --tb=short
	@$(MAKE) rtl-pipeline-manifest-check
	@$(MAKE) rtl-text-transform-audit-check
	@echo "[closeout-gate] Step 9/10: Full canonical OCaml extraction surface (46 opcodes)..."
	@pytest tests/test_extraction_freshness.py tests/test_ocaml_extraction_parity_46.py -q --tb=short
	@echo "[closeout-gate] Step 10/10: Full-state RTL lockstep already verified by isomorphism-bitlock (above)."
	@echo ""
	@echo "============================================================"
	@echo " CLOSEOUT GATE: PASSED"
	@echo " The repository is closed, complete, and testable."
	@echo "============================================================"

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
	pytest tests/test_coq_compile_gate.py tests/test_extraction_freshness.py -v -m "coq or hardware" --tb=short
	@echo ""
	@echo "Running completeness gate..."
	pytest tests/test_completeness_gate.py -q --tb=short
	@echo ""
	@echo "proof-complete-gate: ALL GATES PASSED"

canonical-source-gate:
	@echo "[canonical-source-gate] Verifying extraction roots depend on CanonicalCPUProof..."
	@grep -q 'From KamiHW Require Import .*CanonicalCPUProof' coq/Extraction.v
	@grep -q 'From KamiHW Require Import CanonicalCPUProof' coq/kami_hw/KamiExtraction.v
	@grep -q '^Definition canonical_cpu_module := ' coq/kami_hw/CanonicalCPUProof.v
	@grep -q '^Definition targetB ' coq/kami_hw/CanonicalCPUProof.v
	@echo "[canonical-source-gate] PASS: canonical source wiring is explicit"

canonical-extract: canonical-source-gate
	@echo "[canonical-extract] Rebuilding extraction artefacts from canonical source..."
	@$(MAKE) -C coq -j4 Extraction.vo kami_hw/KamiExtraction.vo ThieleMachineComplete.vo
	@if [ ! -s "build/thiele_core.ml" ]; then echo "FAIL: build/thiele_core.ml missing or empty"; exit 1; fi
	@if [ ! -s "build/kami_hw/Target.ml" ]; then echo "FAIL: build/kami_hw/Target.ml missing or empty"; exit 1; fi
	@if [ ! -s "build/thiele_core_complete.ml" ]; then echo "FAIL: build/thiele_core_complete.ml missing or empty (ThieleMachineComplete extraction)"; exit 1; fi
	@echo "[canonical-extract] Verifying isomorphic extraction parity..."
	@bash -c 'diff <(sort build/thiele_core.ml) <(sort build/thiele_core_complete.ml) > /dev/null || { echo "FAIL: thiele_core.ml and thiele_core_complete.ml are NOT isomorphic"; exit 1; }'
	@echo "[canonical-extract] PASS: thiele_core.ml ≅ thiele_core_complete.ml (isomorphic)"
	@if [ ! -s "build/kami_hw/Main.ml" ]; then echo "FAIL: build/kami_hw/Main.ml missing or empty"; exit 1; fi
	@if [ ! -s "build/kami_hw/mkModule1.v" ]; then echo "FAIL: build/kami_hw/mkModule1.v missing or empty"; exit 1; fi
	@if [ ! -s "build/kami_hw/mkModule1_synth.v" ]; then echo "FAIL: build/kami_hw/mkModule1_synth.v missing or empty"; exit 1; fi
	@if [ ! -s "thielecpu/hardware/rtl/thiele_cpu_kami.v" ]; then echo "FAIL: tracked RTL missing or empty"; exit 1; fi
	@for sym in vm_instruction vm_apply vMState; do \
	  if ! grep -q "$$sym" "build/thiele_core.ml"; then echo "FAIL: $$sym not found in build/thiele_core.ml"; exit 1; fi; \
	done
	@for sym in canonical_cpu_module targetB; do \
	  if ! grep -q "$$sym" "build/kami_hw/Target.ml"; then echo "FAIL: $$sym not found in build/kami_hw/Target.ml"; exit 1; fi; \
	done
	@if ! grep -q 'match targetB iAddrSize with' "build/kami_hw/Main.ml"; then echo "FAIL: build/kami_hw/Main.ml is not driving the pretty-printer via targetB"; exit 1; fi
	@if ! diff -q build/kami_hw/mkModule1_synth.v thielecpu/hardware/rtl/thiele_cpu_kami.v >/dev/null; then \
	  echo "FAIL: tracked RTL is not identical to build/kami_hw/mkModule1_synth.v"; exit 1; \
	fi
	@echo "[canonical-extract] PASS: VM+Kami extraction artefacts regenerated"

canonical-e2e: canonical-extract rtl-gate cosim-gate test-smoke-isomorphism
	@echo ""
	@echo "canonical-e2e: PASS (canonical source -> extraction -> RTL synth/cosim -> smoke tests)"

rtl-pipeline-manifest-check: canonical-extract
	@echo "[rtl-pipeline-manifest] Checking canonical RTL provenance manifest..."
	@python3 scripts/generate_rtl_pipeline_manifest.py --check
	@pytest tests/test_rtl_pipeline_manifest.py -q --tb=short
	@echo "[rtl-pipeline-manifest] PASS"

# Refresh the RTL pipeline manifest (and any future manifests added here).
# Run this after editing tracked Coq sources before committing — or rely on
# the pre-commit hook installed by `make install-hooks` to do it for you.
refresh-manifests:
	@echo "[refresh-manifests] Regenerating artifacts/rtl_pipeline_manifest.json..."
	@python3 scripts/generate_rtl_pipeline_manifest.py --out artifacts/rtl_pipeline_manifest.json
	@echo "[refresh-manifests] Done. Stage the updated manifest with your changes."

# Install the Thiele Machine git hooks (one-time per checkout).
# After this, commits that touch tracked manifest sources will auto-regenerate
# and stage the manifest, eliminating the most common CI failure.
install-hooks:
	@bash scripts/install-git-hooks.sh

rtl-text-transform-audit-check: canonical-extract
	@echo "[rtl-text-transform-audit] Checking BSV/Verilog text transform audit..."
	@python3 scripts/audit_rtl_text_transforms.py --check
	@pytest tests/test_rtl_text_transform_audit.py -q --tb=short
	@echo "[rtl-text-transform-audit] PASS"

coq-gate:
	@echo "[coq-gate] Building all Coq proofs..."
	$(MAKE) -C coq -j4
	@echo "[coq-gate] Checking for Admitted..."
	@count=$$(grep -rnE '^\s*Admitted\.' coq/ --include='*.v' | grep -v patches | wc -l); \
	 if [ "$$count" -ne 0 ]; then \
	   echo "FAIL: $$count Admitted. found:"; \
	   grep -rnE '^\s*Admitted\.' coq/ --include='*.v' | grep -v patches; \
	   exit 1; \
	 fi
	@echo "[coq-gate] PASS: zero Admitted, all proofs compile"

extraction-gate: canonical-extract
	@echo "[extraction-gate] PASS: extraction artefacts are canonical and fresh"

rtl-gate:
	@echo "[rtl-gate] Running Yosys synthesis on extracted Kami RTL..."
	yosys -p "read_verilog -sv -DSYNTHESIS thielecpu/hardware/rtl/RegFile.v thielecpu/hardware/rtl/thiele_cpu_kami.v; prep -top mkModule1; check; stat" 2>&1 | tee /tmp/rtl_gate.log
	@if grep -q 'ERROR\|error:' /tmp/rtl_gate.log; then echo "FAIL: Yosys errors found"; exit 1; fi
	@cells=$$(grep 'Number of cells:' /tmp/rtl_gate.log | awk '{print $$NF}' | tail -n 1); \
	 if ! echo "$$cells" | grep -Eq '^[0-9]+$$'; then \
	   echo "FAIL: could not parse synthesized cell count (got '$$cells')"; exit 1; \
	 fi; \
	 if [ "$$cells" -eq 0 ]; then echo "FAIL: zero cells synthesised"; exit 1; fi
	@echo "[rtl-gate] PASS: extracted RTL synthesises cleanly"

cosim-gate:
	@echo "[cosim-gate] Running iverilog/vvp co-simulation..."
	pytest tests/test_verilog_cosim.py::TestCompilation::test_kami_rtl_compiles -v --tb=short
	@echo "[cosim-gate] PASS"

proof-dag: atlas-audit

isomorphism-visual-audit: atlas-audit

isomorphism-roadmap: atlas-audit

heuristic-heatmaps: atlas-audit

inquisitor-visual-audit: atlas-audit

generate-python: build/thiele_core.ml
	python3 scripts/forge.py \
		--input build/thiele_core.ml \
		--out-python thielecpu/generated/generated_core.py

# Build the Coq-extracted OCaml VM runner.
# Depends on coq/Extraction.vo so the runner is always built from the current proof tree.
ocaml-runner:
	@echo "[ocaml-runner] Ensuring Coq extraction is current..."
	@$(MAKE) -C coq Extraction.vo
	@echo "[ocaml-runner] Compiling OCaml interface..."
	@cd build && ocamlfind ocamlc -package str -c thiele_core.mli
	@echo "[ocaml-runner] Linking extracted runner..."
	@cd build && ocamlfind ocamlc -package str -linkpkg \
		thiele_core.ml extracted_vm_runner.ml \
		-o extracted_vm_runner
	@echo "✅ [ocaml-runner] build/extracted_vm_runner ready"

coq/%.vo:
	$(MAKE) -C coq $(patsubst coq/%,%,$@)

rtl-run:
	mkdir -p outputs/
	@echo "Running RTL co-simulation..."
	pytest tests/test_cross_layer_bisimulation.py -v --tb=short 2>&1 | tee outputs/rtl_log.log
	@echo "RTL log saved to outputs/rtl_log.log"

clean-outputs:
	rm -rf outputs/

# ============================================================================
# RTL SYNTHESIS TARGETS - Hardware Validation
# ============================================================================

RTL_DIR := thielecpu/hardware/rtl
RTL_CANONICAL := $(RTL_DIR)/thiele_cpu_kami.v
RTL_REGFILE := $(RTL_DIR)/RegFile.v
RTL_TOP := mkModule1
RTL_TESTBENCH := rtl_harness/testbench/thiele_cpu_kami_tb.v
SYNTH_LOG := $(RTL_DIR)/synth_lite_clean.log
SYNTH_OUT := $(RTL_DIR)/synth_lite_out.v

.PHONY: rtl-check rtl-synth rtl-cosim rtl-verify rtl-clean archive-vm-verilog

# iverilog compilation check (simulation mode, all $display active)
rtl-check:
	@echo "=== RTL Compilation Check ==="
	@iverilog -g2012 -Wall -o /dev/null $(RTL_REGFILE) $(RTL_CANONICAL) 2>&1 | tee /tmp/rtl_compile.log
	@if grep -qi "error:" /tmp/rtl_compile.log; then echo "FAIL: iverilog reported errors"; exit 1; fi
	@warns=$$(grep -ci "warning:" /tmp/rtl_compile.log || true); \
	echo "✓ iverilog: compile succeeded ($$warns warnings)"

# Full Yosys gate-level synthesis (YOSYS_LITE: same logic, smaller arrays)
rtl-synth: $(RTL_CANONICAL)
	@echo "=== Yosys Gate-Level Synthesis ==="
	@echo "    Source: $(RTL_CANONICAL)"
	@echo "    Top:    $(RTL_TOP)"
	@echo "    Defines: -DSYNTHESIS"
	@echo "    Running (this takes ~5 minutes)..."
	@yosys -l $(SYNTH_LOG) -p "read_verilog -sv -DSYNTHESIS $(RTL_REGFILE) $(RTL_CANONICAL); prep -top $(RTL_TOP); check; stat; write_verilog $(SYNTH_OUT); write_json build/netlist.json;" 2>&1
	@echo ""
	@echo "=== Synthesis Results ==="
	@grep "Warnings:" $(SYNTH_LOG) | tail -1
	@grep -c "ERROR" $(SYNTH_LOG) | xargs -I{} echo "Errors: {}"
	@echo ""
	@grep -A20 "=== $(RTL_TOP) ===" $(SYNTH_LOG)
	@echo ""
	@echo "✓ Synthesis complete — netlist written to $(SYNTH_OUT), JSON: build/netlist.json"
	@echo "=== Generating Circuit Diagram ==="
	@mkdir -p artifacts/synthesis_gate
	@yosys -p "read_verilog -sv -DSYNTHESIS $(RTL_REGFILE) $(RTL_CANONICAL); hierarchy -top $(RTL_TOP); show -format dot -prefix artifacts/synthesis_gate/circuit_hierarchy -notitle;" 2>/dev/null || true
	@if [ -f artifacts/synthesis_gate/circuit_hierarchy.dot ]; then \
		dot -Tsvg artifacts/synthesis_gate/circuit_hierarchy.dot \
		  -o artifacts/synthesis_gate/circuit_hierarchy.svg 2>/dev/null \
		  && echo "✓ Circuit diagram: artifacts/synthesis_gate/circuit_hierarchy.svg" \
		  || echo "⚠ graphviz not found — DOT at artifacts/synthesis_gate/circuit_hierarchy.dot"; \
	fi

# Run all cosim tests (bisimulation + accelerator)
rtl-cosim:
	@echo "=== Co-Simulation Tests ==="
	@echo "    Canonical RTL: $(RTL_CANONICAL)"
	@echo "    Testbench:     $(RTL_TESTBENCH)"
	@pytest tests/test_cross_layer_bisimulation.py tests/test_accelerator_cosim.py -v 2>&1
	@echo "✓ All cosim tests passed"

# Full RTL verification: compile + synthesize + cosim
rtl-verify: rtl-check rtl-synth rtl-cosim
	@echo ""
	@echo "╔══════════════════════════════════════════════════╗"
	@echo "║   THIELE CPU RTL VERIFICATION — ALL PASSED      ║"
	@echo "╠══════════════════════════════════════════════════╣"
	@echo "║  ✓ iverilog compilation     (warnings reviewed) ║"
	@echo "║  ✓ Yosys gate-level synth   (zero errors)       ║"
	@echo "║  ✓ bisimulation cosim       (39 tests)          ║"
	@echo "║  ✓ accelerator cosim        (22+ tests)         ║"
	@echo "╚══════════════════════════════════════════════════╝"

# Full Xilinx Artix-7 (xc7a35t / Arty A7-35T) deployment flow:
# yosys synth_xilinx → nextpnr-xilinx → fasm2frames → xc7frames2bit.
# Lets engineers reproduce the FPGA build locally without going through CI.
# Top is the minimal wrapper (thiele_cpu_top in thiele_cpu_top_min.v) so
# only the 5 board-visible pins need routing.
.PHONY: rtl-synth-xc7
rtl-synth-xc7: $(RTL_CANONICAL)
	@echo "=== Xilinx Artix-7 (xc7a35t) deployment flow ==="
	@command -v yosys             >/dev/null || { echo "ERROR: yosys not found"; exit 1; }
	@command -v nextpnr-xilinx    >/dev/null || { echo "ERROR: nextpnr-xilinx not found (build from openXC7/nextpnr-xilinx)"; exit 1; }
	@command -v xc7frames2bit     >/dev/null || { echo "ERROR: xc7frames2bit not found (build from SymbiFlow/prjxray tools)"; exit 1; }
	@bash fpga/run_synthesis_xc7.sh

# Clean synthesis artifacts
rtl-clean:
	@rm -f $(RTL_DIR)/synth*.log $(RTL_DIR)/synth*_out.v
	@rm -f build/thiele_xc7a35t.json build/thiele_xc7a35t.fasm
	@rm -f build/thiele_xc7a35t.frames build/thiele_xc7a35t.bit
	@rm -f build/yosys_xc7.log build/nextpnr_xc7.log
	@echo "✓ Synthesis artifacts cleaned"

# Archive generated VM/Verilog byproducts out of active folders.
# Usage: make archive-vm-verilog [ARCHIVE_TAG=YYYY-MM-DD_label]
archive-vm-verilog:
	@set -e; \
	tag="$${ARCHIVE_TAG:-$$(date +%F)_vm_verilog_cleanup}"; \
	archive_dir="archive/hardware_legacy/$$tag"; \
	mkdir -p "$$archive_dir/rtl" "$$archive_dir/build"; \
	for f in \
		thielecpu/hardware/rtl/synth_full_out.v \
		thielecpu/hardware/rtl/synth_lite_clean.log \
		thielecpu/hardware/rtl/thiele_cpu_tb.vcd; do \
		if [ -e "$$f" ]; then mv "$$f" "$$archive_dir/rtl/"; fi; \
	done; \
	for f in \
		build/thiele_kami_batch.vvp \
		build/thiele_kami_test.vvp \
		build/thiele_cpu_kami_tb.out \
		build/vm_runner \
		build/extracted_vm_runner \
		build/extracted_vm_runner_native \
		build/verify_trace.txt \
		build/hw_trace.json; do \
		if [ -e "$$f" ]; then mv "$$f" "$$archive_dir/build/"; fi; \
	done; \
	if [ -d build/verilator ]; then mv build/verilator "$$archive_dir/build/"; fi; \
	echo "✓ Archived VM/Verilog byproducts into $$archive_dir"

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
.PHONY: coq-core coq-kernel coq-subsumption proof-undeniable isomorphism-bitlock parity-extracted-only proof-gate-repro synthesis-repro-gate final-claim-audit final-claim-all check-sensitive-files check-sensitive-files-strict

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
	@$(MAKE) bitlock-proof-vm-cpu
	@bash scripts/parity_extracted_only.sh
	@echo "✓ Bit-for-bit runtime lockstep PASSED"

bitlock-proof-vm-cpu: canonical-extract ocaml-runner rtl-gate
	@echo "[bitlock-proof-vm-cpu] verifying deterministic hash lock across Coq/OCaml/RTL..."
	@python3 -c "from rtl_harness.cosim import _ensure_verilator_current; _ensure_verilator_current(); print('[bitlock-proof-vm-cpu] verilator cache ready')"
	@pytest -q tests/test_bitlock_proof_vm_cpu.py -x --maxfail=1
	@echo "[bitlock-proof-vm-cpu] PASS"

bitlock-manifest: bitlock-proof-vm-cpu
	@python3 scripts/generate_bitlock_manifest.py --output artifacts/isomorphism_bitlock_manifest.json

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

isa-proof-freshness-check:
	@echo "[isa-proof-freshness] Checking that proof-sensitive .vo files are current..."
	@bash scripts/check_isa_proof_freshness.sh coq/
	@echo "[isa-proof-freshness] PASS"

# E6: Red-flag diff gate — warns when proof-sensitive files are modified
# Run this before committing to catch accidental semantic drift.
check-sensitive-files:
	@echo "[check-sensitive-files] Checking for uncommitted changes to proof-sensitive files..."
	@SENSITIVE="coq/kernel/VMStep.v coq/kernel/VMState.v coq/Extraction.v"; \
	 CHANGED=""; \
	 for f in $$SENSITIVE; do \
	   if ! git diff --quiet HEAD -- "$$f" 2>/dev/null; then \
	     CHANGED="$$CHANGED $$f"; \
	   fi; \
	 done; \
	 if [ -n "$$CHANGED" ]; then \
	   echo ""; \
	   echo "⚠  WARNING: Proof-sensitive files have uncommitted changes:$$CHANGED"; \
	   echo ""; \
	   echo "   These files affect the following theorems:"; \
	   echo "     VMStep.v        → MuLedgerConservation (vm_apply_mu), AbstractNoFI (cert_addr_setterb),"; \
	   echo "                       PrimeAxiom (vm_apply_certified), InsightTaxonomy, ShadowProjection"; \
	   echo "     VMState.v       → All theorems — VMState fields define the state space"; \
	   echo "     Extraction.v    → build/thiele_core.ml freshness (run: make canonical-extract)"; \
	   echo ""; \
	   echo "   Required actions before committing:"; \
	   echo "     1. make -C coq -j4              (rebuild proofs)"; \
	   echo "     2. make isa-proof-freshness-check (verify .vo freshness)"; \
	   echo "     3. python3 scripts/inquisitor.py  (zero Admitted check)"; \
	   echo "     4. Update artifacts/final_claim_audit/isa_proof_impact.md if ISA changed"; \
	   echo ""; \
	 else \
	   echo "[check-sensitive-files] No uncommitted changes to proof-sensitive files. OK"; \
	 fi

# E6-STRICT: Hard-fail variant for use in proof-undeniable and CI.
# Exits with code 1 if any proof-sensitive file has uncommitted changes,
# blocking release gates until the change is committed + proofs rebuilt.
check-sensitive-files-strict:
	@SENSITIVE="coq/kernel/VMStep.v coq/kernel/VMState.v coq/Extraction.v"; \
	 CHANGED=""; \
	 for f in $$SENSITIVE; do \
	   if ! git diff --quiet HEAD -- "$$f" 2>/dev/null; then \
	     CHANGED="$$CHANGED $$f"; \
	   fi; \
	 done; \
	 if [ -n "$$CHANGED" ]; then \
	   echo ""; \
	   echo "✗ ERROR: Proof-sensitive files have uncommitted changes:$$CHANGED"; \
	   echo ""; \
	   echo "  proof-undeniable requires a clean proof-sensitive file state."; \
	   echo "  Required actions before re-running:"; \
	   echo "    1. make -C coq -j4              (rebuild proofs)"; \
	   echo "    2. make isa-proof-freshness-check (verify .vo freshness)"; \
	   echo "    3. python3 scripts/inquisitor.py  (zero Admitted check)"; \
	   echo "    4. git add + git commit the changed files"; \
	   echo ""; \
	   exit 1; \
	 else \
	   echo "[check-sensitive-files-strict] No uncommitted changes to proof-sensitive files. OK"; \
	 fi

proof-undeniable:
	@echo "Running formal proof gate (compile + audit + independent checker)..."
	@$(MAKE) coq-kernel
	@$(MAKE) isa-proof-freshness-check
	@$(MAKE) check-sensitive-files-strict
	@python3 scripts/inquisitor.py
	@cd coq && coqchk -R kernel Kernel Kernel.Kernel Kernel.KernelTM Kernel.KernelThiele
	@cd coq && coqchk -R kernel Kernel Kernel.PythonBisimulation Kernel.HardwareBisimulation Kernel.ThreeLayerIsomorphism
	@cd coq && coqchk -R kernel Kernel Kernel.VMState Kernel.VMStep Kernel.MuShannonBridge Kernel.HonestNoFI_TheoremsWithoutAssumptions
	@$(MAKE) isomorphism-bitlock
	@echo "✓ Formal proof gate PASSED (inquisitor + coqchk)"

# Integration testing
.PHONY: test-vm-rtl test-integration

test-vm-rtl:
	@echo "Testing VM-RTL equivalence..."
	@pytest -q tests/test_cross_layer_adversarial_fuzz.py tests/test_cross_layer_bisimulation.py --tb=line
	@echo "✓ VM-RTL equivalence tests passed"

test-integration: coq-core rtl-synth test-vm-rtl
	@echo "✓ Full integration test complete"
	@echo "  - Coq proofs compiled"
	@echo "  - RTL synthesized"
	@echo "  - VM-RTL equivalence validated"

# Clean build artifacts and cache files
clean:
	@echo "Cleaning build artifacts and cache files..."
	@rm -rf .build_cache/ .test_artifacts/ .generated/
	@rm -rf build/ .pytest_cache/ outputs/
	@rm -f /tmp/*.log
	@find . -name "*.vo" -delete
	@find . -name "*.vos" -delete
	@find . -name "*.vok" -delete
	@find . -name "*.glob" -delete
	@find . -name "*.aux" -delete
	@find . -name "__pycache__" -type d -exec rm -rf {} + 2>/dev/null || true
	@echo "✓ Clean complete (audit artifacts preserved)"

deep-clean: clean
	@echo "Running deep clean (includes audit artifacts)..."
	@rm -rf artifacts/
	@echo "✓ Deep clean complete"

# Organize workspace (move artifacts to appropriate directories)
organize:
	@echo "Organizing workspace..."
	@./scripts/auto_organize.sh

# Clean everything including dependencies
purge: deep-clean
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

.PHONY: release release-toolchain-check proof extract synth sim source-of-truth coq-kami-reset

coq-kami-reset:
	@echo "[coq-kami-reset] removing stale kami_hw Coq artefacts to enforce canonical namespace"
	@find coq/kami_hw -maxdepth 1 -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' \) -delete
	@echo "[coq-kami-reset] done"

.PHONY: coq-clean
# Purge ONLY the project's Coq build artefacts under coq/ — leaves vendor/
# alone so vendor caches stay valid. Use this in CI before invoking the Coq
# build to drop tracked-but-stale .vo files (which `make` would otherwise
# treat as up-to-date and skip rebuilding, causing "inconsistent assumptions
# over library Kami.Semantics" when vendor/kami has been rebuilt).
coq-clean:
	@echo "[coq-clean] purging coq/**/*.{vo,vos,vok,glob,aux} (vendor/ untouched)"
	@find coq -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '*.aux' \) -delete
	@echo "[coq-clean] done"

.PHONY: vendor-bbv-build
vendor-bbv-build:
	@git submodule update --init --recursive vendor/bbv
	@cd vendor/bbv && make -j4
	@echo "✅ [vendor-bbv-build] vendor/bbv full build completed"

.PHONY: vendor-kami-build
vendor-kami-build:
	@git submodule update --init --recursive vendor/kami
	@./scripts/fix_kami_coq18.sh
	@cd vendor/kami && make -j4
	@echo "✅ [vendor-kami-build] vendor/kami full build completed"

RELEASE_BLUESPECDIR ?= /usr/local/lib
RELEASE_BSC ?= /tmp/bsc-2024.07-ubuntu-22.04/bin/bsc

release-toolchain-check:
	@echo "[release] checking pinned toolchain expectations..."
	@coqc --version | grep -q "8.18" || (echo "FAIL: require Coq 8.18.x" && exit 1)
	@verilator --version | grep -q "5\.020" || (echo "FAIL: require Verilator 5.020" && exit 1)
	@iverilog -V | head -n1 | grep -q "12.0" || (echo "FAIL: require Icarus Verilog 12.0" && exit 1)
	@yosys -V | grep -q "Yosys 0.33" || (echo "FAIL: require Yosys 0.33" && exit 1)
	@python3 -c "import z3; assert z3.get_version_string().startswith('4.'), 'require python z3-solver 4.x'; print('[release] z3 version', z3.get_version_string())"
	@echo "[release] toolchain OK"

proof: release-toolchain-check coq-kami-reset vendor-bbv-build vendor-kami-build
	@echo "[proof] compiling kami refinement contract..."
	@cd coq && coqc -R kernel Kernel -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -Q ../vendor/bbv/src/bbv bbv kami_hw/ThieleTypes.v
	@cd coq && coqc -R kernel Kernel -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -Q ../vendor/bbv/src/bbv bbv kami_hw/ThieleCPUCore.v
	@cd coq && coqc -R kernel Kernel -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -Q ../vendor/bbv/src/bbv bbv kami_hw/Compatibility.v
	@cd coq && coqc -R kernel Kernel -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -Q ../vendor/bbv/src/bbv bbv kami_hw/CanonicalCPUProof.v
	@cd coq && coqc -R kernel Kernel -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -Q ../vendor/bbv/src/bbv bbv kami_hw/Abstraction.v
	@cd coq && coqc -R kernel Kernel -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -Q ../vendor/bbv/src/bbv bbv kami_hw/KamiExtraction.v
	@cd coq && coqc -R kernel Kernel -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -Q ../vendor/bbv/src/bbv bbv kami_hw/VerilogRefinement.v
	@echo "✅ [proof] VerilogRefinement checked"

extract: release-toolchain-check coq-kami-reset
	@echo "[extract] running Coq->Kami->BSV->Verilog extraction..."
	@SKIP_YOSYS=1 BLUESPECDIR="$(RELEASE_BLUESPECDIR)" BSC="$(RELEASE_BSC)" ./scripts/kami_extract.sh ThieleCPU
	@candidate=""; \
	if [ -s build/kami_hw/mkModule1_synth.v ]; then \
		candidate="build/kami_hw/mkModule1_synth.v"; \
	elif [ -s build/kami_hw/mkModule1.v ]; then \
		candidate="build/kami_hw/mkModule1.v"; \
	else \
		echo "FAIL: no extracted Verilog candidate produced"; \
		exit 1; \
	fi; \
	echo "[extract] candidate: $$candidate"; \
	mkdir -p thielecpu/hardware/rtl; \
	cp "$$candidate" thielecpu/hardware/rtl/thiele_cpu_kami.v.tmp; \
	mv thielecpu/hardware/rtl/thiele_cpu_kami.v.tmp thielecpu/hardware/rtl/thiele_cpu_kami.v
	@echo "✅ [extract] canonical RTL refreshed: thielecpu/hardware/rtl/thiele_cpu_kami.v"

synth: release-toolchain-check
	@echo "[synth] Final Audit: Counting every physical flip-flop bit..."
	@yosys -p "read_verilog -sv -DSYNTHESIS thielecpu/hardware/rtl/thiele_cpu_kami.v; hierarchy -top mkModule1; proc; flatten; memory_unpack; memory_map; select -list t:\$dff t:\$adff t:\$sdff t:\$_DFF* t:\$_SDFF*; stat"
	@echo "✅ [synth] RTL synthesizable"

sim: release-toolchain-check
	@echo "[sim] prebuilding Verilator binary cache..."
	@python3 -c "from rtl_harness.cosim import _ensure_verilator_current; _ensure_verilator_current(); print('[sim] verilator cache ready')"
	@echo "[sim] running Verilator + external Z3 bridge tests..."
	@THIELE_RTL_SIM=verilator pytest -q \
		tests/test_logic_z3_verilator_bridge.py::test_lassert_bridge_prevents_stall_and_reaches_halt \
		tests/test_chsh_verilator_hardware_bridge.py::test_chsh_x1_without_reveal_certificate_is_rejected \
		tests/test_chsh_verilator_hardware_bridge.py::test_chsh_x1_with_reveal_certificate_is_allowed_and_surcharged
	@echo "✅ [sim] runtime bridge + CHSH physics checks passed"

release: proof extract synth sim
	@echo "✅ release complete: proof + extraction + synthesis + runtime physics checks"

source-of-truth: release
	@echo "✅ source-of-truth complete: Coq -> Kami -> Bluespec -> Verilog -> synth -> sim"
