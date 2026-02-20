#!/usr/bin/env python3
"""Test runner that stops at first timeout or failure."""
import subprocess
import sys
import time

test_files = """tests/alignment/test_comprehensive_alignment.py
tests/alignment/test_mu_alignment.py
tests/test_2d_mesh_creation.py
tests/test_accelerator_cosim.py
tests/test_actual_truth_simplified.py
tests/test_advantage_benchmarks.py
tests/test_alpha_refinement.py
tests/test_axiom_geometric_calibration.py
tests/test_axiom_horizon_cycle.py
tests/test_axiom_source_normalization.py
tests/test_benchmark_suite.py
tests/test_bianchi_enforcement.py
tests/test_bisimulation.py
tests/test_bisimulation_complete.py
tests/test_c1_physics_divergence_verifier.py
tests/test_c_causal_causal_verifier.py
tests/test_c_entropy_entropy2_verifier.py
tests/test_c_rand_randomness_verifier.py
tests/test_c_tomo_tomography_verifier.py
tests/test_canonical_hash_golden.py
tests/test_certcheck.py
tests/test_christoffel_corrected_metric.py
tests/test_christoffel_empirical.py
tests/test_christoffel_flat_spacetime.py
tests/test_christoffel_v3_metric.py
tests/test_chsh_manifold.py
tests/test_connectivity_enforcement.py
tests/test_coq_available.py
tests/test_coq_bridge_coverage_links.py
tests/test_coq_compile_gate.py
tests/test_cross_layer_comprehensive.py
tests/test_cross_platform_isomorphism.py
tests/test_crypto_isomorphism.py
tests/test_dialogue_of_the_one.py
tests/test_discovery_enhancements.py
tests/test_discrete_topology.py
tests/test_efficient_discovery.py
tests/test_einstein_equation_empirical.py
tests/test_einstein_nonvacuum_empirical.py
tests/test_einstein_vacuum_empirical.py
tests/test_einstein_with_v3_metric.py
tests/test_emergent_geometry_proxies.py
tests/test_equivalence_bundle.py
tests/test_even_factor.py
tests/test_extracted_vm_runner.py
tests/test_extraction_freshness.py
tests/test_falsifiable_predictions.py
tests/test_find_actual_truth.py
tests/test_fine_structure.py
tests/test_foundry_generated_surface.py
tests/test_full_stack_geometric_factorization.py
tests/test_fuzz_isomorphism.py
tests/test_gauss_bonnet_2d.py
tests/test_geometric_factorization_claim.py
tests/test_isomorphism_violation_detection.py
tests/test_isomorphism_vm_vs_coq.py
tests/test_isomorphism_vm_vs_verilog.py
tests/test_metric_diagnosis.py
tests/test_metric_position_dependent.py
tests/test_mu.py
tests/test_mu_costs.py
tests/test_mu_entropy_n_bits_certificate.py
tests/test_mu_entropy_one_bit_certificate.py
tests/test_mu_fixed.py
tests/test_mu_gravity_axioms.py
tests/test_mu_gravity_calibration_validator.py
tests/test_mu_gravity_physics_analysis.py
tests/test_mu_profiler_universality.py
tests/test_mu_signaling_lower_bound.py
tests/test_nofi_pyexec_nonforgeability.py
tests/test_nofi_semantic_structure_event.py
tests/test_observational_no_signaling.py
tests/test_opcode_alignment.py
tests/test_opcode_isomorphism.py
tests/test_openfpga_flow.py
tests/test_partition_boundary.py
tests/test_partition_isomorphism_minimal.py
tests/test_partition_rsa_factorization.py
tests/test_period_oracle.py
tests/test_phase1_long_run.py
tests/test_phase3_bad_graph.py
tests/test_phase4_null_hypothesis.py
tests/test_pnew_topology_change.py
tests/test_predicate_parser.py
tests/test_properties.py
tests/test_property_bisimulation.py
tests/test_qm_divergent.py
tests/test_quantitative_nofreeinsight.py
tests/test_random_program_fuzz.py
tests/test_real_angles_from_metric.py
tests/test_receipt_chain.py
tests/test_refinement.py
tests/test_rigorous_isomorphism.py
tests/test_rsa_scaling.py
tests/test_rtl_compute_isomorphism.py
tests/test_rtl_mu_charging.py
tests/test_rtl_synthesis_gate.py
tests/test_security_monitor.py
tests/test_shor_demo.py
tests/test_stress_energy_pnew.py
tests/test_structural_verifier.py
tests/test_structure_period_finding.py
tests/test_thesis_verify.py
tests/test_three_layer_isomorphism.py
tests/test_three_layer_isomorphism_fuzz.py
tests/test_three_layer_isomorphism_semantic.py
tests/test_topology_curvature_bridge.py
tests/test_transition_logic.py
tests/test_utm_program_validation.py
tests/test_verification_fuzz.py
tests/test_verilog_cosim.py
tests/test_vm_cli_c_and_stdin.py
tests/test_vm_cli_input_prompt.py
tests/test_vm_encoding_validation.py
tests/trs_conformance/test_trs10.py
tests/trs_conformance/test_vectors.py""".strip().split('\n')

for i, test_file in enumerate(test_files, 1):
    print(f"\n{'='*80}")
    print(f"[{i}/{len(test_files)}] Testing: {test_file}")
    print('='*80)

    start = time.time()
    try:
        result = subprocess.run(
            ['python', '-m', 'pytest', test_file, '-v', '--tb=short'],
            capture_output=True,
            text=True,
            timeout=30
        )
        elapsed = time.time() - start

        if result.returncode != 0:
            # Check if it's a "no tests collected" issue (but allow skipped tests)
            if ("no tests ran" in result.stdout or "collected 0 items" in result.stdout) and "skipped" not in result.stdout.lower():
                print(f"WARNING: No tests found in {elapsed:.2f}s - needs fixing")
                print(f"\n⚠️  First test with no tests found: {test_file}")
                sys.exit(1)
            else:
                print(f"FAILED after {elapsed:.2f}s")
                print("STDOUT:", result.stdout[-1000:])
                print("STDERR:", result.stderr[-1000:])
                sys.exit(1)
        else:
            # Success (includes skipped tests)
            if "skipped" in result.stdout.lower() and "passed" not in result.stdout.lower():
                print(f"SKIPPED in {elapsed:.2f}s (missing dependencies)")
            else:
                print(f"PASSED in {elapsed:.2f}s")

    except subprocess.TimeoutExpired:
        elapsed = time.time() - start
        print(f"TIMEOUT after {elapsed:.2f}s")
        print(f"\n❌ First timeout found: {test_file}")
        sys.exit(1)

print(f"\n{'='*80}")
print("✅ All tests passed within 30 seconds!")
print('='*80)
