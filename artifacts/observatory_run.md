# Observatory Run – 2025-11-29

This snapshot records the verification-and-measurement pass requested for aligning the Coq VM, RTL harness, and Monte Carlo probes.

## Tooling and builds
- Coq core build: `make -C coq core` (success).
- Python/RTL checks: `pytest tests/test_opcode_alignment.py tests/test_hardware_alignment.py tests/test_vm.py tests/test_vm_halt.py tests/test_mu.py tests/test_alpha_refinement.py tests/test_chsh_manifold.py tests/test_fine_structure.py -q` (18 passed, 1 skipped for 16-bit EMIT probe).

## Monte Carlo probes (2025-xx-xx)
- Certificate-reader density (CSR.CERT_ADDR proxy, requires execution to reach MDLACC):
  - 32 bits: 2 readers / 2 000 valid ⇒ **0.00100**.
  - 64 bits: 2 / 2 000 ⇒ **0.00100**.
  - 128 bits: 3 / 2 000 ⇒ **0.00150**.

## CHSH manifold harness
- Trials: 2 000 with hashed level/payload hidden variables; hidden vectors are
  setting-independent in both modes.
- Local masks: **S ≈ 1.25** (classical bound respected).
- Meta masks (different window overlaps only): **S ≈ 0.76**. No violation was
  observed without setting-aware hidden variables, underscoring that geometry
  alone stays within the classical limit.

## Gravity sandbox (µ-weighted two-body)
- Final state after 200 steps (Δt = 0.1): mass derived from opcode irreversibility only.
  - `cold`: pos ≈ (599.51, 0.00), vel ≈ (31.52, 0.00).
  - `hot`: pos ≈ (-74.06, 0.00), vel ≈ (-3.94, 0.00).

