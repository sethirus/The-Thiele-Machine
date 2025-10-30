# Thiele proofpack summary — public-figshare

- **Verdict:** PASS
- **Created:** 2025-10-30T04:11:58.146304Z
- **Bundled artefacts:** 69
- **Notes:**
  - Bundled with tools.proofpack_bundler

## Phase diagnostics

### Cross Domain — PASS
- blind: PASS (verifier=verifier/cross_domain_blind.json)
  - metadata digests verified
- destroyed: PASS (verifier=verifier/cross_domain_destroyed.json)
  - metadata digests verified
- sighted: PASS (verifier=verifier/cross_domain_sighted.json)
  - metadata digests verified
- Highlight: blind ΔAIC ≥ 96.9
- Highlight: sighted |slope| ≤ 0.0503
- Highlight: destroyed structure ≈ 0
- Highlight: metadata digests verified

### Cwd — PASS
- Protocol directories:
  - blind: cwd/blind
  - destroyed: cwd/destroyed
  - sighted: cwd/sighted
- Highlight: min (Δwork − I) = 15.1 bits
- Highlight: min blind penalty = 16.6 bits
- Highlight: metadata digests verified

### Einstein — PASS
- einstein/sighted: PASS (trials=4, verifier=verifier/einstein_0.json)
  - max |D − μkT| = 3.33e-16
  - mean |D − μkT| = 1.94e-16
  - max |drift| = 0.24
  - metadata digests verified
- Highlight: max |D − μkT| = 3.33e-16
- Highlight: mean |D − μkT| = 1.94e-16
- Highlight: max |drift| = 0.24
- Highlight: metadata digests verified

### Entropy — PASS
- entropy/blind: PASS (trials=4, verifier=verifier/entropy_0.json)
  - Theil–Sen slope CI ≈ [0.558, 1.48]
  - min Spearman ρ = 0.995
  - max Spearman p-value = 0
  - metadata digests verified
- entropy/sighted: PASS (trials=4, verifier=verifier/entropy_1.json)
  - Theil–Sen slope CI ≈ [0.908, 1.17]
  - min Spearman ρ = 0.997
  - max Spearman p-value = 0
  - metadata digests verified
- Highlight: Theil–Sen slope CI ≈ [0.558, 1.48]
- Highlight: min Spearman ρ = 0.995
- Highlight: max Spearman p-value = 0
- Highlight: metadata digests verified

### Landauer — PASS
- landauer/blind: PASS (trials=6, verifier=verifier/landauer_0.json)
  - max |ΔW/(kT ln 2) − Σμ| = 0 bits
  - mean |ΔW/(kT ln 2) − Σμ| = 0 bits
  - tolerance pass rate = 100.0%
  - metadata digests verified
- landauer/sighted: PASS (trials=6, verifier=verifier/landauer_1.json)
  - max |ΔW/(kT ln 2) − Σμ| = 0 bits
  - mean |ΔW/(kT ln 2) − Σμ| = 0 bits
  - tolerance pass rate = 100.0%
  - metadata digests verified
- Highlight: max |ΔW/(kT ln 2) − Σμ| = 0 bits
- Highlight: mean |ΔW/(kT ln 2) − Σμ| = 0 bits
- Highlight: tolerance pass rate = 100.0%
- Highlight: metadata digests verified

## Verdict
All verifiers report THIELE_OK for the bundled artefacts.

## Public data
- datasets analysed = 2
- max OOS error = 1.1%
- min blind ΔAIC = 553
- max destroyed ρ = -0.335
- brownian_beads_02: PASS (verifier=verifier/public_spt_0.json)
  - OOS error = 1.1%
  - blind ΔAIC = 553
  - sighted slope CI ≈ [0.997, 1]
  - destroyed ρ = -0.335
- optical_tweezers_01: PASS (verifier=verifier/public_spt_1.json)
  - OOS error = 0.6%
  - blind ΔAIC = 553
  - sighted slope CI ≈ [0.996, 1]
  - destroyed ρ = -0.335

## Turbulence data
- datasets analysed = 1
- pass rate = 100.0%
- min blind ΔAIC = 996
- mean ρ drop = 0.906
- isotropic1024coarse: PASS (verifier=verifier/turbulence_0.json)
  - sighted ρ = 1
  - sighted runtime slope = 0.0612
  - blind ΔAIC = 996
  - ρ drop = 0.906
