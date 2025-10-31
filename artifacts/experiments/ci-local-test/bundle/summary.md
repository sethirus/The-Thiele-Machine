# Thiele proofpack summary — ci-local-test

- **Verdict:** PASS
- **Created:** 1970-01-01T00:00:00Z
- **Bundled artefacts:** 45
- **Notes:**
  - CI-smoke

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
- datasets analysed = 0

## Turbulence data
- datasets analysed = 0
