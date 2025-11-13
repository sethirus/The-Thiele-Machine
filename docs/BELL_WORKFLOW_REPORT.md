# Bell / CHSH workflow

This document captures the reproducible supra-quantum sandbox delivered in this
repository.  All correlation tables are exact rational distributions stored in
plain-text artefacts so reviewers can audit every probability and regenerate
downstream analyses.

## Reference correlation tables

The following tables live under `artifacts/bell/`:

| Artefact | Description | CHSH value |
| --- | --- | --- |
| `supra_quantum_16_5.csv` | Thiele’s supra-quantum box with exact correlators that achieve \(S = 16/5 = 3.2\). | 3.2 |
| `polytope_scan.csv` | Mixture scan over classical, Thiele, and PR boxes with weight and CHSH columns. | Range 2–4 |
| `nearby_scan.json` | Perturbation summary around the supra box reporting accepted samples and CHSH bounds. | Near 3.2 |

All tables are no-signalling and normalised.  The repository also ships the
canonical PR box and the classical optimum as inline generators inside the
verification tooling so they can be re-derived from first principles.

## Verification entry point

`tools/verify_bell_workflow.py` orchestrates the full audit:

1. Loads `supra_quantum_16_5.csv`, checks normalisation and no-signalling, and
   recomputes \(S = 16/5\).
2. Derives the classical optimum via a deterministic-program search, verifying
   it respects the \(S \leq 2\) bound.
3. Reconstructs the PR box in code and confirms \(S = 4\).
4. Regenerates `polytope_scan.csv` and `nearby_scan.json`, ensuring the sampled
   mixtures span the \([2, 4]\) range without violating the supra-quantum
   baseline.

The script exits non-zero if any distribution fails a normalisation or
no-signalling check, if the expected CHSH values are not reproduced, or if the
regenerated artefacts drift outside the documented ranges.  It is also wired
into `tools/verify_end_to_end.py` so the Bell audit runs alongside the rest of
the regression pipeline.
