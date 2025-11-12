# How to verify the phase-three proofpack

This short guide explains how to rebuild and audit the combined witness bundle
that packages the Bell, lattice-law, universal NUSD, and turbulence head-to-head
receipts.

## 1. Regenerate the bundle

From the repository root run:

```
make proofpack-phase3
```

The target ensures all prerequisite receipts are current, stages the bundle
under `artifacts/phase_three_bundle/`, compresses it to
`artifacts/phase_three/phase_three_proofpack.tar.gz`, and immediately invokes
the self-checker on the resulting archive.

## 2. Verify independently

To re-verify an existing archive (for example after transferring it to a new
machine), run:

```
python3 tools/verify_phase_three_proofpack.py artifacts/phase_three/phase_three_proofpack.tar.gz
```

The verifier performs four checks:

1. Recomputes the SHA-256 digest of every file mentioned in the bundle
   manifest;
2. Replays `tools/verify_bell_receipt.py`, `tools/verify_law_receipt.py`, the
   four `tools/verify_nusd_receipt.py` domain checks, and
   `tools/verify_turbulence_head_to_head.py` using the bundled calibration
   dataset;
3. Compiles `coq/PhaseThreeWitness.v`, which in turn loads the auto-generated
   harnesses and proves the master statement `phase_three_verified`;
4. Reports success only if every receipt, signature, and proof obligation
   matches the staged artefacts.

The harness relies on the new Coq module `ThieleMachine.PhaseThree`, which shows
that a positive μ-gap implies the sighted solver is strictly cheaper than the
blind baseline.  This links the Phase 1 “one inequality everywhere” receipts
with the Phase 2 head-to-head witness inside a single mechanised proof.

## 3. Contents of the archive

The compressed archive contains:

- `receipts/` – all JSONL receipts plus their auto-generated Coq harnesses,
- `coq/PhaseThreeWitness.v` – the combined proof harness,
- `mu_bit_correlation_data.json` – the calibration dataset referenced by the
  turbulence artefacts,
- `manifest.json` – SHA-256 digests for every staged file,
- `README.md` – a concise summary of the μ totals and verification steps.

Auditors can extract the archive, inspect or re-run the harness, and confirm
that the receipts, signatures, and Coq lemmas line up with the final theorem.
