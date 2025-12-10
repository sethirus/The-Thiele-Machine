# Law receipt verification guide

The `make law` pipeline synthesises a discrete lattice law, records the
hash-chained receipt, regenerates the Coq harness, and replays the
end-to-end verifier. The resulting bundle lives alongside the Bell pack
in `artifacts/`.

## Quick start

```
make law
```

The target performs three steps:

1. `python3 tools/make_law_receipt.py --sites 8 --steps 16 --seed 2025`
2. `python3 tools/verify_law_receipt.py artifacts/law_receipt.jsonl --coq-binary $(COQTOP)`
3. `python3 tools/verify_end_to_end.py --skip-hardware` (the verifier now bundles
   the halting boundary and Bell/CHSH checks; add `--skip-bell` if those artefacts
   are already confirmed on your system)

Set `LAW_SKIP_COQ=1` when the Coq toolchain is unavailable. The verifier
skips the harness check in that mode and still validates the receipt
integrity and lattice analytics.

## Manual verification

To re-run the checks by hand:

1. Generate a receipt with custom parameters (for example a shorter
   lattice for debugging):
   ```
   python3 tools/make_law_receipt.py --sites 6 --steps 12 --seed 1337 --output artifacts/debug_law.jsonl
   ```
2. Run the verifier. Supply `--skip-coq` to avoid invoking the harness.
   ```
   python3 tools/verify_law_receipt.py artifacts/debug_law.jsonl --coq-binary coqtop
   ```
3. Inspect the generated harness at
   `artifacts/debug_law.LawCheckInstance.v`. The script records the
   SHA256 and byte length in the summary; the verifier checks the digest
   before optionally executing the proof.

## Receipt structure

The JSON Lines receipt contains:

- A `time_slice` entry for each simulated slice with the exact lattice
  field values (rational numerators and denominators).
- A final `law_summary` block summarising the derived update rule,
  Lagrangian coefficients, conserved quantities, recursion operator,
  polynomial witnesses, MDL scores, μ-accounting, and harness metadata.
  The `nusd_bound` object inside the summary expands the No Unpaid Sight
  Debt inequality: it records μ-question/answer bits, the chosen
  temperature, the Landauer work bound, and—when supplied—the empirical
  μ↔joule calibration digest. The summary is signed with an HMAC keyed by
  `ThieleLawKey`.

Refer to `docs/law_receipt.schema.json` for a machine-readable schema of
these entries. For cross-domain variants that apply the same NUSD
analysis to logic, computation, and turbulence traces see
`docs/HOWTO_VERIFY_NUSD_RECEIPT.md`.

## Checking the μ ↔ joule calibration

Run the helper script to inspect the calibration dataset recorded in the
receipt:

```
python3 tools/mu_calibration.py mu_bit_correlation_data.json --temperature 300 --mu-bits 256
```

`tools/verify_law_receipt.py` executes the same calculations and fails if
the digest, sample counts, mean energy-per-μ-bit, or the derived work
bound diverge from the embedded values beyond 10⁻⁹ relative tolerance.
