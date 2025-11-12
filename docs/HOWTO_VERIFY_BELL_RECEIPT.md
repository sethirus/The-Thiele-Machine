# Bell Receipt Pack Verification Guide

The `make bell` pipeline produces a receipt-backed CHSH violation with a Coq
harness. The artefacts live under `artifacts/`:

* `bell_receipt.jsonl` – append-only receipt log
* `bell_receipt.BellCheckInstance.v` – auto-generated Coq harness placed next to the receipt

## Generate the artefact

```bash
make bell
```

This command will:

1. run `tools/make_bell_receipt.py` with the default parameters (`N=20000`,
   `epsilon=0.01`, `seed=1337`),
2. execute `tools/verify_bell_receipt.py` to recompute correlators, MDL totals,
   verify the hash chain, re-run the Coq harness, and confirm the HMAC
   signature, and
3. finish with `tools/verify_end_to_end.py --skip-hardware`.

## Standalone verification

To re-verify an existing artefact without regenerating it, run:

```bash
python3 tools/verify_bell_receipt.py artifacts/bell_receipt.jsonl
```

The script prints the Bell and classical `S` scores, the violation margin, and a
green `ALL VERIFIED` banner if everything passes.

Optional arguments:

* `--coqtop` – path to the `coqtop` binary (defaults to `coqtop`).
* `--skip-coq` – run all checks except the Coq harness (useful on systems
  without Coq installed).

The receipt summary stores the Coq load arguments (`-Q coq/thielemachine/coqproofs
ThieleMachine`) alongside the harness metadata, so the verifier reconstructs the
proof environment automatically.

The JSON line structure is documented in `docs/bell_receipt.schema.json`.
