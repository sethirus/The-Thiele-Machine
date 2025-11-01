# Pillar 4 – Receipts and zero-trust auditability

`verify_receipts.py` replays the Tseitin bundle without invoking any solver. It
checks that:

- the blind solver's μ matches its Cadical conflict counter,
- the sighted rank certificates have a positive gap,
- `μ_sighted = μ_question + μ_answer`, and
- the recorded information gain equals the μ-answer portion mandated by
  `spec/mu_spec_v2.md`.

Run the audit with:

```bash
make -C proof-of-thiele receipts
```

The script walks every `receipt_*.json` file in the bundle, validates the
invariants, and prints a status histogram. Any deviation triggers an exception,
making the receipts independently checkable without the heavy proofpack
infrastructure.
