# Pillar 3 – μ-bit conservation

The μ-spec v2.0 contract (`spec/mu_spec_v2.md`) defines the additive tariff
μ(q, N, M) = 8·|canon(q)| + log₂(N/M) that every Thiele instruction must
respect. The Tseitin receipts bundle ships per-run μ ledgers so auditors can
check that:

- `μ_sighted = μ_question + μ_answer`,
- `μ_answer` coincides with the recorded information gain, and
- the blind solver pays one μ-bit per Cadical conflict.

Replay the conservation check with:

```bash
make -C proof-of-thiele cost-model
```

This command imports `tools.check_mu_ledger` to validate every receipt and then
summarises the μ totals across the entire sweep. Any mismatch between the
recorded counters and the μ-spec raises immediately.
