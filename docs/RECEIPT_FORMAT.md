# RECEIPT_FORMAT

A receipt is JSON:

```json
{
  "steps": [
    {
      "step_id": 0,
      "partition_id": 0,
      "axiom_ids": ["axiom"],
      "certificate": "opaque string",
      "certificate_hash": "sha256",
      "mu_delta": 1
    }
  ],
  "mu_total": 1
}
```

`certificate_hash` is `sha256(certificate)`.  `mu_delta` and `mu_total` are numbers or the string `"INF"` for paradox.
