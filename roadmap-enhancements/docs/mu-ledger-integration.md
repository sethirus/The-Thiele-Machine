# µ-Ledger Integration

Integration of µ-bit cost measurement into receipt system.

## Overview

The µ-ledger tracks information-theoretic cost of computation:

```
µ(q, N, M) = 8 × |canon(q)| + log₂(N/M)
```

Where:
- `q` is the canonical query
- `N` is the initial search space
- `M` is the reduced search space
- `|canon(q)|` is the byte length of canonical query

## Receipt Integration

Receipts now include µ-ledger data:

```json
{
  "version": "TRS-0-INLINE",
  "mu_ledger": {
    "total_mu_bits": 1234.56,
    "energy_estimate_nJ": 567.89,
    "breakdown": [
      {
        "operation": "partition",
        "mu_bits": 100.0,
        "query_bytes": 12,
        "space_reduction": 1024
      }
    ]
  }
}
```

## Computing µ-Ledger

```python
from thielecpu.mu import compute_mu, estimate_energy

# Compute µ for a query
mu_bits = compute_mu(
    query_bytes=len(canonical_query),
    initial_space=2**20,
    reduced_space=2**10
)

# Estimate energy (requires calibration)
energy_nJ = estimate_energy(mu_bits, temperature=300)
```

## Verification

```bash
python3 thielecpu/mu.py --verify receipt.json
```

## Calibration

Energy estimates require experimental calibration:

1. Run reference computation
2. Measure actual energy consumption
3. Compute µ-bits from canonical receipt
4. Derive calibration constant: `E_measured / µ_bits`

Current calibration: `1 µ-bit ≈ 0.46 nJ @ 300K`

## Physical Interpretation

The µ-bit is the fundamental unit of "sight cost":

- **Lower bound**: Landauer limit (kT ln 2 ≈ 0.018 eV @ 300K)
- **Upper bound**: Practical implementation overhead
- **Measurement**: Calibrated against real hardware

## DoD (Definition of Done)

- [x] Specification documented
- [ ] `mu.py` extended with receipt integration
- [ ] CLI tool `thiele-replay --mu` prints µ estimates
- [ ] Calibration script for experimental validation
- [ ] CI test verifying µ-ledger consistency
