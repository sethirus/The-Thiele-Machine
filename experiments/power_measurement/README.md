# Power Measurement Experiments

This directory contains tools for measuring **actual energy consumption** to validate the thermodynamic bridge between μ-cost and physical energy.

## Quick Start

### 1. Check Local RAPL Support (FREE)

```bash
python test_rapl_local.py
```

If your local machine has RAPL support, you can run experiments for free:

```bash
python measure_real_power.py
```

### 2. AWS Cloud Option (~$2)

If local RAPL isn't available:

```bash
# Configure AWS first
aws configure

# Set your key pair
export AWS_KEY_NAME="your-key-pair-name"

# Run setup (interactive)
./aws_setup.sh

# Or dry run first
./aws_setup.sh --dry-run
```

## Files

| File | Purpose |
|------|---------|
| `test_rapl_local.py` | Check if your machine has RAPL power measurement |
| `measure_real_power.py` | Run actual power measurement experiments |
| `aws_setup.sh` | Automated AWS spot instance setup |
| `power_results.json` | Results output (created after running) |

## What We're Measuring

The **thermodynamic bridge** predicts:

```
E_physical ≈ μ-cost × C × kT ln(2)
```

Where:
- `E_physical` = actual energy consumed (joules)
- `μ-cost` = information-theoretic cost (μ-bits)
- `C` = overhead constant (expected: 10^6 to 10^12)
- `kT ln(2)` = Landauer limit (~2.87 × 10^-21 J at 300K)

If μ-cost correlates with actual energy:
- **Strong correlation (r > 0.9)**: Evidence FOR the bridge
- **No correlation (r < 0.3)**: Evidence AGAINST the bridge

## Safety Guarantees

The AWS setup includes multiple safety mechanisms:

1. **Spot instances**: ~70% cheaper than on-demand
2. **Max price cap**: Won't exceed $2/hour
3. **Auto-termination**: Instance dies after 25 minutes max
4. **One-time spot**: No recurring charges
5. **Confirmation prompt**: Must type 'y' to proceed

## Expected Results

Based on CPU time correlation (r = 0.94 from test_empirical_correlation.py), we expect:

| Metric | Expected |
|--------|----------|
| Correlation | r > 0.8 |
| Energy per μ-bit | ~10^-9 to 10^-6 J |
| Landauer overhead | ~10^6 to 10^12× |

## Interpretation

| Correlation | Meaning |
|-------------|---------|
| r > 0.9 | Strong evidence for thermodynamic bridge |
| 0.7 < r < 0.9 | Suggestive but not definitive |
| 0.3 < r < 0.7 | Inconclusive |
| r < 0.3 | Evidence against the bridge |

## Requirements

- **Local**: Linux with Intel CPU (Haswell or newer), root access for RAPL
- **AWS**: AWS CLI configured, EC2 key pair, ~$2 budget
