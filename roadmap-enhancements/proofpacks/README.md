# Proofpack README

This directory contains paper-grade proofpacks for reproducible research.

## Structure

Each subdirectory is a self-contained proofpack:

- `dialogue/` - Dialogue of the One experiment
- `engine/` - Engine of Truth results
- `calorimeter/` - µ-bit calorimeter calibration
- `adversarial/` - Adversarial diagnostic tests

## Creating a Proofpack

```bash
# Run experiment
cd proofpacks/dialogue/
make run

# Generate receipts
make receipts

# Package
tar -czf dialogue.proofpack.tar.gz dialogue/
```

## Verifying a Proofpack

```bash
# Extract
tar -xzf dialogue.proofpack.tar.gz
cd dialogue/

# Verify
make verify
```

## Expected Digests

Each proofpack's README lists the expected global digest for verification.

| Proofpack    | Global Digest                                                    |
|--------------|------------------------------------------------------------------|
| dialogue     | `PLACEHOLDER_DIALOGUE_DIGEST`                                   |
| engine       | `PLACEHOLDER_ENGINE_DIGEST`                                     |
| calorimeter  | `PLACEHOLDER_CALORIMETER_DIGEST`                                |
| adversarial  | `PLACEHOLDER_ADVERSARIAL_DIGEST`                                |

## Citation

Each proofpack is citable independently via Zenodo DOIs:

- Dialogue: `10.5281/zenodo.PLACEHOLDER_DIALOGUE_DOI`
- Engine: `10.5281/zenodo.PLACEHOLDER_ENGINE_DOI`
- Calorimeter: `10.5281/zenodo.PLACEHOLDER_CALORIMETER_DOI`
- Adversarial: `10.5281/zenodo.PLACEHOLDER_ADVERSARIAL_DOI`
