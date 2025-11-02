# Proofpack: Dialogue of the One

Reproducible artifacts for "Dialogue of the One" experiment.

## Overview

This proofpack contains everything needed to reproduce the Dialogue of the One results from the paper.

## Contents

- `src/` - Source code for the dialogue system
- `data/` - Input datasets
- `receipts/` - Cryptographic receipts for each run
- `results/` - Output data and analysis
- `Makefile` - One-command reproduction

## Quick Start

```bash
# Unpack
tar -xf dialogue.proofpack.tar.gz
cd dialogue/

# Reproduce
make run

# Verify
make verify
```

## Expected Output

```
Global digest: abc123...
Analysis completed successfully
Results match paper figures
```

## Paper Reference

See Section 4.2 "Dialogue of the One" in the manuscript.

## Citation

```bibtex
@inproceedings{thiele2025,
  title={The Thiele Machine: Computational Proofs with µ-bit Accounting},
  author={Thiele, Devon},
  year={2025}
}
```
