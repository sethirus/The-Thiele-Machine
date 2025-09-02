# The Thiele Machine: Archival Artifact

This is the archival artifact for the paper "The Thiele Machine: A Formal Model of Computation with Provable Consistency".

## Contents

- `documents/The_Thiele_Machine.tex`: The final LaTeX source of the paper
- `documents/The_Thiele_Machine.pdf`: The compiled PDF of the paper
- `coq/`: Complete Coq source files and build system
- `scripts/`: Python scripts for empirical experiments and μ-spec verification
- `compute_mu_bits.py`: Script to compute μ-bit costs for formulas and partitions
- `verify_receipt_mu_spec.py`: Script to verify receipt compliance with μ-spec
- `mu-spec.json`: Canonical μ-spec v1.0 specification
- `results/`: Experimental results and receipts

## Building the Coq Proofs

### Requirements

- Coq version 8.18.0 (compiled with OCaml 4.14.1)
- GNU Make

### Build Instructions

1. Navigate to the `coq` directory:
   ```
   cd coq
   ```

2. Build the proofs:
   ```
   make
   ```

This will compile all the Coq source files and verify the mechanized proofs.

## Reproducing Experiments

See the `scripts/` directory for Python scripts to reproduce the empirical experiments described in the paper.

## μ-spec Verification

The `mu-spec.json` file contains the canonical specification for μ-bit encoding and accounting.

- `compute_mu_bits.py`: Compute μ-bit costs for logical formulas or partitions.
  ```
  python compute_mu_bits.py --formula "(assert (= x 1))"
  ```

- `verify_receipt_mu_spec.py`: Verify that a receipt's μ-bit calculations comply with μ-spec.
  ```
  python verify_receipt_mu_spec.py --receipt receipt.json
  ```

## License

This work is provided as-is for academic and research purposes.