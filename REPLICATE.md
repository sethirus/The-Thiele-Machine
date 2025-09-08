# Replicate in 3 Commands

## Command 1: Install dependencies
```bash
pip install -e .
```

## Command 2: Generate golden data
```bash
python scripts/make_golden.py
```
Expected output: Generates golden receipt files in spec/golden/ with fixed digests

## Command 3: Verify results
```bash
python scripts/thiele_verify.py spec/golden
```
Expected output for successful verification:
```
horn_small.json: mu 1.0
tseitin_small.json: mu 1.0
xor_small.json: mu 1.0
xor_small_orderA.json: mu 2.0
xor_small_orderB.json: mu 2.0
total mu 7.0
```