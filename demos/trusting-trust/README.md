# Trusting Trust Demo

This directory demonstrates Ken Thompson's "Reflections on Trusting Trust" attack using receipts to prove compiler equivalence.

## Overview

The classic compiler trust problem: how do you know your compiler hasn't been backdoored? Even if you have the source code, the compiler that compiles it might be compromised.

**Receipts solve this**: By building the same compiler with two different toolchains and generating receipts for both builds, we can cryptographically prove that:

1. Both builds used the same source code
2. Both builds produced byte-identical binaries
3. No toolchain-specific backdoor was inserted

## Files

- `toycc.c` - A minimal C compiler (supports basic arithmetic, variables, if/while, print)
- `test_program.c` - A simple test program to compile
- `Makefile` - Automates the build and verification process

## Quick Start

Build the compiler with two different compilers and verify equivalence:

```bash
make clean
make proofpack
```

This will:
1. Build `toycc` with both `gcc` and `clang`
2. Generate receipts for both source and binaries
3. Create a proofpack proving byte-identical outputs
4. Verify the proofpack

## Manual Steps

### 1. Build with GCC

```bash
gcc -o toycc_gcc toycc.c
```

### 2. Build with Clang

```bash
clang -o toycc_clang toycc.c
```

### 3. Generate Receipts

```bash
# Receipt for source code
python3 ../../tools/ingest_binary.py toycc.c --out receipts/toycc_source.json

# Receipt for GCC build
python3 ../../tools/ingest_binary.py toycc_gcc --out receipts/toycc_gcc.json

# Receipt for Clang build
python3 ../../tools/ingest_binary.py toycc_clang --out receipts/toycc_clang.json
```

### 4. Verify Equivalence

```bash
# Extract SHA256 from receipts
GCC_SHA=$(jq -r '.global_digest' receipts/toycc_gcc.json)
CLANG_SHA=$(jq -r '.global_digest' receipts/toycc_clang.json)

# Compare
if [ "$GCC_SHA" = "$CLANG_SHA" ]; then
    echo "✓ Compilers produced identical binaries!"
    echo "  SHA256: $GCC_SHA"
else
    echo "✗ Binaries differ (possible backdoor!)"
    echo "  GCC:   $GCC_SHA"
    echo "  Clang: $CLANG_SHA"
fi
```

## Expected Output

When both compilers are clean, you should see:

```
✓ Compilers produced identical binaries!
  SHA256: 45bc9110a8d95e9b7e8c7f3d2e1a6b9c...
```

This proves that:
- The source code was the same (verified by source receipt)
- Both toolchains processed it identically
- No compiler-specific backdoor was inserted

## The Attack Scenario

If one compiler were backdoored (e.g., it inserts a trojan when compiling compilers), the receipts would show:

```
✗ Binaries differ (possible backdoor!)
  GCC:   45bc9110a8d95e9b7e8c7f3d2e1a6b9c...
  Clang: 9f7e3d2a1c8b6e5f4d3c2b1a09876543...
```

This difference is cryptographic proof of tampering.

## Why This Matters

1. **Bootstrapping Trust**: You can build compilers from different "trust roots" and prove equivalence
2. **Supply Chain Security**: Detects compromised build tools
3. **Reproducible Builds**: Proves builds are deterministic
4. **Audit Trail**: Receipts provide cryptographic evidence

## Testing the Toy Compiler

```bash
# Create a test program
echo 'a = 5; b = 10; c = a + b; print(c);' > test.toy

# Compile with GCC-built compiler
./toycc_gcc test.toy test_gcc.c
gcc test_gcc.c -o test_gcc
./test_gcc  # Should print: 15

# Compile with Clang-built compiler
./toycc_clang test.toy test_clang.c  
gcc test_clang.c -o test_clang
./test_clang  # Should print: 15

# The generated C code should be identical
diff test_gcc.c test_clang.c
```

## Proofpack Contents

The `trusting-trust.proofpack.zst` contains:

- Source code receipt (`toycc_source.json`)
- GCC build receipt (`toycc_gcc.json`)
- Clang build receipt (`toycc_clang.json`)
- Equivalence verification script
- This README

To verify:

```bash
# Extract proofpack
zstd -d trusting-trust.proofpack.zst

# Verify all receipts
python3 ../../verifier/replay.py trusting-trust/receipts/

# Check equivalence
./trusting-trust/verify_equivalence.sh
```

## References

- [Reflections on Trusting Trust](https://www.cs.cmu.edu/~rdriley/487/papers/Thompson_1984_ReflectionsonTrustingTrust.pdf) - Ken Thompson's original paper
- [Diverse Double-Compiling](https://dwheeler.com/trusting-trust/) - DDC technique for defeating the attack
- [Reproducible Builds](https://reproducible-builds.org/) - Industry effort for deterministic builds
