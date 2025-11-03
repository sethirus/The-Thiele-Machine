# Reproducibility Guide

## Overview

This document describes how to reproduce the Thiele minimal kernel (`thiele_min.py`) from cryptographic receipts on any system with Python 3.11+.

## Prerequisites

- Python 3.11 or later
- Git (for cloning the repository)
- Standard Unix tools: `sha256sum` or equivalent

## Step-by-Step Instructions

### 1. Clone the Repository

```bash
git clone https://github.com/sethirus/The-Thiele-Machine.git
cd The-Thiele-Machine
```

### 2. Verify Initial State

The repository should NOT contain `thiele_min.py`. Verify:

```bash
ls -la thiele_min.py
# Should output: No such file or directory
```

### 3. Reconstruct the Kernel

Run the receipt replay verifier:

```bash
python3 verifier/replay.py bootstrap_receipts
```

Expected output:
```
Materialized: thiele_min.py (8348 bytes, sha256=77cd06bbb84ed8ccc4fd2949c555a8ba553d56629c88338435db65ce4d079135)
Receipt verification complete. All invariants satisfied.
```

### 4. Verify the Kernel Hash

```bash
sha256sum thiele_min.py
```

Expected output:
```
77cd06bbb84ed8ccc4fd2949c555a8ba553d56629c88338435db65ce4d079135  thiele_min.py
```

This hash MUST match the value in `tests/expected_kernel_sha256.txt`:

```bash
cat tests/expected_kernel_sha256.txt
```

### 5. Test Kernel Self-Verification

The reconstructed kernel can verify its own construction:

```bash
python3 thiele_min.py --verify bootstrap_receipts/050_kernel_emit.json
```

Expected output:
```
Receipt verification OK
Global digest: 45bc91102be2a30e3d8f851c375809f5640bed1a180f0597f559d3bb927ef1f7
```

### 6. Run Complete Integrity Proof

For a comprehensive verification:

```bash
python3 tools/prove_integrity.py
```

## One-Command Verification

```bash
python3 verifier/replay.py bootstrap_receipts && sha256sum thiele_min.py
```

## Platform-Specific Notes

### Windows

Use `certutil` instead of `sha256sum`:

```powershell
python verifier/replay.py bootstrap_receipts
certutil -hashfile thiele_min.py SHA256
```

### macOS

Use `shasum`:

```bash
python3 verifier/replay.py bootstrap_receipts && shasum -a 256 thiele_min.py
```

## Reproducibility Guarantees

1. **Deterministic**: Same receipts always produce identical output
2. **Platform-independent**: Works on Linux, macOS, Windows
3. **Cryptographically verified**: Every byte justified by hash chain
4. **Minimal TCB**: Trust only ~160 LoC of verifier code

## Troubleshooting

### Problem: "No such file or directory: bootstrap_receipts"

Ensure you're in the repository root directory.

### Problem: Hash mismatch

1. Verify you're using the correct branch/commit
2. Check that receipt files haven't been modified
3. Compare with `checksums/receipts_sha256.txt`

### Problem: Python version too old

Upgrade to Python 3.11+:

```bash
python3 --version  # Should be >= 3.11
```

## Verification Checklist

- [ ] Repository cloned successfully
- [ ] No pre-existing `thiele_min.py`
- [ ] Receipt replay completed without errors
- [ ] Kernel hash matches expected value
- [ ] Kernel self-verification passes
- [ ] Integrity proof script confirms all checks

## Receipt Details

- **Total receipts**: 1 file (`050_kernel_emit.json`)
- **Total steps**: 7
- **Global digest**: `45bc91102be2a30e3d8f851c375809f5640bed1a180f0597f559d3bb927ef1f7`
- **Kernel size**: 8348 bytes
- **Kernel hash**: `77cd06bbb84ed8ccc4fd2949c555a8ba553d56629c88338435db65ce4d079135`

## Support

For issues with reproduction, see the main README or open an issue on GitHub.
