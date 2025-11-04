# Offline Receipt Verification Demo

This directory contains a complete offline demonstration of receipt creation and verification. Everything works without internet access.

## Contents

- `sample_artifact.txt` - Example file to create receipt for
- `sample_artifact.receipt.json` - Pre-generated receipt
- `verify_offline.py` - Standalone verifier (no dependencies except Python stdlib)
- `README.md` - This file

## Quick Start

### Step 1: Verify the pre-generated receipt (offline)

```bash
python verify_offline.py sample_artifact.receipt.json sample_artifact.txt
```

**Expected output:**
```
✅ Receipt verification successful!
   Version: 1.0
   Files verified: 1
   Global digest matches: Yes
```

## License

This demo is part of The Thiele Machine project (Apache 2.0 license).

## Support

- **Documentation**: [Receipt Guide](../../docs/RECEIPT_GUIDE.md)
- **Issues**: [GitHub Issues](https://github.com/sethirus/The-Thiele-Machine/issues)
- **Spec**: [TRS-1.0](../../docs/trs-spec-v1.md)
