# Software Bill of Materials (SBOM)

## Self-Hosting Thiele Kernel System

**Version**: 1.0  
**Date**: 2025-11-02  
**License**: Apache-2.0

## Core Components

### Verifier (Trusted Computing Base)
- **File**: `verifier/replay.py`
- **Size**: ~160 LoC (excluding comments/blanks)
- **Purpose**: Receipt verification and kernel reconstruction
- **Dependencies**: Python 3.11+ standard library only (hashlib, json, os, sys, pathlib)

### Receipts
- **Directory**: `bootstrap_receipts/`
- **Files**:
  - `050_kernel_emit.json` (7 steps, kernel reconstruction)
- **Format**: TRS-0 (Thiele Receipt Schema version 0)
- **Total size**: ~57 KB

### Documentation
- **File**: `docs/receipt_schema.md`
- **Purpose**: TRS-0 specification
- **Size**: ~7 KB

### Tools (Development Only)
- `tools/canonical_json.py` - JSON canonicalization (self-contained)
- `tools/make_bootstrap_receipts.py` - Receipt generator (dev-time only)
- `tools/prove_integrity.py` - Integrity verification script

### Tests
- `tests/test_end_to_end.sh` - End-to-end reconstruction test
- `tests/expected_kernel_sha256.txt` - Hash pinning

### Artifacts (Not Distributed in Repository)
- `thiele_min.py` - Reconstructed kernel (8348 bytes)
  - Generated from receipts
  - Not committed to repository
  - SHA256: `77cd06bbb84ed8ccc4fd2949c555a8ba553d56629c88338435db65ce4d079135`

- `kernel_template/thiele_min.py` - Development template
  - Used only to generate receipts
  - Not distributed
  - Excluded via `.gitignore`

## Dependencies

### Runtime Dependencies
**None** - The verifier and receipts are self-contained.

### Development Dependencies (Optional)
- Python 3.11+ (required)
- pytest (for running tests, optional)
- Git (for version control)

## Security Notes

1. **Minimal TCB**: Trust required only for ~160 LoC verifier
2. **No external dependencies**: Pure Python stdlib
3. **Cryptographic verification**: All state transitions hash-verified
4. **Deterministic**: Same receipts → identical output

## File Inventory

```
The-Thiele-Machine/
├── verifier/
│   └── replay.py                    [TCB: 160 LoC]
├── bootstrap_receipts/
│   └── 050_kernel_emit.json         [Receipts: 57 KB]
├── docs/
│   └── receipt_schema.md            [Spec: 7 KB]
├── tests/
│   ├── test_end_to_end.sh          [Test script]
│   └── expected_kernel_sha256.txt   [Hash pin]
├── tools/
│   ├── canonical_json.py            [Tool: JSON canon]
│   ├── make_bootstrap_receipts.py   [Tool: generator]
│   └── prove_integrity.py           [Tool: verification]
├── checksums/
│   └── receipts_sha256.txt          [Receipt checksums]
├── attestations/
│   ├── SBOM.md                      [This file]
│   └── REPRODUCIBILITY.md           [Repro guide]
├── examples/
│   └── hello.thiele                 [Example program]
├── .gitignore                       [Excludes: kernel, template]
├── .github/workflows/ci.yml         [CI config]
├── README.md                        [Main docs]
└── LICENSE                          [Apache-2.0]
```

## Checksums

### Receipt Files
```
219ee502d24c43e55bbb3734404cec7b7903b94d33d2d8e7b27413f6ceb3df8d  bootstrap_receipts/050_kernel_emit.json
```

### Expected Kernel
```
77cd06bbb84ed8ccc4fd2949c555a8ba553d56629c88338435db65ce4d079135  thiele_min.py
```

## Verification

To verify this SBOM:

```bash
# Verify receipt checksums
sha256sum -c checksums/receipts_sha256.txt

# Reconstruct and verify kernel
python3 verifier/replay.py bootstrap_receipts
sha256sum thiele_min.py  # Should match expected hash above

# Run integrity proof
python3 tools/prove_integrity.py
```

## Provenance

All receipts were generated from the kernel template using deterministic tooling. The generation process is documented in `tools/make_bootstrap_receipts.py` and can be reproduced (though not required for verification).

## Contact

For security concerns or vulnerability reports, see SECURITY.md in the repository root.
