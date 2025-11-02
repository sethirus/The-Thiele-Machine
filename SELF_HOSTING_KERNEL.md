# Self-Hosting Thiele Kernel

## Overview

This directory contains a **self-hosting kernel system** where the Thiele minimal kernel (`thiele_min.py`) is distributed as cryptographically verifiable receipts rather than source code.

## The "System = Proof" Paradigm

Traditional software distribution:
- Trust source code
- Compile/install
- Hope for the best

Self-hosting Thiele:
- Trust cryptographic receipts (hash-chained proof of construction)
- Verify with minimal TCB (~160 LoC verifier)
- Reconstruct kernel deterministically
- Kernel can verify its own construction

## Quick Start

```bash
# One command to reconstruct the kernel
python3 verifier/replay.py bootstrap_receipts && sha256sum thiele_min.py

# Expected output:
# Materialized: thiele_min.py (8348 bytes, sha256=77cd06bbb84ed8ccc4fd2949c555a8ba553d56629c88338435db65ce4d079135)
# Receipt verification complete. All invariants satisfied.
```

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     Bootstrap Receipts                       │
│  (Cryptographic proof of kernel construction)               │
│  • 050_kernel_emit.json (7 steps, 8348 bytes)              │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│                    Receipt Verifier                          │
│  • verifier/replay.py (~160 LoC, Trusted Computing Base)    │
│  • Validates state transitions                              │
│  • Reconstructs kernel byte-by-byte                         │
│  • No external dependencies                                 │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│                  Thiele Minimal Kernel                       │
│  • thiele_min.py (8348 bytes, reconstructed)                │
│  • Bytecode interpreter                                     │
│  • Receipt verifier (self-verification capability)          │
│  • NOT in repository (generated from receipts)              │
└─────────────────────────────────────────────────────────────┘
```

## File Structure

```
.
├── verifier/
│   └── replay.py                    # TCB: Receipt verifier (160 LoC)
├── bootstrap_receipts/
│   └── 050_kernel_emit.json         # Kernel construction receipts
├── docs/
│   └── receipt_schema.md            # TRS-0 specification
├── tools/
│   ├── canonical_json.py            # JSON canonicalization
│   ├── make_bootstrap_receipts.py   # Receipt generator (dev only)
│   └── prove_integrity.py           # Integrity verification
├── tests/
│   ├── test_end_to_end.sh          # E2E test script
│   └── expected_kernel_sha256.txt   # Hash pinning
├── checksums/
│   └── receipts_sha256.txt          # Receipt checksums
├── attestations/
│   ├── SBOM.md                      # Software Bill of Materials
│   └── REPRODUCIBILITY.md           # Reproduction guide
└── examples/
    └── hello.thiele                 # Example program
```

## Security Properties

1. **Minimal TCB**: ~160 LoC verifier vs thousands of LoC in kernel
2. **Cryptographic verification**: Every byte justified by hash chains
3. **Deterministic**: Same receipts → identical kernel
4. **Self-verification**: Kernel can verify its own construction
5. **No dependencies**: Pure Python stdlib
6. **Path validation**: No traversal, no absolute paths
7. **Monotone offsets**: Write order enforced
8. **State integrity**: Pre/post hash verification at every step

## Receipt Schema (TRS-0)

Receipts use the Thiele Receipt Schema version 0 (TRS-0):

- **Top-level**: version, steps, global_digest, sig_scheme, signature
- **Steps**: pre_state_sha256, opcode, args, axioms, oracle_reply, mu_bits, post_state_sha256
- **Opcodes**: EMIT_BYTES, MAKE_EXEC, ASSERT_SHA256
- **Global digest**: SHA256 of concatenated step hashes

See `docs/receipt_schema.md` for complete specification.

## Verification Workflow

1. **Load receipts** from `bootstrap_receipts/`
2. **For each step**:
   - Verify pre-state hash matches current state
   - Execute opcode (EMIT_BYTES, MAKE_EXEC, or ASSERT_SHA256)
   - Recompute state hash
   - Verify post-state hash matches
3. **Materialize** virtual filesystem to disk
4. **Set permissions** (executable bit for flagged files)

## Testing

```bash
# End-to-end test
bash tests/test_end_to_end.sh

# Integrity proof
python3 tools/prove_integrity.py

# Kernel self-verification
python3 thiele_min.py --verify bootstrap_receipts/050_kernel_emit.json

# Verify receipt checksums
sha256sum -c checksums/receipts_sha256.txt
```

## Development Workflow

### Modifying the Kernel

1. Edit `kernel_template/thiele_min.py` (not in repository)
2. Regenerate receipts:
   ```bash
   python3 tools/make_bootstrap_receipts.py kernel_template/thiele_min.py
   ```
3. Test reconstruction:
   ```bash
   rm -f thiele_min.py
   python3 verifier/replay.py bootstrap_receipts
   bash tests/test_end_to_end.sh
   ```
4. Commit updated receipts and expected hash

### Adding New Features

The system is designed to be extended:

- **New opcodes**: Add to verifier and receipt generator
- **Signature verification**: See Phase 10 (optional)
- **Alternative verifiers**: Go, shell, etc. (Phase 9)
- **Size enforcement**: CI checks for TCB size (Phase 18)

## Hashes & Checksums

### Expected Kernel
```
77cd06bbb84ed8ccc4fd2949c555a8ba553d56629c88338435db65ce4d079135  thiele_min.py
```

### Receipt File
```
219ee502d24c43e55bbb3734404cec7b7903b94d33d2d8e7b27413f6ceb3df8d  bootstrap_receipts/050_kernel_emit.json
```

### Global Digest
```
45bc91102be2a30e3d8f851c375809f5640bed1a180f0597f559d3bb927ef1f7
```

## References

- **Receipt Schema**: `docs/receipt_schema.md`
- **SBOM**: `attestations/SBOM.md`
- **Reproducibility**: `attestations/REPRODUCIBILITY.md`
- **Main README**: See "Self-Hosting Thiele Kernel" section

## FAQ

**Q: Why distribute receipts instead of source?**  
A: Much smaller trusted computing base. You only need to trust ~160 LoC of verifier instead of ~8000 bytes of kernel code.

**Q: Can I inspect the kernel source?**  
A: Yes! After reconstruction: `cat thiele_min.py`. Every byte is cryptographically justified.

**Q: Is this really deterministic?**  
A: Yes. Same receipts on any platform produce identical kernel (bit-for-bit).

**Q: What if receipts are tampered?**  
A: Hash verification fails immediately. Global digest provides tamper-evidence.

**Q: Can the kernel verify itself?**  
A: Yes! `python3 thiele_min.py --verify bootstrap_receipts/050_kernel_emit.json`

**Q: What about updates?**  
A: Generate new receipts, update expected hash, commit. Old receipts remain verifiable.

## License

Apache-2.0 (same as main repository)

---

**Status**: Phases 0-8, 11, 13-15, 20 complete. System is fully functional.
