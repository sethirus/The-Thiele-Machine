# Repository Reorganization (2025-11-03)

This document describes the repository reorganization that moved all v1.2 roadmap enhancement components into a dedicated `roadmap-enhancements/` directory.

## What Changed

All files added as part of the v1.2 milestone roadmap have been reorganized into a structured directory:

```
roadmap-enhancements/
├── zk-proofs/              # Zero-knowledge receipt proofs (Component A)
├── trusting-trust/         # Compiler equivalence demo (Component B)
├── supply-chain/           # SLSA/Rekor attestations (Component C)
├── go-verifier/            # Go static verifier (Component D)
├── binary-ingest/          # Binary→receipt tool (Component E)
├── delta-receipts/         # Delta receipts (Component F)
├── fuzzing/                # Fuzzing corpus (Component K)
├── integrations/           # Package managers (Component J)
├── proofpacks/             # Research proofpacks (Component L)
├── web-demos/              # Browser demos
└── docs/                   # Enhancement documentation
```

## File Mapping

### Old Location → New Location

| Old Path | New Path |
|----------|----------|
| `zk/` | `roadmap-enhancements/zk-proofs/zk/` |
| `thielecpu/zk_bridge.py` | `roadmap-enhancements/zk-proofs/zk_bridge.py` |
| `web/zk.html` | `roadmap-enhancements/zk-proofs/web/zk.html` |
| `demos/trusting-trust/` | `roadmap-enhancements/trusting-trust/demo/` |
| `web/trusting-trust.html` | `roadmap-enhancements/trusting-trust/web/trusting-trust.html` |
| `attestations/` | `roadmap-enhancements/supply-chain/attestations/` |
| `tools/rekor_submit.py` | `roadmap-enhancements/supply-chain/tools/rekor_submit.py` |
| `cmd/thiele-replay-go/` | `roadmap-enhancements/go-verifier/thiele-replay-go/` |
| `tools/ingest_binary.py` | `roadmap-enhancements/binary-ingest/ingest_binary.py` |
| `thielecpu/delta.py` | `roadmap-enhancements/delta-receipts/delta.py` |
| `verifier/replay_delta.py` | `roadmap-enhancements/delta-receipts/replay_delta.py` |
| `fuzz/` | `roadmap-enhancements/fuzzing/fuzz/` |
| `tests/canonical/corpus/malformed_receipts.py` | `roadmap-enhancements/fuzzing/corpus/malformed_receipts.py` |
| `integrations/` | `roadmap-enhancements/integrations/` |
| `proofpacks/` | `roadmap-enhancements/proofpacks/` |
| `web/install.html` | `roadmap-enhancements/web-demos/install.html` |
| `web/install.js` | `roadmap-enhancements/web-demos/install.js` |
| `docs/ROADMAP.md` | `roadmap-enhancements/docs/ROADMAP.md` |
| `docs/ENHANCEMENTS_INDEX.md` | `roadmap-enhancements/docs/ENHANCEMENTS_INDEX.md` |
| `docs/zk-backend-integration.md` | `roadmap-enhancements/docs/zk-backend-integration.md` |
| `docs/publishing-guide.md` | `roadmap-enhancements/docs/publishing-guide.md` |
| `docs/ingest.md` | `roadmap-enhancements/docs/ingest.md` |
| `docs/trs-delta-1.md` | `roadmap-enhancements/docs/trs-delta-1.md` |
| `docs/wasm-receipts.md` | `roadmap-enhancements/docs/wasm-receipts.md` |
| `docs/mu-ledger-integration.md` | `roadmap-enhancements/docs/mu-ledger-integration.md` |
| `docs/browser-verifier-enhancements.md` | `roadmap-enhancements/docs/browser-verifier-enhancements.md` |
| `docs/pitch.md` | `roadmap-enhancements/docs/pitch.md` |

## Backward Compatibility

Symlinks have been created for Python modules to maintain backward compatibility with existing imports:

- `tools/ingest_binary.py` → `roadmap-enhancements/binary-ingest/ingest_binary.py`
- `thielecpu/delta.py` → `roadmap-enhancements/delta-receipts/delta.py`
- `verifier/replay_delta.py` → `roadmap-enhancements/delta-receipts/replay_delta.py`

This ensures that:
1. PyPI package entry points still work (`thiele-ingest`, `thiele-delta`)
2. Existing imports don't break
3. CI workflows continue to function

## What Wasn't Moved

The following were intentionally **NOT** moved to avoid breaking the core repository:

- `thielecpu/` (core Thiele CPU implementation)
- `verifier/` (core verifier - only `replay_delta.py` was moved)
- `theory/` (theoretical foundations)
- `coq/` (formal proofs)
- `tests/` (test infrastructure)
- `experiments/` (experimental data)
- `tools/` (utility tools - only specific roadmap tools were moved)

## Updated References

The following files were updated to reflect the new paths:

### CI/CD Workflows

- `.github/workflows/ci.yml`
  - Fuzzer path: `roadmap-enhancements/fuzzing/fuzz/mutate_receipts.py`
  
- `.github/workflows/release.yml`
  - Binary ingest: `roadmap-enhancements/binary-ingest/ingest_binary.py`
  - Rekor submit: `roadmap-enhancements/supply-chain/tools/rekor_submit.py`
  - Go verifier: `roadmap-enhancements/go-verifier/thiele-replay-go/`
  - Attestations: `roadmap-enhancements/supply-chain/attestations/`

- `.github/workflows/publish.yml`
  - Homebrew formula: `roadmap-enhancements/integrations/homebrew/Formula/thiele-replay.rb`

### Tests

- `tests/test_fuzz_receipts.py`
  - Import path updated to use `roadmap-enhancements/fuzzing/corpus/`

### Documentation

- `README.md`
  - Demo links updated to point to `roadmap-enhancements/web-demos/` and `roadmap-enhancements/*/web/`
  - Added reorganization notice

## Migration Guide for External Users

If you have scripts or tools that reference the old paths:

### Option 1: Use New Paths (Recommended)

Update your scripts to use the new paths:

```bash
# Old
python3 tools/ingest_binary.py ...

# New
python3 roadmap-enhancements/binary-ingest/ingest_binary.py ...
```

### Option 2: Use Symlinks (Temporary)

The symlinks will work for now, but update to new paths when convenient:

```bash
# Works via symlink (but update eventually)
python3 tools/ingest_binary.py ...
```

### Option 3: Use CLI Tools (Best for End Users)

Once published to PyPI, use the CLI tools:

```bash
# Install package
pip install thiele-replay

# Use CLI commands (paths abstracted)
thiele-ingest ...
thiele-delta ...
```

## Why This Change?

The reorganization addresses several issues:

1. **Clutter**: Root directory had become cluttered with diverse components
2. **Discoverability**: Hard to understand what's new vs. core functionality
3. **Modularity**: Components should be self-contained and independently documentable
4. **Separation of Concerns**: Clear boundary between core implementation and enhancements
5. **Future Scalability**: Easy to add more roadmap components without further clutter

## Getting Help

- See [roadmap-enhancements/README.md](roadmap-enhancements/README.md) for comprehensive component guide
- Each component has its own README with usage instructions
- File issues on GitHub if you encounter migration problems

## Rollback Plan

If needed, the reorganization can be rolled back using:

```bash
# WARNING: This is destructive and should only be done if absolutely necessary
git revert <commit-hash>
```

However, all workflows have been tested and symlinks ensure backward compatibility, so rollback should not be necessary.
