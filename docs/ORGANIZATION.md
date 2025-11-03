# Repository Organization Guide

This document explains the organization of The Thiele Machine repository following the Phase 2 reorganization (January 2025).

## Directory Structure

### Core Directories

```
The-Thiele-Machine/
├── thielecpu/              # Core Thiele CPU implementation (Python)
├── verifier/               # Receipt verification system
├── coq/                    # Formal Coq proofs
├── theory/                 # Theoretical foundations
├── spec/                   # Specifications (μ-spec, TRS, etc.)
├── tests/                  # Test suite
└── docs/                   # Documentation
```

### Demonstration Code

```
demos/
├── core-examples/          # Basic Thiele programs (hello, fizzbuzz, primes)
├── research-demos/         # Advanced research demonstrations
│   ├── partition/          # Graph partition and Tseitin examples
│   ├── oracles/            # Oracle demonstrations
│   ├── architecture/       # System architecture demos
│   ├── dialogue/           # Dialogue of the One
│   └── problem-solving/    # Problem-solving demonstrations
└── verification-demos/     # Verification and testing
    ├── bell-inequality/    # Bell inequality verification
    ├── riemann-hunt/       # Riemann hypothesis experiments
    └── adversarial/        # Adversarial testing
```

### Scripts and Utilities

```
scripts/
├── build/                  # Build and packaging scripts
├── maintenance/            # Repository maintenance utilities
├── experiments/            # Experiment runners
└── verification/           # Verification scripts
```

### v1.2 Roadmap Enhancements

```
roadmap-enhancements/
├── zk-proofs/              # Zero-knowledge proof infrastructure
├── trusting-trust/         # Compiler equivalence demo
├── supply-chain/           # SLSA/Rekor attestations
├── go-verifier/            # Go static verifier
├── binary-ingest/          # Binary→receipt conversion tool
├── delta-receipts/         # Delta receipt generation/replay
├── fuzzing/                # Fuzzing corpus and mutation tests
├── integrations/           # Package manager integrations
├── proofpacks/             # Research proofpacks
├── web-demos/              # Browser-based demonstrations
└── docs/                   # Enhancement documentation
```

### Data and Artifacts

```
artifacts/                  # Experiment artifacts and results
bootstrap_receipts/         # Bootstrap receipts for kernel
receipts/                   # Generated receipts
experiments/                # Experiment outputs
public_data/                # Public datasets
replication/                # Replication data
```

### Archive

```
archive/                    # Historical code and demonstrations
docs/archive/               # Archived documentation
├── results/                # Experimental result files
└── [various summaries]     # Historical summaries and manifestos
```

## File Organization Principles

### 1. Separation of Concerns

- **Core implementation** (`thielecpu/`, `verifier/`): Production code
- **Demonstrations** (`demos/`): Example programs and research demos
- **Scripts** (`scripts/`): Build, maintenance, and experiment utilities
- **Enhancements** (`roadmap-enhancements/`): Modular v1.2 additions
- **Documentation** (`docs/`, root): Essential and archived docs

### 2. Discoverability

- Core examples in `demos/core-examples/` for new users
- Research demos organized by topic
- Scripts categorized by function
- Clear README files in each directory

### 3. Historical Preservation

- Experimental results archived, not deleted (`docs/archive/results/`)
- Old summaries and manifestos preserved (`docs/archive/`)
- History maintained through `git mv` (not copy/delete)

### 4. Backward Compatibility

- Symlinks for critical scripts where needed
- Import paths updated throughout codebase
- CI/CD workflows updated with new paths

## Migration from Old Structure

### Root Directory Cleanup

**Before**: 100+ files in root (scripts, results, demos)
**After**: ~25 essential files (README, LICENSE, core docs)

Files moved:
- 14 Python scripts → `demos/` or `scripts/`
- 10 shell scripts → `scripts/`
- 20+ result markdown files → `docs/archive/results/`
- 17+ summary/manifesto files → `docs/archive/`

### Examples/Demos Consolidation

**Before**: Scattered across `examples/`, `demo/`, and root
**After**: Unified in `demos/` with clear categorization

- `examples/hello.thiele` → `demos/core-examples/hello.thiele`
- `examples/bell_inequality_demo.py` → `demos/verification-demos/bell-inequality/`
- `hunt_riemann.py` → `demos/verification-demos/riemann-hunt/`

### Scripts Reorganization

**Before**: Mixed in `scripts/`, `tools/`, and root
**After**: Categorized in `scripts/{build,maintenance,experiments,verification}/`

- `verify_bell.sh` → `scripts/verification/verify_bell.sh`
- `run_composition_experiments.py` → `scripts/experiments/`
- Build scripts → `scripts/build/`

## Finding Files

### Quick Reference

| Old Location | New Location | Notes |
|--------------|--------------|-------|
| `examples/*.thiele` | `demos/core-examples/` | Basic programs |
| `examples/*_demo.py` | `demos/{research,verification}-demos/` | Categorized |
| `hunt_riemann*.py` | `demos/verification-demos/riemann-hunt/` | Research demos |
| `verify_*.sh` | `scripts/verification/` | Verification scripts |
| `run_*_experiments.py` | `scripts/experiments/` | Experiment runners |
| `*_RESULTS.md` | `docs/archive/results/` | Archived |
| `*_SUMMARY.md` | `docs/archive/` | Archived |
| `zk/`, `demos/trusting-trust/` | `roadmap-enhancements/` | v1.2 enhancements |

### Search Tips

```bash
# Find a specific file
find . -name "filename"

# Find demonstrations
ls demos/*/

# Find scripts by category
ls scripts/*/

# Find archived results
ls docs/archive/results/
```

## Documentation Structure

### Active Documentation (Root)

Essential documentation remains in root for easy access:

- `README.md` - Main project README
- `CONTRIBUTING.md` - Contribution guidelines
- `SECURITY.md` - Security policy
- `CHANGELOG.md` - Version history
- `CITATION.cff` - Citation information
- `LICENSE` - Apache 2.0 license
- `REORGANIZATION.md` - v1.2 reorganization guide
- `docs/ORGANIZATION.md` - This file

### Archived Documentation

Historical and superseded documentation in `docs/archive/`:

- `results/` - Experimental result files
- `*_SUMMARY.md` - Project summaries and manifestos
- `*_README.md` - Superseded README files

### Enhancement Documentation

v1.2 roadmap documentation in `roadmap-enhancements/docs/`:

- Implementation guides
- Specifications
- Integration documentation
- See [`roadmap-enhancements/README.md`](../roadmap-enhancements/README.md)

## Best Practices

### Adding New Files

1. **Demonstrations**: Add to appropriate `demos/` subdirectory
2. **Scripts**: Categorize in `scripts/{build,maintenance,experiments,verification}/`
3. **Documentation**: Essential docs in root, detailed docs in `docs/`
4. **Enhancements**: New features go in `roadmap-enhancements/` or appropriate subdirectory

### Maintaining Organization

- Keep root directory minimal (essential files only)
- Archive old experimental results (don't delete)
- Update README files when adding new categories
- Use `git mv` to preserve history when relocating files

### Running Code

- Always use paths relative to repository root
- Update import statements when moving Python files
- Test scripts after moving to ensure paths are correct
- Maintain symlinks for frequently-used scripts

## See Also

- [`demos/README.md`](../demos/README.md) - Demonstration code guide
- [`scripts/README.md`](../scripts/README.md) - Scripts and utilities guide
- [`roadmap-enhancements/README.md`](../roadmap-enhancements/README.md) - v1.2 enhancements guide
- [`REORGANIZATION.md`](../REORGANIZATION.md) - v1.2 reorganization details
