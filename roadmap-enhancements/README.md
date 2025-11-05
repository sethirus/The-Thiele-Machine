# Roadmap Enhancements (v1.2)

This directory contains all the enhancements implemented as part of the v1.2 milestone roadmap. Each component is self-contained with its own documentation and tooling.

## 📁 Directory Structure

```
roadmap-enhancements/
├── zk-proofs/              # Component A: Zero-Knowledge Receipt Proofs
├── trusting-trust/         # Component B: Ken Thompson "Trusting Trust" Demo
├── supply-chain/           # Component C: SLSA/in-toto/Sigstore Provenance
├── go-verifier/            # Component D: Go Static Verifier
├── binary-ingest/          # Component E: Binary→Receipt Ingest Tool
├── delta-receipts/         # Component F: Delta Receipts
├── fuzzing/                # Component K: Fuzzing & Red-team Corpus
├── integrations/           # Component J: Package Manager Hooks
├── proofpacks/             # Component L: Paper-grade Proofpacks
├── web-demos/              # Browser Demos (Proof-Install, etc.)
└── docs/                   # Documentation for all components
```

## 🎯 Components

### A) Zero-Knowledge Proofs (`zk-proofs/`)

Cryptographic proof generation and verification without replay.

**Key Files**:
- `zk/guest/` - RISC Zero/SP1 guest program
- `zk/host/` - Prover and verifier CLI tools
- `zk_bridge.py` - Python integration
- `web/zk.html` - Browser ZK verifier

**Usage**:
```bash
cd zk-proofs/zk/host
cargo build --release
./target/release/zk-prove --receipt receipt.json --out zkproof.json
./target/release/zk-verify zkproof.json
```

**Status**: ✅ Infrastructure complete, needs real ZK backend (see `docs/zk-backend-integration.md`)

---

### B) Trusting Trust Demo (`trusting-trust/`)

Demonstrates compiler equivalence proof via receipts.

**Key Files**:
- `demo/toycc.c` - Minimal C compiler
- `demo/Makefile` - Build automation
- `web/trusting-trust.html` - Browser demo

**Usage**:
```bash
cd trusting-trust/demo
make proofpack  # Build with GCC & Clang
make verify     # Prove byte-identical outputs
```

**Status**: ✅ Complete and working

---

### C) Supply-Chain Provenance (`supply-chain/`)

Industry-standard attestations (SLSA v1, Rekor transparency log).

**Key Files**:
- `attestations/slsa-provenance.json` - SLSA v1 template
- `tools/rekor_submit.py` - Rekor submission tool

**Usage**:
```bash
python3 supply-chain/tools/rekor_submit.py receipt.json zkproof.json
```

**Status**: ✅ Templates ready for CI integration

---

### D) Go Static Verifier (`go-verifier/`)

Third independent verifier implementation (Python, Shell, **Go**).

**Key Files**:
- `thiele-replay-go/main.go` - Main verifier
- `thiele-replay-go/internal/canonical/` - Canonical JSON
- `thiele-replay-go/internal/replay/` - Replay logic

**Usage**:
```bash
cd go-verifier/thiele-replay-go
CGO_ENABLED=0 go build -trimpath -ldflags="-s -w"
./thiele-replay-go ../../bootstrap_receipts/050_kernel_emit.json --print-digest
```

**Status**: ✅ Complete, ready for CI integration

---

### E) Binary Ingest (`binary-ingest/`)

Convert any binary/directory to TRS-0 receipts.

**Key Files**:
- `ingest_binary.py` - Main ingestion tool

**Usage**:
```bash
python3 binary-ingest/ingest_binary.py /usr/bin/busybox --out busybox.receipt.json
python3 verifier/replay.py busybox.receipt.json --verify
```

**Status**: ✅ Production ready

---

### F) Delta Receipts (`delta-receipts/`)

Efficient updates via chunk-level diffs.

**Key Files**:
- `delta.py` - Delta generation
- `replay_delta.py` - Delta application

**Usage**:
```bash
# Generate delta
python3 delta-receipts/delta.py --base v1.json --new v2.json --out delta.json

# Apply delta
python3 delta-receipts/replay_delta.py --base v1.json --delta delta.json --verify
```

**Status**: ✅ End-to-end implementation complete

---

### J) Package Manager Integrations (`integrations/`)

Homebrew, Nix, Chocolatey package definitions.

**Key Files**:
- `homebrew/Formula/thiele-replay.rb` - Homebrew formula
- `nix/flake.nix` - Nix flake
- `choco/thiele-replay.nuspec` - Chocolatey package

**Status**: ✅ Templates ready for publication

---

### K) Fuzzing & Red-Team Corpus (`fuzzing/`)

Security testing with malformed receipts.

**Key Files**:
- `fuzz/mutate_receipts.py` - Mutation fuzzer
- `corpus/malformed_receipts.py` - Test corpus

**Usage**:
```bash
python3 fuzzing/fuzz/mutate_receipts.py receipt.json --count 100 --out-dir /tmp/fuzz
```

**Status**: ✅ Integrated into CI (100% rejection rate enforced)

---

### L) Proofpacks (`proofpacks/`)

Reproducible research artifacts.

**Key Files**:
- `dialogue/` - Example proofpack with Makefile

**Status**: ✅ Templates ready

---

### Browser Demos (`web-demos/`)

Client-side verification demos.

**Key Files**:
- `install.html` + `install.js` - Proof-Install (4-step workflow)
- (See also `zk-proofs/web/zk.html` and `trusting-trust/web/trusting-trust.html`)

**Usage**:
```bash
python3 -m http.server -d roadmap-enhancements/web-demos 8080
# Open http://localhost:8080/install.html
```

**Status**: ✅ Production ready, 100% offline

---

## 📖 Documentation (`docs/`)

Complete documentation for all components:

- **ROADMAP.md** - Implementation tracker
- **ENHANCEMENTS_INDEX.md** - Quick reference
- **zk-backend-integration.md** - RISC Zero/SP1 integration guide
- **publishing-guide.md** - PyPI/Homebrew publishing
- **ingest.md** - Binary ingestion guide
- **trs-delta-1.md** - Delta receipt specification
- **wasm-receipts.md** - WASM execution spec
- **mu-ledger-integration.md** - µ-ledger integration
- **browser-verifier-enhancements.md** - Web UI improvements
- **pitch.md** - Plain-English project pitch

---

## 🚀 Quick Start

### Try the Browser Demos

1. **Proof-Install**: `web-demos/install.html`
2. **Trusting Trust**: `trusting-trust/web/trusting-trust.html`
3. **ZK Verify**: `zk-proofs/web/zk.html`

All work 100% offline with zero dependencies.

### Install CLI Tools (After PyPI Publication)

```bash
pip install thiele-replay
thiele-replay     # Verify receipts
thiele-ingest     # Binary→receipt conversion
thiele-delta      # Delta generation
```

### Build Go Verifier

```bash
cd go-verifier/thiele-replay-go
go build
./thiele-replay-go --help
```

---

## 📊 Status Summary

| Component | Status | Files | Priority |
|-----------|--------|-------|----------|
| A - ZK Proofs | 🟡 Infra ready | 5 | High |
| B - Trusting Trust | 🟢 Complete | 5 | Medium |
| C - Supply Chain | 🟡 Templates | 3 | High |
| D - Go Verifier | 🟢 Complete | 5 | Medium |
| E - Binary Ingest | 🟢 Complete | 1 | High |
| F - Delta Receipts | 🟢 Complete | 2 | Medium |
| G - WASM Receipts | 🟡 Spec only | 1 | Low |
| H - µ-Ledger | 🟡 Spec only | 1 | Medium |
| I - Browser Polish | 🟡 Plan ready | 1 | Medium |
| J - Integrations | 🟡 Templates | 4 | Low |
| K - Fuzzing | 🟢 Complete | 3 | High |
| L - Proofpacks | 🟡 Templates | 2 | Medium |
| M - DOI/Website | 🟡 Partial | 1 | Low |

🟢 Complete (5) | 🟡 Partial (8) | Total: 13 components

---

## 🔗 Links to Main Repository

- **Core Verifier**: `../../verifier/`
- **Thiele CPU**: `../../thielecpu/`
- **Tests**: `../../tests/`
- **CI Workflows**: `../../.github/workflows/`
- **Main README**: `../../README.md`

---

## 📝 Notes

This reorganization (completed 2025-11-03) moved all v1.2 roadmap components into this dedicated directory to:
- Reduce repository clutter
- Improve discoverability
- Enable modular development
- Maintain clear separation between core and enhancements

All paths in workflows, imports, and documentation have been updated accordingly.
