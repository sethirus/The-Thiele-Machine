# Roadmap Implementation Guide

This document tracks the implementation status of the 13-component roadmap for enhancing The Thiele Machine.

## Implementation Status

### ✅ A) Zero-Knowledge Receipt (ZK) Proofs

**Status**: Infrastructure Complete (Placeholder Proofs)

**Files**:
- `zk/guest/src/main.rs` - ZK guest program
- `zk/host/src/main.rs` - ZK prover CLI
- `zk/host/src/verify.rs` - ZK verifier CLI
- `thielecpu/zk_bridge.py` - Python integration
- `web/zk.html` - Browser verifier

**DoD Progress**:
- [x] ZK guest program structure
- [x] ZK host prover CLI (`zk-prove`)
- [x] ZK verifier CLI (`zk-verify`)
- [x] Python bridge (`thiele-proof prove/verify`)
- [x] Web verifier UI
- [ ] Real ZK backend (RISC Zero or SP1) integration
- [ ] Production cryptographic proofs

**Next Steps**: Integrate actual ZK VM (RISC Zero or SP1) for real cryptographic proofs

---

### ✅ B) Ken Thompson "Trusting-Trust" Demo

**Status**: Complete

**Files**:
- `demos/trusting-trust/toycc.c` - Minimal C compiler
- `demos/trusting-trust/Makefile` - Build automation
- `demos/trusting-trust/README.md` - Documentation

**DoD Progress**:
- [x] Toy compiler implementation
- [x] Build with GCC and Clang
- [x] Receipt generation for equivalence
- [x] Proofpack creation
- [x] Documentation walkthrough

**Ready**: ✅ Fully functional, ready for demo

---

### ✅ C) Supply-Chain Provenance (SLSA + in-toto + Sigstore/Rekor)

**Status**: Templates Complete

**Files**:
- `attestations/slsa-provenance.json` - SLSA template
- `tools/rekor_submit.py` - Rekor submission tool
- `attestations/README.md` - Documentation

**DoD Progress**:
- [x] SLSA provenance template
- [x] Rekor submission tool
- [x] Documentation
- [ ] CI workflow integration
- [ ] Real Sigstore/Rekor submissions

**Next Steps**: Integrate with GitHub Actions release workflow

---

### ✅ D) Go Static Verifier

**Status**: Core Implementation Complete

**Files**:
- `cmd/thiele-replay-go/main.go` - Main CLI
- `cmd/thiele-replay-go/internal/canonical/` - Canonical JSON
- `cmd/thiele-replay-go/internal/replay/` - Receipt replay
- `cmd/thiele-replay-go/README.md` - Documentation

**DoD Progress**:
- [x] Go verifier implementation
- [x] Canonical JSON verification
- [x] Static binary support
- [ ] CI integration
- [ ] Performance benchmarks

**Next Steps**: Add to CI matrix with Python and Shell verifiers

---

### ✅ E) "Any Binary → Receipt" Ingest

**Status**: Complete

**Files**:
- `tools/ingest_binary.py` - Ingestion tool

**DoD Progress**:
- [x] Binary/directory ingestion
- [x] Deterministic chunking
- [x] Ed25519 signing support
- [x] CLI with examples
- [x] Documentation

**Ready**: ✅ Fully functional

---

### ✅ F) Delta Receipts

**Status**: Specification Complete

**Files**:
- `docs/trs-delta-1.md` - Specification
- `thielecpu/delta.py` - Delta generation

**DoD Progress**:
- [x] Specification document
- [x] Delta generation tool
- [ ] Delta replay tool
- [ ] CI tests

**Next Steps**: Implement `replay_delta.py` and add tests

---

### ✅ G) WASM Execution Receipts

**Status**: Specification Complete

**Files**:
- `docs/wasm-receipts.md` - Specification

**DoD Progress**:
- [x] Specification document
- [ ] WASM runner implementation
- [ ] Deterministic VM setup
- [ ] Receipt emission

**Next Steps**: Implement `wasm/runner/` with Wasmtime

---

### ✅ H) µ-Ledger Integration

**Status**: Specification Complete

**Files**:
- `docs/mu-ledger-integration.md` - Specification

**DoD Progress**:
- [x] Specification document
- [ ] Receipt schema extension
- [ ] CLI tool integration
- [ ] Calibration data

**Next Steps**: Extend existing `mu.py` with receipt integration

---

### ✅ I) Browser Verifier Polish

**Status**: Plan Complete

**Files**:
- `docs/browser-verifier-enhancements.md` - Enhancement plan

**DoD Progress**:
- [x] Enhancement specification
- [ ] Web worker implementation
- [ ] Progress UI
- [ ] QR code support
- [ ] Mobile optimization

**Next Steps**: Implement web worker and chunked streaming

---

### ✅ J) Packaging Hooks

**Status**: Templates Complete

**Files**:
- `integrations/homebrew/Formula/thiele-replay.rb`
- `integrations/nix/flake.nix`
- `integrations/choco/thiele-replay.nuspec`
- `integrations/README.md`

**DoD Progress**:
- [x] Homebrew formula
- [x] Nix flake
- [x] Chocolatey package
- [ ] Published to registries
- [ ] CI automation

**Next Steps**: Publish to actual package registries

---

### ✅ K) Canonical Corpus & Red-Team Fuzz

**Status**: Corpus and Fuzzer Complete

**Files**:
- `tests/canonical/corpus/malformed_receipts.py` - Test corpus
- `fuzz/mutate_receipts.py` - Mutation fuzzer

**DoD Progress**:
- [x] Malformed receipt corpus
- [x] Mutation fuzzer
- [ ] CI integration
- [ ] Rejection rate dashboard

**Next Steps**: Add to CI with expected rejection rate

---

### ✅ L) Paper-Grade Proofpacks

**Status**: Templates Complete

**Files**:
- `proofpacks/README.md` - Documentation
- `proofpacks/dialogue/` - Dialogue proofpack template

**DoD Progress**:
- [x] Directory structure
- [x] Template Makefiles
- [x] Documentation
- [ ] Actual experiment data
- [ ] Verified digests

**Next Steps**: Populate with real experiment results

---

### ✅ M) DOI + Citation + Website

**Status**: Partial (CITATION.cff exists)

**Files**:
- `CITATION.cff` - Already exists in repo
- Zenodo integration needed
- GitHub Pages setup needed

**DoD Progress**:
- [x] CITATION.cff exists
- [ ] Zenodo DOI minting
- [ ] GitHub Pages deployment
- [ ] Website with demos

**Next Steps**: Create GitHub Pages site in `docs/` or via workflow

---

## Summary

| Component | Status | Priority | Complexity |
|-----------|--------|----------|------------|
| A - ZK Proofs | 🟡 Infra Ready | High | High |
| B - Trusting Trust | 🟢 Complete | Medium | Low |
| C - Supply Chain | 🟡 Templates Ready | High | Medium |
| D - Go Verifier | 🟡 Core Done | Medium | Low |
| E - Binary Ingest | 🟢 Complete | High | Low |
| F - Delta Receipts | 🟡 Spec Done | Medium | Medium |
| G - WASM Receipts | 🟡 Spec Done | Low | High |
| H - µ-Ledger | 🟡 Spec Done | Medium | Low |
| I - Browser Polish | 🟡 Plan Done | Medium | Medium |
| J - Packaging | 🟡 Templates Ready | Low | Low |
| K - Fuzzing | 🟡 Tools Ready | High | Low |
| L - Proofpacks | 🟡 Templates Ready | Medium | Low |
| M - DOI/Website | 🟡 Partial | Low | Low |

**Legend**:
- 🟢 Complete - Fully functional
- 🟡 Partial - Infrastructure/templates ready, needs implementation
- 🔴 Not Started

## Next Development Priorities

1. **Integrate ZK backend** (Component A) - Highest impact
2. **Add fuzzing to CI** (Component K) - Security critical
3. **Complete Go verifier CI** (Component D) - Easy win
4. **Delta replay implementation** (Component F) - High utility
5. **GitHub Pages deployment** (Component M) - Visibility

## Timeline Estimate

- **Week 1-2**: ZK backend integration (A)
- **Week 3**: CI enhancements (D, K)
- **Week 4**: Delta receipts (F)
- **Week 5**: Browser enhancements (I)
- **Week 6**: Packaging and deployment (J, M)
- **Ongoing**: Proofpack population (L)

## Contributing

See individual component README files for detailed implementation guides.
