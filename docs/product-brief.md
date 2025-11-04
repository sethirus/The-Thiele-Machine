# Thiele Receipt System - Product Brief

## Executive Summary

The Thiele Receipt System transforms software distribution from a trust-based model to a proof-based model. Instead of asking users to trust that a binary matches its source code, we provide cryptographic receipts that mathematically prove how software was constructed.

**Core Promise:** *Install software from a proof you can replay, not just from a signed blob.*

## Target Audience

### Primary Users

1. **OSS Maintainers & Developers**
   - Want to distribute software with cryptographic guarantees
   - Need to prove their builds are reproducible and tamper-free
   - Value transparency and verifiability over "just trust me"

2. **Security-Sensitive Organizations**
   - Banks, healthcare, government, critical infrastructure
   - Required to verify software supply chain integrity
   - Need audit trails for compliance (SOC2, FedRAMP, etc.)
   - Want protection against supply chain attacks

3. **Package Consumers & End Users**
   - Want to verify software before running it
   - Don't want to trust build servers or download channels
   - Need protection against backdoored compilers and toolchains
   - Value privacy (verification happens locally, not via external services)

### Secondary Users

4. **Researchers & Academics**
   - Need reproducible computational results
   - Want cryptographic audit trails for experiments
   - Value deterministic replay capabilities

5. **DevOps & CI/CD Teams**
   - Need to integrate verification into existing pipelines
   - Want automated receipt generation in build processes
   - Value minimal friction adoption paths

## Core Value Propositions

### For Developers
- **Zero-Trust Distribution**: Ship receipts instead of asking users to trust your binaries
- **Compiler Equivalence**: Defeat "Trusting Trust" attacks by proving compiler output
- **One-Line Integration**: Add receipts to your project with a single CI step
- **No Infrastructure**: No servers to run, no keys to manage (for basic use)

### For Users
- **Frictionless Verification**: Drag-and-drop JSON file → instant cryptographic verification
- **Complete Privacy**: Verification happens 100% client-side in browser
- **No Installation Required**: Works on desktop and mobile browsers
- **Reproducible Builds**: Same receipt always produces identical output

### For Organizations
- **Supply Chain Security**: Cryptographic proof of software provenance
- **Compliance Ready**: Audit trails compatible with SLSA, Sigstore, Rekor
- **Risk Reduction**: Mathematical proof replaces organizational trust
- **Integration Friendly**: Works with existing CI/CD and package managers

## Product Components

### 1. Web Verifier (Current: v0.8 → Target: v1.0)
**What:** Browser-based receipt verification tool  
**Status:** Basic verifier exists, needs signatures, performance, accessibility  
**Target:** Production-quality verifier for receipts of any size with full signature support

### 2. Web Generator (Target: v1.0)
**What:** Browser-based receipt creation tool  
**Status:** Doesn't exist  
**Target:** Drag-and-drop file → download receipt JSON (client-side only)

### 3. CLI Tools (Current: v0.7 → Target: v1.0)
**What:** Command-line verifier, generator, and ingest tools  
**Status:** Python scripts exist, need packaging and hardening  
**Target:** `pip install thiele` with `thiele-receipt` and `thiele-verify` commands

### 4. CI/CD Integration (Target: v1.0)
**What:** GitHub Actions, GitLab CI, and other CI/CD templates  
**Status:** Doesn't exist  
**Target:** Add receipts to any project in 3 lines of YAML

### 5. Ecosystem Tools (Target: v1.1)
**What:** Badges, QR codes, package manager integration  
**Status:** Doesn't exist  
**Target:** "Receipt Verified" badges and Homebrew/Nix/etc formulas

## In Scope for v1.0 "Mainstream"

✅ **Core Features**
- TRS-1.0 spec finalized and frozen
- Ed25519 signature support in CLI and web
- Large receipt support (hundreds of MB, millions of steps)
- Mobile-friendly web UI with accessibility
- Browser-based receipt generator
- Packaged CLI tools (`pip install thiele`)
- GitHub Action for CI integration
- Documentation and tutorials

✅ **Security & Compliance**
- Signature verification
- Path traversal protection
- Size limits and resource controls
- Basic SLSA/Sigstore integration patterns documented

## Out of Scope for v1.0

❌ **Advanced Features (Future Versions)**
- Full ZK proof service integration
- Proprietary key management systems
- Custom signature schemes beyond Ed25519
- Binary delta/diff receipts
- Multi-party signing workflows
- Advanced receipt compression

❌ **Enterprise-Only Features (Future Commercial)**
- SLA guarantees
- Dedicated support channels
- Custom compliance tooling
- Managed signing infrastructure

❌ **Nice-to-Have (Prioritize Later)**
- Receipt search/indexing service
- Visual receipt explorer/debugger
- Receipt marketplace/registry
- Automated CVE scanning for receipts

## Success Metrics

### Adoption Indicators
- **Downloads**: 1,000+ CLI installs within 3 months of v1.0
- **Usage**: 100+ projects using receipts in CI within 6 months
- **Ecosystem**: 5+ package managers with receipt support within 1 year

### Quality Indicators
- **Reliability**: <1% error rate on receipt verification
- **Performance**: Verify 1M-step receipts in <30s (web) / <5s (CLI)
- **Accessibility**: Lighthouse accessibility score ≥ 90
- **Security**: Zero critical vulnerabilities in core verification code

### Community Indicators
- **Documentation**: 90%+ of users can create their first receipt in <10 minutes
- **Contributions**: 10+ external contributors within first year
- **Integration**: Featured in at least one major security/DevOps conference

## Competitive Landscape

### How Thiele Receipts Differ

**vs. Digital Signatures (GPG, Sigstore)**
- Signatures prove *who* signed, receipts prove *how* it was built
- Receipts enable deterministic reconstruction
- No trust required in signer's key management

**vs. Reproducible Builds (Debian, Nix)**
- Receipts work with ANY build system, not just specific ones
- Don't require controlled build environments
- Include cryptographic proof of each step

**vs. SBOMs (Software Bill of Materials)**
- SBOMs list components, receipts prove construction process
- Receipts enable verification without access to original toolchain
- Include hash chains for tamper detection

**vs. SLSA/SCAI Frameworks**
- Complementary: receipts provide the cryptographic evidence SLSA requires
- Thiele receipts can be embedded in SLSA attestations
- More granular: step-by-step proof vs. high-level metadata

## Go-to-Market Strategy

### Phase 1: Technical Validation (Months 1-3)
- Polish web verifier and generator
- Package CLI tools for easy installation
- Create comprehensive documentation
- Build 5-10 example projects using receipts

### Phase 2: Developer Adoption (Months 4-6)
- GitHub Action release and promotion
- Conference talks and blog posts
- Engage with OSS security communities
- Partner with 2-3 popular OSS projects for case studies

### Phase 3: Ecosystem Growth (Months 7-12)
- Package manager integration
- Badge and QR code adoption
- Supply chain security vendor partnerships
- Enterprise pilot programs

## Product Principles

### Design Principles
1. **Zero-Trust by Default**: No service, no servers, no external dependencies for core features
2. **Friction-Free**: Should be easier to use receipts than to not use them
3. **Privacy-First**: All sensitive operations happen client-side
4. **Mainstream-Ready**: Must work on mobile, must have <10min learning curve
5. **Integration-Friendly**: Drop into existing workflows, don't replace them

### Technical Principles
1. **Minimal Specifications**: TRS spec should fit on one page
2. **Boring Crypto**: Use proven primitives (SHA-256, Ed25519), no novel crypto
3. **Fail Secure**: Verification errors should fail loudly and clearly
4. **Progressive Enhancement**: Basic features work everywhere, advanced features when available
5. **Open by Design**: Everything open source, no lock-in, no proprietary extensions

## Risks & Mitigations

### Technical Risks

**Risk**: Large receipts cause browser memory issues  
**Mitigation**: Web Workers, streaming JSON parsing, progress indicators

**Risk**: Receipt format needs breaking changes  
**Mitigation**: Frozen TRS-1.0 spec, versioning for future formats

**Risk**: Signature verification complexity  
**Mitigation**: Use standard libraries (nacl.js), extensive testing

### Adoption Risks

**Risk**: "Too complicated for average users"  
**Mitigation**: Browser tools require zero installation/setup, clear visual feedback

**Risk**: "Not enough benefit vs. current signing"  
**Mitigation**: Educational content, demos showing attacks receipts prevent

**Risk**: "Integration friction too high"  
**Mitigation**: One-line CI integration, comprehensive examples

### Ecosystem Risks

**Risk**: Package managers don't adopt receipt support  
**Mitigation**: Start with Homebrew/Nix (community-friendly), show value with examples

**Risk**: Competing standards emerge  
**Mitigation**: Focus on interop (SLSA, Sigstore), be the best tool not the only tool

## Timeline to v1.0

### Month 1: Foundation
- Week 1-2: Freeze TRS spec, create conformance tests
- Week 3-4: Harden CLI with signatures, package for pip

### Month 2: Web Tools
- Week 1-2: Production web verifier (signatures, performance, accessibility)
- Week 3-4: Browser receipt generator

### Month 3: Integration
- Week 1-2: GitHub Action and CI templates
- Week 3-4: Documentation, examples, tutorials

**Launch Target**: End of Month 3

## Post-v1.0 Roadmap

### v1.1: Ecosystem (Months 4-6)
- Badges and QR codes
- Package manager recipes
- More CI/CD platform support

### v1.2: Supply Chain (Months 7-9)
- SLSA attestation integration
- Rekor transparency log support
- Enhanced SBOM generation

### v2.0: Advanced (Year 2)
- Zero-knowledge proof integration
- Multi-party signing
- Receipt compression and deltas

## Conclusion

The Thiele Receipt System has a clear path to becoming the standard for cryptographically verifiable software distribution. By focusing on:

1. **Usability** (browser tools, one-line CI)
2. **Security** (frozen spec, proven crypto)
3. **Ecosystem** (GitHub Actions, package managers)

We can achieve mainstream adoption while maintaining the technical rigor that makes receipts trustworthy.

The v1.0 release will prove that proof-based software distribution is not just possible, but *easier* than the current trust-based model.
