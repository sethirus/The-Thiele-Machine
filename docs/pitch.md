# The Thiele Machine: Software You Can Install from a Proof

## The Problem

You download software every day. How do you know it's safe? You trust:
- The developer (could be compromised)
- The website (could be hacked)  
- The package manager (could serve malware)
- Your compiler (could have a backdoor)

**Ken Thompson showed in 1984 that even with source code, you can't trust your compiler.** It could insert backdoors when compiling itself. This is the "trusting trust" attack—and until now, there was no solution.

## The Solution

**Don't trust. Verify mathematically.**

The Thiele Machine generates cryptographic **receipts** that prove software was built correctly:

1. **Drop a receipt in your browser** → See the exact binary hash it will create
2. **Click "Materialize"** → The binary reconstructs itself from the proof
3. **No servers, no downloads, no trust** → Just pure mathematics

Even better: Add a **zero-knowledge proof** and you can verify in milliseconds without even running the code.

## Why This Matters

**For users**: Install software knowing it's exactly what was intended—no backdoors, no tampering.

**For developers**: Ship receipts alongside binaries. Anyone can verify authenticity without trusting your build server.

**For security researchers**: The "trusting trust" demo shows how to build the same compiler with GCC and Clang, then cryptographically prove they produce identical output—defeating compiler backdoors for the first time.

**For enterprises**: Integrate receipts into your supply chain. SLSA provenance + Rekor transparency logs + zero-knowledge proofs = defense-in-depth that package managers can verify automatically.

## Try It Now

1. **[Proof-Install Demo](../web/install.html)** - Drop a receipt, get the verified binary
2. **[Trusting Trust Demo](../web/trusting-trust.html)** - See compiler backdoors defeated live
3. **[ZK Verify](../web/zk.html)** - Verify zero-knowledge proofs in your browser

All demos run 100% client-side. No servers. No tracking. Just open in any browser.

## The Science

This isn't vapor—it's backed by:
- **Formal Coq proofs** showing the Thiele Machine strictly contains Turing Machines
- **Empirical evidence** of exponential performance gains on structured problems  
- **Three independent verifiers** (Python, Shell, Go) for defense-in-depth
- **Published research** with DOI [10.5281/zenodo.17316437](https://doi.org/10.5281/zenodo.17316437)

## Get Started

```bash
# Verify any binary
python3 tools/ingest_binary.py /path/to/binary --out receipt.json
python3 verifier/replay.py receipt.json --verify

# Install the verifier
pip install thiele-replay
# or: brew install thiele-replay

# Try the trusting trust demo
cd demos/trusting-trust && make proofpack && make verify
```

## The Vision

**Software you can install from a proof.**

No more "download this .exe and hope for the best." Instead:
- Download a cryptographic receipt (tiny, text file)
- Verify the proof in your browser (instant, no execution)
- Materialize the exact binary the proof guarantees
- Know with mathematical certainty it's safe

This is the future of software distribution. And it's live today.

---

**Repository**: [github.com/sethirus/The-Thiele-Machine](https://github.com/sethirus/The-Thiele-Machine)  
**License**: Apache 2.0  
**Status**: Production-ready verifiers, active research on ZK integration
