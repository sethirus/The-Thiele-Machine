# Supply-Chain Provenance

This directory contains attestations and provenance records for Thiele Machine releases, following industry standards:

- **SLSA** (Supply chain Levels for Software Artifacts)
- **in-toto** (Framework for securing software supply chains)
- **Sigstore/Rekor** (Transparency log for artifact integrity)

## Files

- `slsa-provenance.json` - SLSA v1 provenance attestation
- `TRANSPARENCY.txt` - Rekor transparency log entries

## Verification

### Verify SLSA Provenance

The SLSA provenance attestation proves:
- **Builder identity**: GitHub Actions
- **Source location**: GitHub repository + commit SHA
- **Build process**: Reproducible workflow
- **Materials**: All input dependencies

To verify:

```bash
# Using cosign (requires Sigstore)
cosign verify-attestation --type slsaprovenance \
  --certificate-identity-regexp='^https://github.com/sethirus/The-Thiele-Machine/' \
  <artifact>

# Manual verification
python3 ../tools/verify_provenance.py slsa-provenance.json
```

### Verify Transparency Log

The Rekor entries provide tamper-evident proof that artifacts existed at a specific time:

```bash
# Get entry by UUID
rekor-cli get --uuid <UUID>

# Search by artifact hash
rekor-cli search --sha <SHA256>

# Verify inclusion proof
rekor-cli verify --uuid <UUID>
```

## Generating Attestations

Attestations are automatically generated during CI release workflow:

```yaml
# In .github/workflows/release.yml
- name: Generate SLSA provenance
  run: python3 tools/generate_slsa_provenance.py
  
- name: Submit to Rekor
  run: python3 tools/rekor_submit.py dist/receipt.json dist/zkproof.json
```

### Manual Generation

```bash
# Generate SLSA provenance
python3 tools/generate_slsa_provenance.py \
  --artifact dist/receipt.json \
  --commit $GITHUB_SHA \
  --workflow release.yml

# Submit to Rekor transparency log
python3 tools/rekor_submit.py \
  dist/receipt.json \
  dist/zkproof.json \
  --out attestations/TRANSPARENCY.txt
```

## Integration with Package Managers

These attestations enable package managers to verify authenticity:

### APT/Debian

```bash
# Verify signature and provenance
apt-get install --allow-unauthenticated thiele-verify
dpkg --verify thiele-verify
```

### Homebrew

```ruby
# Formula includes provenance check
class ThieleReplay < Formula
  url "https://github.com/sethirus/The-Thiele-Machine/releases/download/v1.0/thiele-replay.tar.gz"
  sha256 "..."
  
  def install
    # Verify SLSA provenance before install
    system "cosign", "verify-attestation", "..."
  end
end
```

### Docker

```dockerfile
# Verify provenance in Dockerfile
FROM python:3.12
RUN curl -LO https://github.com/sethirus/The-Thiele-Machine/releases/download/v1.0/receipt.json
RUN cosign verify-attestation --type slsaprovenance receipt.json
```

## Standards References

- [SLSA Framework](https://slsa.dev/)
- [in-toto Attestations](https://in-toto.io/)
- [Sigstore Rekor](https://docs.sigstore.dev/rekor/overview/)
- [Cosign](https://docs.sigstore.dev/cosign/overview/)

## Security Properties

These attestations provide:

1. **Non-repudiation**: Cryptographic proof of build provenance
2. **Transparency**: Public log prevents backdating or hiding artifacts
3. **Integrity**: Tamper-evident records detect modifications
4. **Traceability**: Full chain from source to binary

## Threat Model

Protections against:
- ✅ Compromised build environment
- ✅ Tampered artifacts post-build
- ✅ Backdated or hidden releases
- ✅ Dependency confusion attacks
- ✅ Compromised distribution channels

Does NOT protect against:
- ❌ Compromised source repository
- ❌ Malicious maintainer
- ❌ Bugs in signing infrastructure

Use **receipts** + **ZK proofs** + **provenance** together for defense-in-depth.
