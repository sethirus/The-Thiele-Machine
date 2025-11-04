# CI/CD Templates for Thiele Receipts

This directory contains ready-to-use CI/CD templates for automatically generating cryptographic receipts in various platforms.

## Quick Start

Choose your CI/CD platform and follow the instructions:

### GitHub Actions ✅

**Easiest option** - Use our composite action:

```yaml
- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    project-dir: .
    upload-to-release: true
```

See [../actions/create-receipt/README.md](../actions/create-receipt/README.md) for full documentation.

### GitLab CI

1. Copy [`gitlab-ci.yml`](gitlab-ci.yml) to your repository as `.gitlab-ci.yml`
2. Customize the `build` stage for your project
3. Push and create a tag

```bash
cp .github/ci-templates/gitlab-ci.yml .gitlab-ci.yml
# Edit .gitlab-ci.yml as needed
git add .gitlab-ci.yml
git commit -m "Add receipt generation"
git tag v1.0.0
git push --tags
```

### Azure Pipelines

1. Copy [`azure-pipelines.yml`](azure-pipelines.yml) to your repository
2. Configure Azure Pipelines for your repository
3. Customize build steps
4. Create a release tag

```bash
cp .github/ci-templates/azure-pipelines.yml azure-pipelines.yml
# Edit azure-pipelines.yml as needed
git add azure-pipelines.yml
git commit -m "Add receipt generation"
```

### Generic Script (Any CI/CD)

Use the generic shell script for any CI/CD system:

```bash
# Copy script to your repository
cp .github/ci-templates/generate-receipts.sh .

# Make it executable
chmod +x generate-receipts.sh

# Run it in your CI
./generate-receipts.sh --project . --verify
```

Add to your CI config (CircleCI, Jenkins, Travis, etc.):

```yaml
# CircleCI example
- run:
    name: Generate receipts
    command: ./generate-receipts.sh --project . --output receipts
```

## What Gets Generated

All templates create:

1. **Individual receipts** - One `.receipt.json` file per build artifact
2. **MANIFEST.receipt.json** - Index of all receipts for easy discovery
3. **Verification instructions** - Added to release notes

### Example Output

```
receipts/
├── myapp-1.0.0.whl.receipt.json
├── myapp-1.0.0.tar.gz.receipt.json
└── MANIFEST.receipt.json
```

## Features Across All Templates

| Feature | GitHub | GitLab | Azure | Generic |
|---------|--------|--------|-------|---------|
| Auto-discovery | ✅ | ✅ | ✅ | ✅ |
| Ed25519 signing | ✅ | ✅ | ✅ | ✅ |
| Manifest index | ✅ | ✅ | ✅ | ✅ |
| Auto-upload | ✅ | ✅ | ✅ | Manual |
| Verification | ✅ | ✅ | ✅ | ✅ |

## Auto-Discovery

All templates support auto-discovery mode, which automatically finds build artifacts in:

- `dist/` - Python packages, general builds
- `target/` - Rust, Java builds
- `build/` - General build output
- `bin/` - Compiled binaries
- `pkg/` - Go packages
- `out/` - Various build systems
- `releases/` - Release artifacts

And detects package manifests from:
- `package.json` (Node.js)
- `pyproject.toml` (Python)
- `Cargo.toml` (Rust)
- `pom.xml` (Java/Maven)
- `build.gradle` (Java/Gradle)
- `go.mod` (Go)

## Signing Receipts

To sign receipts with Ed25519 (recommended for production):

### 1. Generate a key pair

```bash
python3 << 'EOF'
from cryptography.hazmat.primitives.asymmetric import ed25519
from cryptography.hazmat.primitives import serialization

# Generate key pair
private_key = ed25519.Ed25519PrivateKey.generate()
public_key = private_key.public_key()

# Save private key (KEEP SECRET!)
with open('signing.key', 'wb') as f:
    f.write(private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption()
    ))

# Save public key (distribute with receipts)
with open('signing.pub', 'wb') as f:
    f.write(public_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    ))

print("✅ Keys generated!")
print("⚠️  Store signing.key as a secret in your CI")
print("✓  Include signing.pub in your repository")
EOF
```

### 2. Add key to CI secrets

- **GitHub**: Settings → Secrets and variables → Actions → New secret
- **GitLab**: Settings → CI/CD → Variables → Add variable
- **Azure**: Pipelines → Library → Secure files or Variable groups

### 3. Update template to use signing

See comments in each template file for signing configuration.

## Language-Specific Examples

### Python

```yaml
# Build
- pip install build
- python -m build

# Generate receipts (auto-discovers dist/*.whl, dist/*.tar.gz)
- ./generate-receipts.sh --project .
```

### Rust

```yaml
# Build
- cargo build --release

# Generate receipts (auto-discovers target/release/*)
- ./generate-receipts.sh --project .
```

### Node.js

```yaml
# Build
- npm run build

# Generate receipts (auto-discovers dist/*)
- ./generate-receipts.sh --project .
```

### Go

```yaml
# Build
- go build -o bin/myapp

# Generate receipts (auto-discovers bin/*)
- ./generate-receipts.sh --project .
```

### C/C++

```yaml
# Build
- make
- make install DESTDIR=build

# Generate receipts (auto-discovers build/*)
- ./generate-receipts.sh --project .
```

## Customizing Templates

All templates support these customizations:

### Add custom metadata

```bash
./generate-receipts.sh --metadata '{
  "version": "1.0.0",
  "commit": "abc123",
  "build_date": "2024-01-01",
  "author": "Your Name"
}'
```

### Specify output directory

```bash
./generate-receipts.sh --output my-receipts
```

### Enable verification

```bash
./generate-receipts.sh --verify
```

### Verbose output

```bash
./generate-receipts.sh --verbose
```

## Verification for End Users

Include these instructions in your release notes:

```markdown
## Verifying This Release

All artifacts include cryptographic receipts for verification.

### Browser (Easiest)
1. Visit https://sethirus.github.io/The-Thiele-Machine/verify.html
2. Download any `.receipt.json` file from this release
3. Drag and drop it into the verifier
4. Get instant verification ✅

### CLI
```bash
# Install verifier
pip install git+https://github.com/sethirus/The-Thiele-Machine.git

# Fetch and verify receipts automatically
thiele-fetch your-username/your-repo

# Or verify manually
thiele-verify artifact.receipt.json
```

### Manual Verification
```bash
# Download artifact and receipt
curl -LO https://github.com/owner/repo/releases/download/v1.0.0/artifact
curl -LO https://github.com/owner/repo/releases/download/v1.0.0/artifact.receipt.json

# Verify hash
python3 << 'EOF'
import json, hashlib
receipt = json.load(open('artifact.receipt.json'))
expected = receipt['files'][0]['sha256']
actual = hashlib.sha256(open('artifact', 'rb').read()).hexdigest()
print("✅ VERIFIED" if expected == actual else "❌ MISMATCH")
EOF
```
```

## Troubleshooting

### "Python 3.11+ required"

Update your CI image to use Python 3.11 or later:

```yaml
# GitHub Actions
- uses: actions/setup-python@v5
  with:
    python-version: '3.12'

# GitLab CI
image: python:3.12

# Azure Pipelines
- task: UsePythonVersion@0
  inputs:
    versionSpec: '3.12'
```

### "No artifacts found"

Make sure you've run your build commands before generating receipts:

```bash
# Python
python -m build

# Rust
cargo build --release

# Node.js
npm run build

# Then generate receipts
./generate-receipts.sh --project .
```

### "Signing key not found"

Ensure your signing key is properly configured:

1. Check the secret is created in your CI platform
2. Verify the secret name matches the template
3. Make sure the key is written to a file before use

### "Import error: create_receipt"

Install Thiele tools:

```bash
pip install git+https://github.com/sethirus/The-Thiele-Machine.git
```

Or use the local script if in the repository:

```bash
python3 create_receipt.py --help
```

## Contributing

Found a bug or want to add support for another CI platform?

1. Open an issue: https://github.com/sethirus/The-Thiele-Machine/issues
2. Submit a PR with your template
3. Update this README

## License

Apache 2.0 - Part of [The Thiele Machine](https://github.com/sethirus/The-Thiele-Machine) project.
