# Thiele Receipt Generator Action

Automatically generate cryptographic receipts for your build artifacts on every release.

## Features

- 🔐 **Cryptographic Verification**: Generate SHA-256 based receipts for all artifacts
- 🔑 **Ed25519 Signing**: Optional signature support for authenticity
- 🤖 **Auto-Discovery**: Automatically find build outputs in dist/, target/, build/, etc.
- 📦 **Multi-Artifact**: Create receipts for all artifacts at once
- 📋 **Manifest Index**: Generates MANIFEST.receipt.json for easy discovery
- ☁️ **Auto-Upload**: Optionally upload receipts to GitHub releases

## Quick Start

Add this to your workflow to generate receipts on every release:

```yaml
name: Release with Receipts

on:
  release:
    types: [published]

jobs:
  create-receipts:
    runs-on: ubuntu-latest
    permissions:
      contents: write
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Build your project
        run: |
          # Your build commands here
          # e.g., npm run build, cargo build --release, etc.
      
      - name: Generate receipts
        uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
        with:
          project-dir: .
          upload-to-release: true
```

That's it! Your releases will now include `.receipt.json` files for all build artifacts.

## Usage Examples

### Auto-Discovery Mode (Recommended)

Automatically find and create receipts for all build artifacts:

```yaml
- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    project-dir: .                    # Scan current directory
    upload-to-release: true           # Upload to GitHub release
```

This will:
1. Scan `dist/`, `target/`, `build/`, `bin/`, `pkg/`, etc.
2. Find all artifacts (`.whl`, `.tar.gz`, `.exe`, `.jar`, etc.)
3. Read package manifest (`package.json`, `pyproject.toml`, `Cargo.toml`)
4. Create a receipt for each artifact
5. Generate `MANIFEST.receipt.json` index
6. Upload all receipts to the release

### Specific Files Mode

Create a receipt for specific files:

```yaml
- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    files: dist/*.whl dist/*.tar.gz   # Specific files or patterns
    output: my-receipt.json           # Output filename
```

### With Signing

Sign receipts with Ed25519 for authenticity:

```yaml
- name: Generate signing key
  run: |
    python3 << 'EOF'
    from cryptography.hazmat.primitives.asymmetric import ed25519
    from cryptography.hazmat.primitives import serialization
    
    private_key = ed25519.Ed25519PrivateKey.generate()
    with open('signing.key', 'wb') as f:
        f.write(private_key.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption()
        ))
    
    public_key = private_key.public_key()
    with open('signing.pub', 'wb') as f:
        f.write(public_key.public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo
        ))
    EOF

- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    project-dir: .
    sign-key: signing.key
    public-key: signing.pub
    upload-to-release: true
```

**Best Practice**: Store your signing key in GitHub Secrets:

```yaml
- name: Setup signing key
  env:
    SIGNING_KEY: ${{ secrets.THIELE_SIGNING_KEY }}
  run: echo "$SIGNING_KEY" > signing.key

- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    project-dir: .
    sign-key: signing.key
    upload-to-release: true
```

### With Metadata

Include custom metadata in receipts:

```yaml
- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    project-dir: .
    metadata: |
      {
        "version": "${{ github.ref_name }}",
        "commit": "${{ github.sha }}",
        "build_date": "${{ github.event.head_commit.timestamp }}",
        "repository": "${{ github.repository }}"
      }
```

## Inputs

| Input | Description | Required | Default |
|-------|-------------|----------|---------|
| `files` | Files to include (space-separated). Mutually exclusive with `project-dir`. | No | - |
| `project-dir` | Project directory for auto-discovery. Mutually exclusive with `files`. | No | - |
| `output` | Output path for receipt(s) | No | `receipts` |
| `metadata` | JSON metadata to include | No | - |
| `sign-key` | Path to Ed25519 private key | No | - |
| `public-key` | Path to Ed25519 public key | No | - |
| `upload-to-release` | Auto-upload to GitHub release | No | `false` |
| `create-manifest` | Create MANIFEST.receipt.json | No | `true` |

## Outputs

| Output | Description |
|--------|-------------|
| `receipt-path` | Path to generated receipt(s) |
| `global-digest` | Global digest (single file mode) |
| `receipt-count` | Number of receipts created |

## Verification

Users can verify your receipts in two ways:

### Browser (Easiest)

1. Visit https://sethirus.github.io/The-Thiele-Machine/verify.html
2. Drag and drop the `.receipt.json` file
3. Get instant verification ✅

### CLI

```bash
pip install git+https://github.com/sethirus/The-Thiele-Machine.git
thiele-verify artifact.receipt.json
```

Or fetch directly from your releases:

```bash
thiele-fetch your-username/your-repo
```

## Language-Specific Examples

### Python Project

```yaml
- name: Build package
  run: python -m build

- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    project-dir: .
    upload-to-release: true
```

### Rust Project

```yaml
- name: Build release
  run: cargo build --release

- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    project-dir: .
    upload-to-release: true
```

### Node.js Project

```yaml
- name: Build
  run: npm run build

- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    project-dir: .
    upload-to-release: true
```

### Go Project

```yaml
- name: Build
  run: go build -o bin/myapp

- uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    project-dir: .
    upload-to-release: true
```

## FAQ

### Q: Do I need to install anything?

No! The action handles all dependencies automatically.

### Q: What file types are detected in auto-discovery mode?

Common artifact types including:
- Python: `.whl`, `.tar.gz`, `.egg`
- Rust: binaries in `target/release/`
- Node.js: archives in `dist/`
- Java: `.jar`, `.war`
- Go: binaries in `bin/`, `pkg/`
- C/C++: `.exe`, `.dll`, `.so`, `.dylib`
- And more...

### Q: Can I use this in private repositories?

Yes! The action works in both public and private repositories.

### Q: How do I add a verification badge to my README?

Visit https://sethirus.github.io/The-Thiele-Machine/badge.html to generate a badge.

## License

Apache 2.0 - Part of [The Thiele Machine](https://github.com/sethirus/The-Thiele-Machine) project.
