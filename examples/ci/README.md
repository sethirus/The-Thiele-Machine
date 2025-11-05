# CI/CD Integration Examples

This directory contains example CI/CD configurations for integrating Thiele receipts into your build pipeline.

## Quick Start

### GitHub Actions

**Option 1: Use the Thiele Receipt Action (Recommended)**

```yaml
- name: Create receipt
  uses: sethirus/The-Thiele-Machine/.github/actions/create-receipt@main
  with:
    files: 'dist/*'
    output: 'receipt.json'
    metadata: '{"version":"1.0.0"}'
```

**Option 2: Use the CLI directly**

```yaml
- name: Install Thiele
  run: pip install thiele-replay  # (not yet published to PyPI)

- name: Create receipt
  run: thiele-receipt dist/* --output receipt.json
```

## Examples

### GitHub Actions

- **[github-actions-simple.yml](github-actions-simple.yml)** - Minimal example for source code receipts
- **[github-actions-release-receipts.yml](github-actions-release-receipts.yml)** - Full example with release integration

### Other CI Systems

Coming soon:
- GitLab CI
- CircleCI
- Travis CI
- Jenkins

## Usage Patterns

### 1. Receipts for Release Artifacts

Generate receipts when you publish a release:

```yaml
on:
  release:
    types: [published]

jobs:
  receipts:
    steps:
      - uses: ./.github/actions/create-receipt
        with:
          files: 'dist/*'
          output: 'dist/receipt.json'
```

### 2. Receipts for Every Build

Generate receipts on every commit:

```yaml
on:
  push:
    branches: [main]

jobs:
  receipts:
    steps:
      - uses: ./.github/actions/create-receipt
        with:
          files: 'build/**/*'
          output: 'build-receipt.json'
```

### 3. Signed Receipts

Generate signed receipts using secrets:

```yaml
steps:
  - name: Create signing key
    run: |
      # Generate or retrieve signing key
      echo "${{ secrets.RECEIPT_SIGNING_KEY }}" > signing.key
  
  - uses: ./.github/actions/create-receipt
    with:
      files: 'dist/*'
      sign-key: 'signing.key'
      output: 'signed-receipt.json'
```

### 4. Verification in CI

Verify receipts as part of your build:

```yaml
steps:
  - name: Verify receipt
    run: |
      python3 verifier/replay.py receipt.json --dry-run
```

## Best Practices

### 1. Always Include Metadata

```yaml
metadata: |
  {
    "project": "${{ github.repository }}",
    "version": "${{ github.ref_name }}",
    "commit": "${{ github.sha }}",
    "build_date": "${{ github.event.head_commit.timestamp }}",
    "ci_run": "${{ github.run_id }}"
  }
```

### 2. Upload Receipts as Artifacts

```yaml
- uses: actions/upload-artifact@v3
  with:
    name: receipts
    path: '**/*receipt.json'
```

### 3. Attach to Releases

```yaml
- uses: actions/upload-release-asset@v1
  env:
    GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
  with:
    upload_url: ${{ github.event.release.upload_url }}
    asset_path: receipt.json
    asset_name: receipt.json
    asset_content_type: application/json
```

### 4. Create "Receipt Verified" Badge

Add to your README:

```markdown
[![Receipt](https://img.shields.io/badge/Receipt-Verified-green?logo=lock)](https://sethirus.github.io/The-Thiele-Machine/verify.html)
```

## Action Inputs

### Required Inputs

- **`files`** - Files to include (space-separated paths or globs)

### Optional Inputs

- **`output`** - Output path (default: `receipt.json`)
- **`metadata`** - JSON metadata to include
- **`sign-key`** - Path to Ed25519 private key for signing
- **`public-key`** - Path to public key (optional, derived if not provided)

## Action Outputs

- **`receipt-path`** - Path to the generated receipt
- **`global-digest`** - Global digest of the receipt

## Example: Complete Workflow

```yaml
name: Build and Receipt

on:
  push:
    branches: [main]
  release:
    types: [published]

jobs:
  build:
    runs-on: ubuntu-latest
    
    steps:
      - uses: actions/checkout@v4
      
      # Your build steps
      - name: Build
        run: |
          make build
          # Output to dist/
      
      # Create receipt
      - name: Create receipt
        id: receipt
        uses: ./.github/actions/create-receipt
        with:
          files: 'dist/*'
          output: 'dist/receipt.json'
          metadata: |
            {
              "project": "${{ github.repository }}",
              "version": "${{ github.ref_name }}",
              "commit": "${{ github.sha }}"
            }
      
      # Verify
      - name: Verify receipt
        run: |
          python3 verifier/replay.py dist/receipt.json --dry-run
      
      # Upload
      - name: Upload artifacts
        uses: actions/upload-artifact@v3
        with:
          name: build-with-receipt
          path: dist/
      
      # Attach to release
      - name: Attach to release
        if: github.event_name == 'release'
        uses: actions/upload-release-asset@v1
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
        with:
          upload_url: ${{ github.event.release.upload_url }}
          asset_path: dist/receipt.json
          asset_name: receipt.json
          asset_content_type: application/json
      
      # Badge (optional)
      - name: Create badge
        run: |
          echo "Receipt digest: ${{ steps.receipt.outputs.global-digest }}"
```

## Troubleshooting

### Files not found

Make sure glob patterns match your files:

```bash
# Test locally
ls dist/*
```

### Signing fails

Ensure your signing key is properly formatted (32 bytes or 64 hex characters):

```bash
# Generate a test key
python3 -c "from nacl import signing; k = signing.SigningKey.generate(); print(k.encode().hex())"
```

### Receipt too large

For large projects, consider:
- Creating separate receipts for different components
- Using file filtering (`dist/*.whl` instead of `dist/*`)
- Compressing receipts before upload

## Support

- **Documentation:** [Receipt Guide](../../RECEIPT_GUIDE.md)
- **Specification:** [TRS-1.0 Spec](../../trs-spec-v1.md)
- **Issues:** [GitHub Issues](https://github.com/sethirus/The-Thiele-Machine/issues)
- **Discussions:** [GitHub Discussions](https://github.com/sethirus/The-Thiele-Machine/discussions)
