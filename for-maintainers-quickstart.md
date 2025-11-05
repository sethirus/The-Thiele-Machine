# Quick Start for Maintainers: Add Receipts in 5 Minutes

This guide gets receipts into your project with minimal effort.

## Why Add Receipts?

- **Trust**: Users can verify your artifacts without trusting your build server
- **Transparency**: Every file's origin is cryptographically proven
- **Supply Chain Security**: Tamper detection at zero cost
- **Professional**: Show users you care about software integrity

## Option 1: GitHub Action (Recommended)

### Step 1: Add the workflow file

Create `.github/workflows/receipts.yml`:

```yaml
name: Generate Receipts

on:
  release:
    types: [published]
  workflow_dispatch:

jobs:
  create-receipts:
    runs-on: ubuntu-latest
    permissions:
      contents: write
    
    steps:
      - uses: actions/checkout@v4
      
      - uses: actions/setup-python@v5
        with:
          python-version: '3.12'
      
      - name: Install Thiele tools
        run: |
          pip install git+https://github.com/sethirus/The-Thiele-Machine.git
      
      - name: Create receipts
        run: |
          mkdir receipts
          thiele-receipt dist/* --output receipts/ --metadata '{"version":"${{ github.ref_name }}"}'
      
      - name: Upload receipts
        uses: softprops/action-gh-release@v1
        with:
          files: receipts/*.receipt.json
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

### Step 2: Commit and push

```bash
git add .github/workflows/receipts.yml
git commit -m "Add receipt generation to releases"
git push
```

### Step 3: Create a release

Your next release will automatically include `.receipt.json` files!

**Done! Total time: 3 minutes**

---

## Option 2: Manual CLI (Local Builds)

### Step 1: Install Thiele CLI

```bash
pip install git+https://github.com/sethirus/The-Thiele-Machine.git
```

### Step 2: Generate receipt

```bash
# Single file
thiele-receipt myapp.exe --output receipt.json

# Multiple files
thiele-receipt dist/* --output receipts/

# With metadata
thiele-receipt dist/* --metadata '{"version":"1.0.0","commit":"abc123"}'
```

### Step 3: Distribute with your artifacts

Include the `.receipt.json` files alongside your downloads.

**Done! Total time: 2 minutes**

---

## Option 3: Signed Receipts (Advanced)

For maximum security, sign your receipts with Ed25519.

### Generate key pair (once)

```bash
python3 << 'EOF'
from cryptography.hazmat.primitives.asymmetric import ed25519
from cryptography.hazmat.primitives import serialization

# Generate key pair
private_key = ed25519.Ed25519PrivateKey.generate()
public_key = private_key.public_key()

# Save private key (keep secret!)
with open('signing_key.pem', 'wb') as f:
    f.write(private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption()
    ))

# Save public key (distribute with receipts)
with open('public_key.pem', 'wb') as f:
    f.write(public_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    ))

print("✅ Keys generated!")
print("⚠️  Keep signing_key.pem secret")
print("✓  Distribute public_key.pem with receipts")
EOF
```

### Sign receipts

```bash
thiele-receipt dist/* \
  --sign signing_key.pem \
  --public-key public_key.pem \
  --metadata '{"version":"1.0.0"}'
```

### Store private key securely

**GitHub Secrets:**
1. Go to Settings → Secrets and variables → Actions
2. Add `SIGNING_KEY` with contents of `signing_key.pem`
3. Update workflow:

```yaml
- name: Create signed receipts
  env:
    SIGNING_KEY: ${{ secrets.SIGNING_KEY }}
  run: |
    echo "$SIGNING_KEY" > signing_key.pem
    thiele-receipt dist/* --sign signing_key.pem --public-key public_key.pem
    rm signing_key.pem  # Clean up
```

---

## Verification Instructions for Users

Add this to your README:

```markdown
## Verifying Releases

Every release includes cryptographic receipts for verification.

### Browser (Easiest)
1. Visit https://sethirus.github.io/The-Thiele-Machine/verify.html
2. Drag and drop the `.receipt.json` file
3. Get instant verification ✅

### CLI
\`\`\`bash
pip install git+https://github.com/sethirus/The-Thiele-Machine.git
thiele-verify artifact.receipt.json
\`\`\`
```

---

## Troubleshooting

### "Command not found: thiele-receipt"

Install the package:
```bash
pip install git+https://github.com/sethirus/The-Thiele-Machine.git
```

### "No such file or directory: dist/*"

Make sure you've built your artifacts first:
```bash
# Example for Python projects
python -m build
thiele-receipt dist/*
```

### "Permission denied: signing_key.pem"

Protect your key:
```bash
chmod 600 signing_key.pem
```

---

## Next Steps

- **Badge**: Add a "Receipt Verified" badge to your README ([badge generator](https://sethirus.github.io/The-Thiele-Machine/badge.html))
- **QR Codes**: Generate QR codes linking to verification ([QR generator](https://sethirus.github.io/The-Thiele-Machine/qr.html))
- **Automation**: Set up automatic receipt generation in CI
- **Documentation**: Link to the [Receipt Guide](https://github.com/sethirus/The-Thiele-Machine/blob/main/docs/RECEIPT_GUIDE.md)

---

## Support

- **Documentation**: [Receipt Guide](https://github.com/sethirus/The-Thiele-Machine/blob/main/docs/RECEIPT_GUIDE.md)
- **Spec**: [TRS-1.0 Specification](https://github.com/sethirus/The-Thiele-Machine/blob/main/docs/trs-spec-v1.md)
- **Issues**: [GitHub Issues](https://github.com/sethirus/The-Thiele-Machine/issues)
- **Examples**: [CI Examples](https://github.com/sethirus/The-Thiele-Machine/tree/main/examples/ci)

**That's it! Your project now has cryptographic receipts.**
