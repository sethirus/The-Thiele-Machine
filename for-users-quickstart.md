# Quick Start for Users: Verify Receipts in 2 Ways

This guide shows you how to verify software receipts in under 2 minutes.

## What Are Receipts?

Receipts are cryptographic proofs that software hasn't been tampered with. Think of them like a mathematical seal of authenticity.

**Benefits:**
- ✅ Verify software integrity without trusting the source
- ✅ Detect tampering instantly
- ✅ Works offline, no servers needed
- ✅ Free and open source

---

## Method 1: Browser (Easiest - 30 Seconds)

### Step 1: Download the receipt

Get the `.receipt.json` file from the project's releases page.

### Step 2: Verify it

1. Visit: **https://sethirus.github.io/The-Thiele-Machine/verify.html**
2. Drag and drop the `.receipt.json` file
3. See instant results ✅

![Browser Verifier Screenshot](https://github.com/user-attachments/assets/54759101-b534-4985-a620-7523610250c6)

### What the verifier checks:

- ✅ **Hash Chain**: All file hashes are correct
- ✅ **Global Digest**: Overall integrity is intact
- ✅ **Signature** (if present): Receipt was signed by the maintainer
- ✅ **File Count**: All expected files are accounted for

**Done! You've verified the software.**

---

## Method 2: Command Line (Advanced - 2 Minutes)

For developers who prefer the CLI.

### Step 1: Install the verifier

```bash
pip install git+https://github.com/sethirus/The-Thiele-Machine.git
```

### Step 2: Download receipt and artifact

```bash
# Example: verifying a Python package
curl -LO https://example.com/releases/myapp-1.0.0.tar.gz
curl -LO https://example.com/releases/myapp-1.0.0.tar.gz.receipt.json
```

### Step 3: Verify

```bash
thiele-verify myapp-1.0.0.tar.gz.receipt.json
```

**Output:**
```
✅ Receipt verification successful
   Version: 1.0
   Files: 1
   Global digest: a3f2e1...
   Signature: VALID (Ed25519)
```

### Step 4: (Optional) Compare file hash

```bash
# Extract expected digest from receipt
python3 -c "import json; print(json.load(open('myapp-1.0.0.tar.gz.receipt.json'))['global_digest'])"

# Compute actual digest
sha256sum myapp-1.0.0.tar.gz
```

If they match, you're good! ✅

**Done! The software is verified.**

---

## What If Verification Fails?

### ❌ Hash mismatch
**What it means:** The file has been modified  
**Action:** Don't use it! Download from official source again

### ❌ Invalid signature
**What it means:** Receipt wasn't signed by the maintainer  
**Action:** Contact the project maintainers

### ❌ Missing files
**What it means:** Receipt expects files that aren't present  
**Action:** Download complete release package

### ⚠️ No signature
**What it means:** Receipt is unsigned (integrity only, no authenticity)  
**Action:** You can verify integrity, but can't prove who created it

---

## Understanding Verification Levels

| Feature | Unsigned Receipt | Signed Receipt |
|---------|-----------------|----------------|
| Tamper detection | ✅ Yes | ✅ Yes |
| Proves authenticity | ❌ No | ✅ Yes |
| Who can create | Anyone | Only key holder |
| Security level | Medium | High |

**Recommendation:** Always prefer signed receipts for security-critical software.

---

## Frequently Asked Questions

### Q: Do I need to trust the server I downloaded from?

**A:** No! That's the point. Receipts let you verify integrity mathematically, not by trusting a server.

### Q: Can receipts be faked?

**A:** Unsigned receipts can be recreated by anyone. Signed receipts can only be created by someone with the private key.

### Q: What if I lose the receipt?

**A:** You can only verify what you have. Keep receipts alongside your downloads.

### Q: Does verification require internet?

**A:** No! Everything runs locally in your browser or CLI. No servers involved.

### Q: How is this different from checksums?

**A:** Traditional checksums are single hashes. Receipts include:
- Full hash chain showing all computation steps
- Optional cryptographic signatures
- Metadata about the build
- Reproducible verification process

### Q: What's the performance impact?

**A:** Verification is fast:
- Small files (< 1 MB): < 1 second
- Large files (100 MB): ~5 seconds
- Very large (1 GB+): ~30 seconds

### Q: Can I verify old versions?

**A:** Yes! Receipts are permanent. As long as you have the receipt and artifact, you can verify.

---

## Advanced: Verifying Specific Files

If a receipt contains multiple files, you can verify individual ones:

```bash
# List files in receipt
python3 -c "import json; r=json.load(open('receipt.json')); print('\n'.join([f['path'] for f in r['files']]))"

# Extract digest for specific file
python3 -c "import json; r=json.load(open('receipt.json')); f=[x for x in r['files'] if x['path']=='myfile.py'][0]; print(f'Expected: {f[\"sha256\"]}')"

# Compute actual digest
sha256sum myfile.py
```

---

## Examples

### Example 1: Python Package

```bash
# Download
pip download mypackage==1.0.0
curl -LO https://example.com/mypackage-1.0.0.receipt.json

# Verify
thiele-verify mypackage-1.0.0.receipt.json
```

### Example 2: Binary Executable

```bash
# Download
curl -LO https://example.com/releases/myapp.exe
curl -LO https://example.com/releases/myapp.exe.receipt.json

# Verify
thiele-verify myapp.exe.receipt.json
```

### Example 3: Multiple Files

```bash
# Download release tarball with receipt
tar -xzf release.tar.gz
cd release/

# Verify all files at once
thiele-verify release.receipt.json
```

---

## Creating Your Own Receipts

Want to create receipts for your own files?

See the [Maintainer's Quick Start](for-maintainers-quickstart.md) for a 5-minute guide.

---

## Next Steps

- **Learn More**: [Receipt Guide](https://github.com/sethirus/The-Thiele-Machine/blob/main/RECEIPT_GUIDE.md)
- **Technical Spec**: [TRS-1.0 Specification](https://github.com/sethirus/The-Thiele-Machine/blob/main/trs-spec-v1.md)
- **Report Issues**: [GitHub Issues](https://github.com/sethirus/The-Thiele-Machine/issues)
- **Create Receipts**: [Browser Generator](https://sethirus.github.io/The-Thiele-Machine/create.html)

---

## Support

Questions? Issues? Suggestions?

- 📧 Email: thethielemachine@gmail.com
- 🐛 Issues: https://github.com/sethirus/The-Thiele-Machine/issues
- 📖 Docs: https://github.com/sethirus/The-Thiele-Machine/tree/main/docs

**Happy verifying!** 🔒✅
