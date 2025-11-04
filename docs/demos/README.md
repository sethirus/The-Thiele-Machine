# Thiele Machine Live Demos

This directory contains interactive browser-based demonstrations of the Thiele Machine's zero-trust computing capabilities.

## 🎯 Available Demos

### 1. Proof-Install Demo (`install.html`)
- **Purpose**: Demonstrates zero-trust software installation using cryptographic receipts
- **How it works**: 
  1. Upload a Thiele receipt (JSON file)
  2. The demo verifies the cryptographic signatures
  3. Click "Materialize" to reconstruct the binary from the receipt
  4. Download the verified files
- **Sample data**: Use `sample-receipt.json` to try it out

### 2. ZK Verify Demo (`zk.html`)
- **Purpose**: Verify zero-knowledge proofs for Thiele computations
- **How it works**:
  1. Upload a ZK proof file (JSON format)
  2. The demo validates the proof structure
  3. Verifies the Merkle root and public outputs
  4. Shows verification status and proof details
- **Sample data**: Use `sample-zkproof.json` to try it out

### 3. Trusting Trust Demo (`trusting-trust.html`)
- **Purpose**: Defeat compiler backdoors by proving different toolchains produce identical output
- **How it works**:
  1. Upload receipts from two different compilers (e.g., GCC and Clang)
  2. The demo compares the SHA256 hashes of the compiled binaries
  3. If hashes match, no compiler-specific backdoor was inserted
  4. Demonstrates Ken Thompson's "Trusting Trust" attack defeated by receipts
- **Sample data**: Use `sample-gcc-receipt.json` and `sample-clang-receipt.json`

## 🔒 Privacy & Security

**All demos run 100% client-side in your browser:**
- No files are uploaded to any server
- All verification happens using JavaScript in your browser
- Your receipts and proofs never leave your machine
- True zero-trust computing

## 📦 Sample Data Files

The directory includes sample JSON files for testing:

- `sample-receipt.json` - Basic Thiele receipt for the install demo
- `sample-zkproof.json` - Zero-knowledge proof example
- `sample-gcc-receipt.json` - Compiler receipt from GCC
- `sample-clang-receipt.json` - Compiler receipt from Clang

## 🌐 Live Demos

When deployed via GitHub Pages, these demos are available at:
- **All Demos**: https://sethirus.github.io/The-Thiele-Machine/demos/
- **Proof-Install**: https://sethirus.github.io/The-Thiele-Machine/demos/install.html
- **ZK Verify**: https://sethirus.github.io/The-Thiele-Machine/demos/zk.html
- **Trusting Trust**: https://sethirus.github.io/The-Thiele-Machine/demos/trusting-trust.html

## 🧪 Testing

The demos are tested using pytest. Run tests with:

```bash
pytest tests/test_web_demos.py -v
```

Tests verify:
- All HTML files exist and have proper structure
- JavaScript files are present
- Sample data files are valid JSON
- Links between pages work correctly
- Required fields are present in sample data

## 🛠️ Development

### File Structure

```
web/demos/
├── index.html                    # Landing page with all demos
├── install.html                  # Proof-Install demo
├── install.js                    # JavaScript for install demo
├── zk.html                       # ZK verification demo (self-contained)
├── trusting-trust.html          # Trusting Trust demo (self-contained)
├── sample-receipt.json          # Sample data for install demo
├── sample-zkproof.json          # Sample data for ZK demo
├── sample-gcc-receipt.json      # Sample GCC compiler receipt
├── sample-clang-receipt.json    # Sample Clang compiler receipt
└── README.md                    # This file
```

### Adding New Demos

1. Create a new HTML file in this directory
2. Add sample data as JSON files
3. Update `index.html` to link to the new demo
4. Add tests in `tests/test_web_demos.py`
5. Update this README

## 📚 Documentation

For more information about the Thiele Machine:
- [Main README](../../README.md)
- [Receipt Schema](../../docs/receipt_schema.md)
- [Roadmap Enhancements](../../roadmap-enhancements/README.md)

## ⚖️ License

Copyright 2025 Devon Thiele

Licensed under the Apache License, Version 2.0. See [LICENSE](../../LICENSE) for details.
