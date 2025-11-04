# PyPI Package Setup Guide

This guide explains how to publish the Thiele Receipt tools to PyPI.

## Prerequisites

```bash
pip install build twine
```

## Building the Package

### 1. Build the distribution

```bash
python -m build
```

This creates:
- `dist/thiele_replay-1.0.0.tar.gz` (source distribution)
- `dist/thiele_replay-1.0.0-py3-none-any.whl` (wheel distribution)

### 2. Check the distribution

```bash
twine check dist/*
```

### 3. Test installation locally

```bash
pip install dist/thiele_replay-1.0.0-py3-none-any.whl
```

Test the commands:
```bash
thiele-receipt --help
thiele-verify --help
```

### 4. Upload to TestPyPI (optional)

```bash
twine upload --repository testpypi dist/*
```

Then test install:
```bash
pip install --index-url https://test.pypi.org/simple/ thiele-replay
```

### 5. Upload to PyPI

```bash
twine upload dist/*
```

## Usage After Installation

Once published, users can install with:

```bash
pip install thiele-replay
```

Then use the CLI tools:

```bash
# Create a receipt
thiele-receipt myfile.py --output receipt.json

# Create a signed receipt
thiele-receipt myfile.py --sign key.pem --metadata '{"version":"1.0"}'

# Verify a receipt
thiele-verify receipt.json
```

## CLI Commands Available

- `thiele-receipt` - Create TRS-1.0 receipts (alias: `create_receipt.py`)
- `thiele-verify` - Verify receipts (alias: `verifier/replay.py`)
- `thiele-replay` - Verify receipts (same as thiele-verify)
- `thiele-ingest` - Ingest binary tools
- `thiele-delta` - Delta receipt tools

## Version Management

Update version in `pyproject.toml`:

```toml
[project]
name = "thiele-replay"
version = "1.0.1"  # Increment here
```

## Publishing Checklist

- [ ] Update version in `pyproject.toml`
- [ ] Update `CHANGELOG.md` with changes
- [ ] Build package: `python -m build`
- [ ] Check distribution: `twine check dist/*`
- [ ] Test locally: `pip install dist/*.whl`
- [ ] Upload to TestPyPI (optional)
- [ ] Upload to PyPI: `twine upload dist/*`
- [ ] Tag release: `git tag v1.0.1 && git push --tags`
- [ ] Create GitHub release with changelog

## Notes

- Package name on PyPI: `thiele-replay`
- Import name in Python: N/A (CLI tools only for receipts)
- Minimum Python: 3.11
- Core dependencies: PyNaCl, cryptography, jsonschema
