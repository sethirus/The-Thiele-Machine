# Repository Ingestion Guide

This guide explains how to use the enhanced Thiele Receipt system to create cryptographic receipts for entire repositories, build artifacts, and archives.

## Overview

The Thiele Machine now includes comprehensive repository ingestion capabilities:

- **Archive Fetching**: Download and create receipts from GitHub releases or direct URLs
- **Directory-Aware Uploads**: Process entire directories with pattern filtering
- **Metadata Auto-Fill**: Automatically extract project metadata from package manifests
- **Worker-Based Performance**: Web Workers prevent UI blocking during processing
- **Privacy-First Design**: All browser processing is 100% client-side

## Python CLI Usage

### Archive Mode

Fetch and create receipts directly from archive URLs:

```bash
# GitHub release archive
python3 create_receipt.py --archive https://github.com/user/repo/archive/refs/tags/v1.0.0.tar.gz

# Direct tar.gz URL
python3 create_receipt.py --archive https://example.com/project-1.0.0.tar.gz

# With signing
python3 create_receipt.py --archive <URL> --sign keys/signing.key
```

**Supported archive formats:**
- `.zip`
- `.tar.gz` / `.tgz`
- `.tar.bz2`
- `.tar.xz`

### Directory Mode

Scan and create receipts for all files in a directory:

```bash
# Basic directory scan
python3 create_receipt.py --directory ./src

# With include patterns (Python and JavaScript files only)
python3 create_receipt.py --directory ./src --include "*.py" "*.js"

# With exclude patterns (skip tests and cache)
python3 create_receipt.py --directory ./src --exclude "test_*" "__pycache__/**"

# Specify output location
python3 create_receipt.py --directory ./src --output receipts/src_receipt.json
```

**Default exclusions:**
- `.git/**`
- `node_modules/**`
- `__pycache__/**`
- `.venv/**` / `venv/**`
- `*.pyc`
- `.DS_Store`, `Thumbs.db`

### Repository Mode

Auto-discover and create receipts for build artifacts:

```bash
# Scan current directory for build outputs
python3 create_receipt.py --project .

# Scan specific project
python3 create_receipt.py --project /path/to/myproject

# Create signed receipts
python3 create_receipt.py --project . --sign keys/signing.key
```

**Auto-discovered artifacts:**
- Python wheels (`.whl`) from `dist/`
- Tarballs (`.tar.gz`) from `releases/`
- Executables (`.exe`, `.dll`) from `bin/`
- Java archives (`.jar`, `.war`) from `target/`
- Rust binaries from `target/`
- And more...

### Metadata Auto-Fill

The CLI automatically detects and extracts metadata from:

**package.json** (Node.js):
```json
{
  "name": "my-package",
  "version": "1.0.0",
  "description": "My awesome package",
  "author": "Jane Doe",
  "license": "MIT"
}
```

**pyproject.toml** (Python):
```toml
[project]
name = "my-package"
version = "1.0.0"
description = "My awesome package"
```

**Cargo.toml** (Rust):
```toml
[package]
name = "my-package"
version = "1.0.0"
description = "My awesome package"
```

This metadata is automatically included in the receipt without manual input.

## Web UI Usage

### Browser Capabilities

The web interface at `docs/create.html` now supports:

1. **File Upload**: Click "Select Files" or drag-and-drop individual files
2. **Directory Upload**: Click "Select Folder" or drag-and-drop entire folders
3. **Archive URL Input**: Enter a URL to fetch (with limitations, see below)
4. **Metadata Auto-Fill**: Click "Auto-fill from manifest" after uploading files
5. **Progress Tracking**: Visual progress bars during file processing

### Directory Upload

**Desktop browsers** (Chrome, Edge, Firefox):
1. Click "Select Folder" or drag-and-drop a folder onto the upload area
2. The browser will recursively scan all files in the folder
3. Files are processed using Web Workers for better performance
4. Default exclusions (`.git`, `node_modules`, etc.) are automatically applied

**Mobile browsers**:
- Directory upload may not be supported
- Use individual file selection or the Python CLI

### Archive Fetching in Browser

**Important Limitation**: Browser-based archive fetching is limited by CORS (Cross-Origin Resource Sharing) policies. Most archive URLs will be blocked unless they explicitly allow cross-origin requests.

**Recommended approach**:
- Use the Python CLI for reliable archive fetching: `python3 create_receipt.py --archive <URL>`
- Or download the archive manually and upload it as files/directory

**Why the limitation?**
- Browsers prevent JavaScript from fetching arbitrary URLs for security
- GitHub release assets, for example, don't set CORS headers
- The Python CLI doesn't have this restriction

### Metadata Auto-Fill

After uploading files:
1. Click "🔍 Auto-fill from manifest"
2. The system searches for `package.json`, `pyproject.toml`, or `Cargo.toml`
3. If found, metadata is automatically extracted and inserted
4. You can still manually edit or add additional metadata

### Web Worker Performance

**Automatic performance optimization:**
- Files are hashed using Web Workers (separate thread)
- UI remains responsive during processing
- Automatic fallback to main thread if workers unavailable
- Progress indicators show current status

**Worker status** is logged to browser console:
- `✓ Web Worker enabled for better performance` - Workers active
- `⚠ Web Worker not available, using main thread` - Fallback mode

## Examples

### Example 1: Create Receipt for GitHub Release

```bash
# Fetch v1.0.3 release of The Thiele Machine
python3 create_receipt.py \
  --archive https://github.com/sethirus/The-Thiele-Machine/archive/refs/tags/v1.0.3.tar.gz \
  --output releases/thiele-v1.0.3.receipt.json
```

### Example 2: Create Receipt for Project Source Code

```bash
# Scan source directory, include only Python files
python3 create_receipt.py \
  --directory ./thielecpu \
  --include "*.py" \
  --output receipts/thielecpu_receipt.json
```

### Example 3: Create Signed Receipts for All Build Artifacts

```bash
# Auto-discover build outputs and sign receipts
python3 create_receipt.py \
  --project . \
  --sign keys/release_key.bin \
  --public-key keys/release_key.pub
```

### Example 4: Web UI with Metadata

1. Visit `docs/create.html`
2. Drag-and-drop your project folder
3. Click "Auto-fill from manifest"
4. Verify metadata looks correct
5. Click "Generate Receipt"
6. Download the receipt JSON

## Receipt Structure

Receipts include enhanced metadata when created via repository ingestion:

```json
{
  "version": "TRS-1.0",
  "files": [
    {"path": "main.py", "size": 1234, "sha256": "abc..."},
    {"path": "utils.py", "size": 567, "sha256": "def..."}
  ],
  "global_digest": "9aa255d6...",
  "timestamp": "2025-01-04T12:34:56Z",
  "metadata": {
    "name": "my-project",
    "version": "1.0.0",
    "description": "My awesome project",
    "manifest_type": "package.json",
    "scanned_directory": "/path/to/project",
    "file_count": 12
  },
  "sig_scheme": "ed25519",
  "signature": "...",
  "public_key": "..."
}
```

## Verification

All receipts created with these tools can be verified using the standard verification workflow:

```bash
# Verify using Python verifier
python3 verifier/replay.py receipt.json

# Verify using web UI
# Open docs/verify.html and drag-and-drop receipt.json
```

## Performance Guidelines

### File Limits

**Python CLI**:
- Default: 10,000 files maximum
- Default: 1000 MB total size maximum
- Override with manual limits in code if needed

**Web UI**:
- Recommended: < 1000 files for best performance
- Recommended: < 100 MB total size
- Large batches may take time depending on browser

### Optimization Tips

1. **Use Workers**: Web Workers are automatically enabled when supported
2. **Filter Files**: Use `--include` and `--exclude` to limit scope
3. **Batch Processing**: For very large repos, process directories separately
4. **CLI for Large Jobs**: Python CLI handles large batches better than browser

## Privacy and Security

### Client-Side Processing

**Web UI guarantees**:
- All hashing happens in your browser
- No files are uploaded to any server
- No network requests except loading the page
- Works completely offline after page load

**Python CLI guarantees**:
- All processing is local
- Archive downloads are direct (no proxy)
- No telemetry or tracking

### Metadata Handling

- Metadata extraction only reads manifest files
- No data is sent anywhere
- You can review/edit all metadata before generating receipt
- Receipts are cryptographically sealed (tamper-evident)

## Integration with Verification Framework

All receipts created via repository ingestion:

✅ Work with existing `verifier/replay.py`  
✅ Work with `docs/verify.html` browser verifier  
✅ Support Ed25519 signature verification  
✅ Follow TRS-1.0 specification  
✅ Include hash chain integrity checks  

## Troubleshooting

### Archive Fetch Fails

**Problem**: `Archive fetch failed: HTTP 403`  
**Solution**: Some URLs require authentication. Download manually and use `--directory` mode.

**Problem**: `CORS policy blocks request` (in browser)  
**Solution**: Use Python CLI with `--archive` instead.

### Directory Upload Not Working

**Problem**: "Select Folder" button not visible  
**Solution**: Your browser may not support directory upload. Use Python CLI.

**Problem**: Files not appearing after selecting folder  
**Solution**: Check browser console for errors. Try Chrome/Edge for best support.

### Worker Performance

**Problem**: Slow processing in browser  
**Solution**: Check console for "Web Worker enabled" message. If not, try a different browser or use Python CLI.

### Metadata Not Auto-Filling

**Problem**: "No package manifest found" message  
**Solution**: Ensure `package.json`, `pyproject.toml`, or `Cargo.toml` is in uploaded files.

## API Reference

### Python CLI Options

```
--archive URL              Fetch archive and create receipt
--directory DIR            Scan directory recursively
--project DIR              Auto-discover build artifacts
--include PATTERN [...]    Include file patterns (with --directory)
--exclude PATTERN [...]    Exclude file patterns (with --directory)
--output FILE              Receipt output path
--sign KEY_FILE            Sign with Ed25519 key
--public-key PUBKEY_FILE   Include public key in receipt
--metadata JSON            Custom metadata JSON
--verify                   Verify receipt after creation
```

### JavaScript API

```javascript
// Create generator with worker support
const generator = new EnhancedReceiptGenerator();

// Check worker status
console.log(generator.useWorker); // true if workers enabled

// Add files
await generator.addFile(file);

// Generate receipt
const receipt = await generator.generateReceipt({
  metadata: { author: "Name", version: "1.0" }
});

// Clear state
generator.clearFiles();
```

## Learn More

- [Receipt Guide](RECEIPT_GUIDE.md) - Complete receipt documentation
- [TRS-1.0 Specification](trs-spec-v1.md) - Technical specification
- [For Users](for-users-quickstart.md) - 2-minute quickstart for users
- [For Maintainers](for-maintainers-quickstart.md) - 5-minute guide for maintainers
