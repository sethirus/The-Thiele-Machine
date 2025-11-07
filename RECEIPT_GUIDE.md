# Thiele Receipt Guide: What, Why, and How

> **TL;DR**: Thiele receipts are cryptographic proofs of construction that let you verify software without trusting the source code or the build process. Instead of "trust me, this binary is safe," you get "here's a mathematical proof of exactly how this binary was constructed."

## Table of Contents

1. [What is a Thiele Receipt?](#what-is-a-thiele-receipt)
2. [Why Use Receipts?](#why-use-receipts)
3. [How Receipts Work](#how-receipts-work)
4. [Creating Your First Receipt](#creating-your-first-receipt)
5. [Using Receipts in Your Project](#using-receipts-in-your-project)
6. [Practical Examples](#practical-examples)
7. [Receipt Schema Reference](#receipt-schema-reference)

---

## What is a Thiele Receipt?

A **Thiele receipt** is a JSON file that contains a cryptographically verifiable proof of how a file or program was constructed. Think of it like a detailed recipe that:

- Lists every single byte that goes into your files
- Proves each step with cryptographic hashes (SHA-256)
- Can be independently verified by anyone
- Allows deterministic reconstruction: same receipt → identical output, every time

**Key Insight**: Instead of distributing source code or binaries and asking users to trust them, you distribute *receipts* that mathematically prove how the software was built.

### Real-World Analogy

Imagine you're a master chef. Instead of:
- ❌ Giving someone your finished dish and saying "trust me, it's safe"
- ❌ Giving them your recipe and hoping they follow it correctly

You give them a **receipt** that proves:
- ✅ Exactly which ingredients went in (with chemical analysis)
- ✅ Exactly when and how each ingredient was added
- ✅ A cryptographic fingerprint of the final dish
- ✅ Anyone can verify this proof without having to re-cook the entire meal

## Why Use Receipts?

### Problem: The Trust Dilemma

In traditional software distribution:

```
Developer writes code → Compiles it → Users run the binary
                         ↑
                    "Just trust me"
```

**Questions users can't answer:**
- Is this binary really from that source code?
- Did the compiler insert backdoors? (See: [Trusting Trust attack](https://sethirus.github.io/The-Thiele-Machine/demos/trusting-trust.html))
- Were dependencies tampered with?
- Can I verify this independently?

### Solution: Receipts Replace Trust with Proof

```
Developer creates receipt → Users verify receipt → Materialize binary
                    ↑                       ↑
            Mathematical proof      100% reproducible
```

**With receipts, users can verify:**
- ✅ Every single byte in the binary
- ✅ No backdoors were inserted
- ✅ The construction process was deterministic
- ✅ All of this without trusting the developer

### Use Cases

1. **Zero-Trust Software Distribution**
   - Ship receipts instead of binaries
   - Users verify and materialize on their own machines
   - No trust required in build servers or download channels

2. **Compiler Equivalence Proofs**
   - Prove two different compilers produce identical output
   - Defeat "Trusting Trust" attacks
   - [Try the demo](https://sethirus.github.io/The-Thiele-Machine/demos/trusting-trust.html)

3. **Reproducible Research**
   - Scientific computations with cryptographic audit trails
   - Every result is verifiable and reproducible
   - μ-bit accounting tracks computational costs

4. **Supply Chain Security**
   - Prove software bill of materials (SBOM)
   - Verify dependencies haven't been tampered with
   - Create audit trails for compliance

## How Receipts Work

### Core Concepts

#### 1. State Hashing

A receipt tracks a "virtual filesystem" state using cryptographic hashes:

```python
# Empty state (nothing exists yet)
state_hash = sha256(b'') 
# = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

# After adding files, state hash changes deterministically
state_hash = sha256(
    path1 + sha256(file1_content) + 
    path2 + sha256(file2_content) + ...
)
```

Every operation changes the state hash in a predictable way.

#### 2. Step-by-Step Construction

A receipt is a sequence of **steps**, each containing:

```json
{
  "step": 0,
  "pre_state_sha256": "hash_before_operation",
  "opcode": "EMIT_BYTES",
  "args": {"path": "hello.py", "offset": 0, "bytes_hex": "..."},
  "mu_bits": 42.0,
  "post_state_sha256": "hash_after_operation"
}
```

**Operations (opcodes):**
- `EMIT_BYTES`: Write bytes to a file at a specific offset
- `MAKE_EXEC`: Mark a file as executable
- `ASSERT_SHA256`: Verify a file's hash matches expectations

#### 3. Global Digest

The entire receipt is sealed with a **global digest**:

```python
# Hash each step independently
step_hashes = [sha256(canonical_json(step)) for step in steps]

# Concatenate and hash again
global_digest = sha256(b''.join(step_hashes))
```

This creates a single fingerprint for the entire construction process.

#### 4. μ-Bit Accounting

Each step has a `mu_bits` field tracking information-theoretic cost:

```
μ(query, N, M) = 8 × |canonical(query)| + log₂(N/M)
```

- `8 × |canonical(query)|`: Cost of expressing the query
- `log₂(N/M)`: Cost of reducing search space from N to M states

This tracks the computational "work" of construction in information-theoretic units.

### The Verification Process

```
┌─────────────────┐
│ Receipt.json    │
│ (Proof)         │
└────────┬────────┘
         │
         ▼
┌─────────────────┐      ┌──────────────────┐
│ Verifier        │─────▶│ Virtual FS       │
│ (170 lines)     │      │ state_hash       │
└────────┬────────┘      └──────────────────┘
         │
         │ For each step:
         │ 1. Verify pre_state matches current state
         │ 2. Execute opcode (EMIT_BYTES, etc.)
         │ 3. Verify post_state matches result
         │ 4. Verify μ accounting
         │
         ▼
┌─────────────────┐
│ Materialized    │
│ Files on Disk   │
│ + SHA256 proof  │
└─────────────────┘
```

**Key Property**: If verification succeeds, the output is **mathematically guaranteed** to match the receipt's claims.

## Creating Your First Receipt

### Simple Example: Hello World

Let's create a receipt that constructs a simple Python file.

#### Step 1: Manual Receipt Creation

Create `hello_receipt.json`:

```json
{
  "version": "TRS-0",
  "steps": [
    {
      "step": 0,
      "pre_state_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
      "opcode": "EMIT_BYTES",
      "args": {
        "path": "hello.py",
        "offset": 0,
        "bytes_hex": "7072696e742822486f772061726520796f753f22290a"
      },
      "axioms": ["initial_emit"],
      "oracle_reply": {"status": "sat", "witness": null},
      "mu_bits": 120.0,
      "post_state_sha256": "computed_by_verifier"
    }
  ],
  "global_digest": "computed_by_verifier",
  "sig_scheme": "ed25519",
  "key_id": "thiele-core-2025",
  "public_key": "d06cf289ca021314ed902987377d225fb618095d3e3edc4359fb602984643222",
  "signature": "<hex-encoded ed25519 signature>"
}
```

**What this does:**
- Starts from empty state (`e3b0c44...`)
- Emits bytes to `hello.py` at offset 0
- The hex bytes decode to: `print("How are you?")\n`
- Costs 120 μ-bits (information-theoretic cost)
- Declares an Ed25519 signature and the signing key identifier so the verifier can authenticate it against a trust manifest or explicit public key

> **Note:** The snippet above elides the actual signature for brevity. Use `create_receipt.py --sign <private-key>` (documented below) or `tools/sign_receipts.py` to produce real signatures; unsigned receipts now require the explicit `--allow-unsigned` escape hatch and are rejected by default.

#### Step 2: Convert Your Content to Hex

```python
# Python helper to convert text to hex
def text_to_hex(text):
    return text.encode('utf-8').hex()

content = 'print("How are you?")\n'
print(text_to_hex(content))
# Output: 7072696e742822486f772061726520796f753f22290a
```

#### Step 3: Verify and Materialize

```bash
# Verify the receipt and materialize files
python3 verifier/replay.py hello_receipt.json

# Expected output:
# ✓ Step 0 verified
# ✓ Global digest verified
# Materialized: hello.py (21 bytes)
```

Now you have a cryptographically verified `hello.py` file!

### Using the Receipt Generator Script

For more complex files, use the Thiele receipt generator:

```python
# create_receipt.py
import json
import hashlib

def create_simple_receipt(filename, content):
    """Create a Thiele receipt for a single file."""
    
    # Convert content to hex
    bytes_hex = content.encode('utf-8').hex()
    
    # Compute file hash
    content_hash = hashlib.sha256(content.encode('utf-8')).hexdigest()
    
    # Empty state hash (SHA-256 of empty bytes)
    empty_state = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    
    receipt = {
        "version": "TRS-1.0",
        "files": [
            {
                "path": filename,
                "size": len(content.encode('utf-8')),
                "sha256": content_hash,
                "content_sha256": content_hash
            }
        ],
        "steps": [
            {
                "step": 0,
                "pre_state_sha256": empty_state,
                "opcode": "EMIT_BYTES",
                "args": {
                    "path": filename,
                    "offset": 0,
                    "bytes_hex": bytes_hex
                },
                "axioms": ["initial_emit"],
                "oracle_reply": {"status": "sat", "witness": null},
                "mu_bits": len(content) * 8.0,  # Simple estimate
                "post_state_sha256": "computed_by_verifier"
            }
        ],
        "global_digest": "computed_by_verifier",
        "kernel_sha256": content_hash,
        "timestamp": "2025-11-04T00:00:00Z",
        "sig_scheme": "ed25519",
        "key_id": "local-demo",
        "public_key": "<hex public key>",
        "signature": "<hex signature>"
    }

    return receipt

# Example usage
if __name__ == "__main__":
    content = """#!/usr/bin/env python3
print("This file was created from a Thiele receipt!")
"""
    
    receipt = create_simple_receipt("my_script.py", content)
    
    # Save receipt
    with open("my_script_receipt.json", "w") as f:
        json.dump(receipt, f, indent=2)
    
    print("✓ Receipt created: my_script_receipt.json (signature placeholder)")
    print(f"✓ File SHA256: {receipt['files'][0]['sha256']}")
    print("⚠️  Sign the receipt with tools/sign_receipts.py before distributing it")
```

Run it:

```bash
python3 create_receipt.py my_script.py --output my_script_receipt.json \
    --sign path/to/private.key --key-id local-demo
# Output:
# ✓ Receipt created: my_script_receipt.json
# ✓ Receipt signed with Ed25519
# ✓ Public key: 254b57576959e5fb...
```

To verify a freshly signed receipt outside the repository trust manifest, supply the signer’s public key:

```bash
python3 tools/verify_trs10.py my_script_receipt.json \
    --trusted-pubkey 254b57576959e5fb37d087a60d5a72bb75dcf82240cbd62577059695dda0ebea
```

If you maintain many receipts, place a `trust_manifest.json` alongside them (or use `receipts/trust_manifest.json`) to map `key_id` values to trusted public keys.

## Using Receipts in Your Project

### Integration Pattern 1: Zero-Trust Distribution

Instead of shipping binaries or source, ship receipts.

**Project Structure:**

```
my-project/
├── receipts/
│   ├── main_app_receipt.json
│   ├── lib1_receipt.json
│   └── lib2_receipt.json
├── verifier/
│   └── replay.py  (170-line verifier from Thiele)
├── install.sh
└── README.md
```

**install.sh:**

```bash
#!/bin/bash
# Zero-trust installation script

echo "Installing MyProject from cryptographic receipts..."

# Verify and materialize all components
python3 verifier/replay.py receipts/main_app_receipt.json
python3 verifier/replay.py receipts/lib1_receipt.json
python3 verifier/replay.py receipts/lib2_receipt.json

# Verify hashes
expected_hash="77cd06bbb84ed8ccc4fd2949c555a8ba553d56629c88338435db65ce4d079135"
actual_hash=$(sha256sum main_app.py | cut -d' ' -f1)

if [ "$expected_hash" = "$actual_hash" ]; then
    echo "✓ Installation verified!"
    echo "✓ All files cryptographically verified"
    chmod +x main_app.py
else
    echo "✗ Verification failed!"
    exit 1
fi
```

**Benefits:**
- Users verify cryptographic proofs before execution
- No trust in download channels needed
- Tamper-evident: any modification breaks verification
- Reproducible: same receipts always produce identical files

### Integration Pattern 2: Build Verification

Prove that your build process is deterministic and tamper-free.

```python
# build_with_receipt.py
import subprocess
import json
import hashlib

def build_and_receipt(source_file, output_binary):
    """
    Build a binary and create a receipt proving the build.
    """
    
    # Compile
    subprocess.run(["gcc", "-o", output_binary, source_file], check=True)
    
    # Read the binary
    with open(output_binary, "rb") as f:
        binary_content = f.read()
    
    # Create receipt
    receipt = {
        "version": "TRS-1.0",
        "build_info": {
            "compiler": "gcc",
            "source": source_file,
            "output": output_binary
        },
        "files": [{
            "path": output_binary,
            "size": len(binary_content),
            "sha256": hashlib.sha256(binary_content).hexdigest()
        }],
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "sig_scheme": "none",
        "signature": ""
    }
    
    # Save receipt
    receipt_path = f"{output_binary}_receipt.json"
    with open(receipt_path, "w") as f:
        json.dump(receipt, f, indent=2)
    
    print(f"✓ Built: {output_binary}")
    print(f"✓ Receipt: {receipt_path}")
    print(f"✓ SHA256: {receipt['files'][0]['sha256']}")
    
    return receipt

# Usage
build_and_receipt("main.c", "main")
```

### Integration Pattern 3: Dependency Verification

Create a receipt-based package manager.

```python
# receipt_package_manager.py
import json
import os

class ReceiptPackageManager:
    def __init__(self, receipts_dir="~/.receipts"):
        self.receipts_dir = os.path.expanduser(receipts_dir)
        os.makedirs(self.receipts_dir, exist_ok=True)
    
    def install(self, receipt_url):
        """Install a package from its receipt."""
        # Download receipt
        receipt_path = self._download(receipt_url)
        
        # Verify receipt
        print(f"Verifying {receipt_path}...")
        subprocess.run([
            "python3", "verifier/replay.py", receipt_path
        ], check=True)
        
        # Load receipt to get file info
        with open(receipt_path) as f:
            receipt = json.load(f)
        
        print("✓ Installation complete!")
        for file in receipt.get("files", []):
            print(f"  - {file['path']} (SHA256: {file['sha256'][:16]}...)")
    
    def verify(self, package_name):
        """Verify an installed package."""
        receipt_path = os.path.join(self.receipts_dir, f"{package_name}.json")
        
        with open(receipt_path) as f:
            receipt = json.load(f)
        
        for file_info in receipt.get("files", []):
            path = file_info["path"]
            expected_hash = file_info["sha256"]
            
            with open(path, "rb") as f:
                actual_hash = hashlib.sha256(f.read()).hexdigest()
            
            if actual_hash == expected_hash:
                print(f"✓ {path}")
            else:
                print(f"✗ {path} - HASH MISMATCH!")
                return False
        
        return True

# Usage
pm = ReceiptPackageManager()
pm.install("https://example.com/packages/mylib_v1.0_receipt.json")
pm.verify("mylib")
```

## Practical Examples

### Example 1: Multi-File Project Receipt

```json
{
  "version": "TRS-1.0",
  "files": [
    {
      "path": "src/main.py",
      "size": 1234,
      "sha256": "abc123...",
      "content_sha256": "abc123..."
    },
    {
      "path": "src/utils.py",
      "size": 567,
      "sha256": "def456...",
      "content_sha256": "def456..."
    },
    {
      "path": "README.md",
      "size": 890,
      "sha256": "ghi789...",
      "content_sha256": "ghi789..."
    }
  ],
  "global_digest": "computed_from_all_files",
  "timestamp": "2025-11-04T12:00:00Z",
  "sig_scheme": "ed25519",
  "signature": "base64_signature_here"
}
```

### Example 2: Executable Binary Receipt

```json
{
  "version": "TRS-0",
  "steps": [
    {
      "step": 0,
      "opcode": "EMIT_BYTES",
      "args": {
        "path": "my_program",
        "offset": 0,
        "bytes_hex": "7f454c46..." 
      },
      "mu_bits": 16384.0,
      "pre_state_sha256": "e3b0c44...",
      "post_state_sha256": "abc123..."
    },
    {
      "step": 1,
      "opcode": "MAKE_EXEC",
      "args": {"path": "my_program"},
      "mu_bits": 1.0,
      "pre_state_sha256": "abc123...",
      "post_state_sha256": "def456..."
    },
    {
      "step": 2,
      "opcode": "ASSERT_SHA256",
      "args": {
        "path": "my_program",
        "sha256": "expected_hash_of_binary"
      },
      "mu_bits": 256.0,
      "pre_state_sha256": "def456...",
      "post_state_sha256": "def456..."
    }
  ]
}
```

## Receipt Schema Reference

### TRS-0 (Step-Based)

Complete step-by-step construction:

```json
{
  "version": "TRS-0",
  "steps": [
    {
      "step": <integer>,
      "pre_state_sha256": "<hex_hash>",
      "opcode": "EMIT_BYTES|MAKE_EXEC|ASSERT_SHA256",
      "args": { /* opcode-specific */ },
      "axioms": ["<logical_axiom>", ...],
      "oracle_reply": {
        "status": "sat|unsat|unknown",
        "witness": <any>
      },
      "mu_bits": <float>,
      "post_state_sha256": "<hex_hash>"
    }
  ],
  "global_digest": "<hex_hash>",
  "sig_scheme": "ed25519|none",
  "signature": "<hex_or_empty>"
}
```

### TRS-1.0 (File-Based)

Simplified file-level receipts:

```json
{
  "version": "TRS-1.0",
  "files": [
    {
      "path": "<string>",
      "size": <integer>,
      "sha256": "<hex_hash>",
      "content_sha256": "<hex_hash>"
    }
  ],
  "global_digest": "<hex_hash>",
  "kernel_sha256": "<hex_hash>",
  "timestamp": "<ISO8601>",
  "sig_scheme": "ed25519|none",
  "signature": "<base64_or_empty>"
}
```

### Opcodes

#### EMIT_BYTES
Emit bytes to a file.

**Args:**
- `path` (string): Target file path
- `offset` (integer): Byte offset (≥0)
- `bytes_hex` (string): Hex-encoded bytes (lowercase)

#### MAKE_EXEC
Mark file as executable.

**Args:**
- `path` (string): File path

#### ASSERT_SHA256
Verify file hash.

**Args:**
- `path` (string): File path
- `sha256` (string): Expected hash (hex, lowercase)

## Advanced Topics

### Signing Receipts

Add cryptographic signatures:

```python
import ed25519

# Generate keys
signing_key, verifying_key = ed25519.create_keypair()

# Sign receipt
global_digest = compute_global_digest(receipt['steps'])
signature = signing_key.sign(bytes.fromhex(global_digest))

receipt['sig_scheme'] = 'ed25519'
receipt['signature'] = signature.hex()
```

### Receipt Composition

Combine multiple receipts:

```python
def compose_receipts(receipt1, receipt2):
    """Combine two receipts into one."""
    return {
        "version": "TRS-1.0",
        "files": receipt1["files"] + receipt2["files"],
        "components": [
            {"name": "component1", "digest": receipt1["global_digest"]},
            {"name": "component2", "digest": receipt2["global_digest"]}
        ]
    }
```

### μ-Bit Optimization

Minimize information-theoretic costs:

```python
# Instead of emitting entire file at once (high μ-cost):
"mu_bits": len(file_content) * 8

# Emit in structured chunks (lower μ-cost):
# - Emit headers (predictable structure)
# - Emit code blocks (partitioned by function)
# - Use compression-aware encoding
```

## FAQ

**Q: Do I need the full Thiele Machine to use receipts?**

A: No! The verifier is only ~170 lines of Python. You can use receipts with just the verifier script.

**Q: Can I use receipts for closed-source software?**

A: Yes! Receipts prove *how* something was built, not *what* the source code is. You can ship receipts for binaries without revealing source.

**Q: Are receipts specific to Python?**

A: No! Receipts can verify any file type: binaries, scripts, data files, documents, etc.

**Q: How do receipts compare to package signatures?**

A: Signatures prove *who* built something. Receipts prove *how* it was built, step by step. Use both together for maximum security.

**Q: What's the performance overhead?**

A: Verification is fast (milliseconds for small files, seconds for large projects). Receipt generation is the expensive part, but only done once by the developer.

**Q: Can receipts be forged?**

A: No, assuming cryptographic hash functions (SHA-256) are secure. Any tampering changes the hashes and breaks verification.

## Next Steps

1. **Try the browser demos:**
   - [Receipt Verifier](https://sethirus.github.io/The-Thiele-Machine/) - Verify receipts in your browser
   - [Proof-Install](https://sethirus.github.io/The-Thiele-Machine/demos/install.html) - See receipts in action
   - [Trusting Trust](https://sethirus.github.io/The-Thiele-Machine/demos/trusting-trust.html) - Defeat compiler backdoors

2. **Read the specs:**
   - [`receipt_schema.md`](receipt_schema.md) - Complete TRS-0 specification
   - [`spec/receipt-v1.1.md`](../spec/receipt-v1.1.md) - TRS-1.1 enhancements

3. **Explore examples:**
   - [`examples/`](../examples/) - Sample receipts
   - [`receipts/`](../receipts/) - Real-world receipts

4. **Build something:**
   - Create receipts for your own projects
   - Integrate receipt verification into your CI/CD
   - Contribute improvements to the Thiele ecosystem

## Summary

**Thiele receipts replace trust with cryptographic proof.**

Instead of asking users to trust:
- ❌ Your build server
- ❌ Your download channel  
- ❌ Your compiler
- ❌ Your word that "this binary matches that source"

You provide:
- ✅ Mathematical proof of construction
- ✅ Deterministic verification (anyone can check)
- ✅ Tamper-evident audit trail
- ✅ Information-theoretic cost accounting

**Start using receipts today to build more trustworthy software.**

---

*Part of the [Thiele Machine](https://github.com/sethirus/The-Thiele-Machine) project - Zero servers. Zero trust. Only mathematics.*
