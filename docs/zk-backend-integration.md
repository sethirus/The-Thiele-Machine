# ZK Backend Integration Guide

This guide explains how to integrate a real ZK backend (RISC Zero or SP1) into the Thiele Machine's existing ZK infrastructure.

## Current State

The infrastructure is complete and ready for ZK backend integration:

✅ **Guest program**: `zk/guest/src/main.rs` - Computes digest, merkle root, file hashes  
✅ **Host prover**: `zk/host/src/main.rs` - CLI tool `zk-prove`  
✅ **Host verifier**: `zk/host/src/verify.rs` - CLI tool `zk-verify`  
✅ **Python bridge**: `thielecpu/zk_bridge.py` - Python integration  
✅ **Web UI**: `web/zk.html` - Browser verification

**What's needed**: Replace placeholder ZK proof generation with real cryptographic proofs.

## Integration Options

### Option 1: RISC Zero (Recommended)

**Why**: Production-ready, excellent documentation, active development.

**Dependencies**:
```toml
# Add to zk/host/Cargo.toml
[dependencies]
risc0-zkvm = "1.0"
risc0-build = "1.0"

# Add to zk/guest/Cargo.toml
[dependencies]
risc0-zkvm = { version = "1.0", default-features = false }
```

**Guest Program Changes**:
```rust
// zk/guest/src/main.rs
use risc0_zkvm::guest::env;

fn main() {
    // Read receipt from host
    let receipt_bytes: Vec<u8> = env::read();
    
    // Parse and compute (existing logic)
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes).unwrap();
    let manifest_sha256 = compute_sha256(&receipt_bytes);
    let merkle_root = compute_merkle_root(&file_hashes);
    
    // Commit public outputs
    env::commit(&manifest_sha256);
    env::commit(&merkle_root);
    env::commit(&receipt.files.len());
}
```

**Host Prover Changes**:
```rust
// zk/host/src/main.rs
use risc0_zkvm::{default_prover, ExecutorEnv};

fn prove(receipt_bytes: Vec<u8>) -> Result<(String, Vec<FileDigest>, String, Vec<u8>)> {
    // Build executor environment
    let env = ExecutorEnv::builder()
        .write(&receipt_bytes)?
        .build()?;
    
    // Generate proof
    let prover = default_prover();
    let receipt = prover.prove(env, GUEST_ELF)?;
    
    // Extract public outputs
    let manifest_sha256: String = receipt.journal.decode()?;
    let merkle_root: String = receipt.journal.decode()?;
    let file_count: usize = receipt.journal.decode()?;
    
    // Serialize proof
    let proof_bytes = bincode::serialize(&receipt)?;
    
    Ok((manifest_sha256, files, merkle_root, proof_bytes))
}
```

**Host Verifier Changes**:
```rust
// zk/host/src/verify.rs
use risc0_zkvm::Receipt;

fn verify_proof(proof: &ZkProof) -> Result<bool> {
    // Decode proof
    let proof_bytes = base64::decode(&proof.zk_receipt)?;
    let receipt: Receipt = bincode::deserialize(&proof_bytes)?;
    
    // Verify proof
    receipt.verify(GUEST_IMAGE_ID)?;
    
    // Verify public outputs match
    let manifest_sha256: String = receipt.journal.decode()?;
    if manifest_sha256 != proof.manifest_sha256 {
        bail!("Manifest SHA256 mismatch");
    }
    
    Ok(true)
}
```

### Option 2: SP1

**Why**: Newer, faster proof generation, growing ecosystem.

**Dependencies**:
```toml
# Add to zk/host/Cargo.toml
[dependencies]
sp1-sdk = "1.0"

# Add to zk/guest/Cargo.toml
[dependencies]
sp1-zkvm = "1.0"
```

**Guest Program Changes**:
```rust
// zk/guest/src/main.rs
#![no_main]
sp1_zkvm::entrypoint!(main);

use sp1_zkvm::io;

pub fn main() {
    // Read input
    let receipt_bytes = io::read_vec();
    
    // Compute (existing logic)
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes).unwrap();
    let manifest_sha256 = compute_sha256(&receipt_bytes);
    let merkle_root = compute_merkle_root(&file_hashes);
    
    // Commit outputs
    io::commit(&manifest_sha256);
    io::commit(&merkle_root);
}
```

**Host Integration**:
```rust
// zk/host/src/main.rs
use sp1_sdk::{ProverClient, SP1Stdin};

fn prove(receipt_bytes: Vec<u8>) -> Result<(String, Vec<FileDigest>, String, Vec<u8>)> {
    let client = ProverClient::new();
    
    let mut stdin = SP1Stdin::new();
    stdin.write_vec(receipt_bytes);
    
    let (proof, output) = client.prove(GUEST_ELF, stdin).run()?;
    
    // Extract outputs
    let manifest_sha256 = output.read::<String>();
    let merkle_root = output.read::<String>();
    
    let proof_bytes = bincode::serialize(&proof)?;
    
    Ok((manifest_sha256, files, merkle_root, proof_bytes))
}
```

## Build Instructions

### RISC Zero

```bash
cd zk/guest
cargo build --release

cd ../host
cargo build --release --features risc0
```

### SP1

```bash
cd zk
sp1-build --bin zk-guest

cd host
cargo build --release --features sp1
```

## Testing

```bash
# Generate proof
cd zk/host
./target/release/zk-prove --receipt ../../bootstrap_receipts/050_kernel_emit.json --out test.zkproof.json

# Verify proof
./target/release/zk-verify test.zkproof.json

# Test corruption detection
cp ../../bootstrap_receipts/050_kernel_emit.json corrupt.json
sed -i 's/77cd06bb/deadbeef/' corrupt.json  # Corrupt one byte
./target/release/zk-prove --receipt corrupt.json --out corrupt.zkproof.json
./target/release/zk-verify corrupt.zkproof.json  # Should FAIL
```

## Web Integration

Update `web/zk.html` to use real ZK verification:

```javascript
// Option 1: WASM verifier (compile Rust to WASM)
import init, { verify_proof } from './zk_verifier.js';

async function verifyZkProof(zkProof) {
    await init();
    const result = verify_proof(zkProof.zk_receipt);
    return result;
}

// Option 2: Server-side verification
async function verifyZkProof(zkProof) {
    const response = await fetch('/api/verify-zk', {
        method: 'POST',
        body: JSON.stringify(zkProof)
    });
    return await response.json();
}
```

For true client-side verification, compile the Rust verifier to WASM:

```bash
cd zk/host
cargo install wasm-pack
wasm-pack build --target web --out-dir ../../web/pkg
```

## Expected Performance

### RISC Zero
- **Proof generation**: 30-60 seconds for bootstrap receipt
- **Verification**: <1 second
- **Proof size**: ~200 KB

### SP1
- **Proof generation**: 10-30 seconds for bootstrap receipt
- **Verification**: <500 ms
- **Proof size**: ~100 KB

## DoD Checklist

- [ ] Dependencies added to Cargo.toml
- [ ] Guest program reads receipt, computes outputs, commits to journal
- [ ] Host prover generates real cryptographic proofs
- [ ] Host verifier checks proof validity
- [ ] `zk-verify dist/zkproof.json` passes on bootstrap receipt
- [ ] Corrupting one byte in receipt → proof generation fails or verify fails
- [ ] Web UI verifies proofs (WASM or API)
- [ ] CI builds and tests ZK components
- [ ] Documentation updated with example proofs

## Resources

**RISC Zero**:
- [Documentation](https://dev.risczero.com/)
- [Examples](https://github.com/risc0/risc0/tree/main/examples)
- [Discord](https://discord.gg/risczero)

**SP1**:
- [Documentation](https://docs.succinct.xyz/)
- [Examples](https://github.com/succinctlabs/sp1/tree/main/examples)
- [Telegram](https://t.me/succinct_xyz)

## Notes

The placeholder implementation is intentionally structured to minimize changes needed for real ZK integration. The main work is:

1. Add dependencies
2. Update guest to use ZK VM primitives (env::read/commit or io::read/commit)
3. Update host to use actual prover/verifier APIs
4. Replace placeholder proof serialization with real proof bytes
5. Test thoroughly

All the infrastructure (CLI tools, Python bridge, web UI) remains unchanged.
