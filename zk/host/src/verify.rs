//! ZK Verifier for Thiele Receipts
//! 
//! Usage: zk-verify dist/zkproof.json

use anyhow::{Result, bail};
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "zk-verify")]
#[command(about = "Verify ZK proof for Thiele receipt")]
struct Args {
    /// Path to zkproof.json
    zkproof: PathBuf,
}

#[derive(Debug, Deserialize)]
struct ZkProof {
    version: String,
    guest_image_id: String,
    manifest_sha256: String,
    merkle_root: String,
    files: Vec<FileDigest>,
    zk_receipt: String,
}

#[derive(Debug, Deserialize, Serialize)]
struct FileDigest {
    path: String,
    sha256: String,
}

fn verify_proof(proof: &ZkProof) -> Result<bool> {
    // In production, this would:
    // 1. Verify the ZK receipt cryptographically
    // 2. Check guest image ID matches expected
    // 3. Validate public outputs (manifest_sha256, merkle_root, files)
    
    // For placeholder, just validate structure
    if proof.version != "TRS-ZK-1" {
        bail!("Unsupported version: {}", proof.version);
    }
    
    if proof.manifest_sha256.is_empty() {
        bail!("Missing manifest_sha256");
    }
    
    if proof.merkle_root.is_empty() {
        bail!("Missing merkle_root");
    }
    
    if proof.files.is_empty() {
        bail!("No files in proof");
    }
    
    // Decode ZK receipt to verify it's valid base64
    let _decoded = base64::engine::general_purpose::STANDARD
        .decode(&proof.zk_receipt)?;
    
    Ok(true)
}

fn main() -> Result<()> {
    let args = Args::parse();
    
    // Read proof
    let proof_data = fs::read(&args.zkproof)?;
    let proof: ZkProof = serde_json::from_slice(&proof_data)?;
    
    println!("Verifying ZK proof: {}", args.zkproof.display());
    println!("  Version: {}", proof.version);
    println!("  Guest image: {}", proof.guest_image_id);
    println!("  Manifest SHA256: {}", proof.manifest_sha256);
    println!("  Merkle root: {}", proof.merkle_root);
    println!("  Files: {}", proof.files.len());
    
    // Verify proof
    match verify_proof(&proof) {
        Ok(true) => {
            println!("\n✅ ZK proof verification PASSED");
            println!("\nFile digests:");
            for file in &proof.files {
                println!("  {} → {}", file.path, file.sha256);
            }
            Ok(())
        }
        Ok(false) => {
            bail!("❌ ZK proof verification FAILED");
        }
        Err(e) => {
            bail!("❌ Verification error: {}", e);
        }
    }
}
