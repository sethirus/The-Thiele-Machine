//! ZK Prover for Thiele Receipts
//! 
//! Usage: zk-prove --receipt dist/receipt.json --out dist/zkproof.json

use anyhow::Result;
use clap::Parser;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "zk-prove")]
#[command(about = "Generate ZK proof for Thiele receipt")]
struct Args {
    /// Path to input receipt.json
    #[arg(short, long)]
    receipt: PathBuf,
    
    /// Path to output zkproof.json
    #[arg(short, long)]
    out: PathBuf,
}

#[derive(Debug, Serialize, Deserialize)]
struct Receipt {
    version: String,
    global_digest: String,
    files: Vec<FileEntry>,
}

#[derive(Debug, Serialize, Deserialize)]
struct FileEntry {
    path: String,
    content_sha256: String,
    executable: Option<bool>,
}

#[derive(Debug, Serialize)]
struct ZkProof {
    version: &'static str,
    guest_image_id: String,
    manifest_sha256: String,
    merkle_root: String,
    files: Vec<FileDigest>,
    zk_receipt: String,
}

#[derive(Debug, Serialize)]
struct FileDigest {
    path: String,
    sha256: String,
}

fn compute_sha256(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    format!("{:x}", hasher.finalize())
}

fn compute_merkle_root(file_hashes: &[String]) -> String {
    if file_hashes.is_empty() {
        return compute_sha256(b"");
    }
    
    let mut current_level = file_hashes.to_vec();
    
    while current_level.len() > 1 {
        let mut next_level = Vec::new();
        
        for chunk in current_level.chunks(2) {
            let combined = if chunk.len() == 2 {
                format!("{}{}", chunk[0], chunk[1])
            } else {
                chunk[0].clone()
            };
            next_level.push(compute_sha256(combined.as_bytes()));
        }
        
        current_level = next_level;
    }
    
    current_level[0].clone()
}

fn prove(receipt_bytes: Vec<u8>) -> Result<(String, Vec<FileDigest>, String, String)> {
    // Parse receipt
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes)?;
    
    // Compute manifest SHA256
    let manifest_sha256 = compute_sha256(&receipt_bytes);
    
    // Extract file digests
    let file_digests: Vec<FileDigest> = receipt.files.iter()
        .map(|f| FileDigest {
            path: f.path.clone(),
            sha256: f.content_sha256.clone(),
        })
        .collect();
    
    // Compute merkle root
    let file_hashes: Vec<String> = receipt.files.iter()
        .map(|f| f.content_sha256.clone())
        .collect();
    let merkle_root = compute_merkle_root(&file_hashes);
    
    // In production, this would run the guest program in a ZK VM
    // and generate a real cryptographic proof
    // For now, create a placeholder proof
    let zk_receipt_data = serde_json::json!({
        "proof_type": "placeholder",
        "manifest_sha256": manifest_sha256,
        "merkle_root": merkle_root,
        "timestamp": chrono::Utc::now().to_rfc3339(),
    });
    
    let zk_receipt_b64 = base64::engine::general_purpose::STANDARD
        .encode(serde_json::to_vec(&zk_receipt_data)?);
    
    Ok((manifest_sha256, file_digests, merkle_root, zk_receipt_b64))
}

fn main() -> Result<()> {
    let args = Args::parse();
    
    // Read receipt
    let receipt_bytes = fs::read(&args.receipt)?;
    
    println!("Generating ZK proof for receipt: {}", args.receipt.display());
    
    // Generate proof
    let (manifest_sha256, files, merkle_root, zk_receipt_b64) = prove(receipt_bytes)?;
    
    // Create output structure
    let out = ZkProof {
        version: "TRS-ZK-1",
        guest_image_id: "<PLACEHOLDER_IMAGE_ID>".to_string(),
        manifest_sha256,
        merkle_root,
        files,
        zk_receipt: zk_receipt_b64,
    };
    
    // Write output
    fs::write(&args.out, serde_json::to_vec_pretty(&out)?)?;
    
    println!("✓ ZK proof written to: {}", args.out.display());
    println!("  Manifest SHA256: {}", out.manifest_sha256);
    println!("  Merkle root: {}", out.merkle_root);
    println!("  Files: {}", out.files.len());
    
    Ok(())
}
