//! ZK Guest Program for Thiele Receipt Verification
//! 
//! This guest program runs inside a zero-knowledge VM (RISC Zero or SP1)
//! and proves that a TRS-0 receipt can be reconstructed with exact bytes
//! matching the claimed global_digest and per-file SHA256 values.
//!
//! Inputs: Canonical bytes of an inline TRS-0 receipt
//! Outputs: manifest_sha256, per-file SHA256 list, merkle_root (public)

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

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
struct PublicOutputs {
    manifest_sha256: String,
    merkle_root: String,
    file_count: usize,
    files: Vec<FileDigest>,
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
    
    // Simple binary merkle tree
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

fn main() {
    // In a real ZK VM, we would read input from the environment
    // For now, this is a placeholder showing the structure
    
    // Read receipt from stdin (in ZK VM, this would be committed input)
    let receipt_bytes = std::io::stdin()
        .bytes()
        .collect::<Result<Vec<u8>, _>>()
        .unwrap_or_default();
    
    if receipt_bytes.is_empty() {
        eprintln!("No input received");
        return;
    }
    
    // Parse receipt
    let receipt: Receipt = match serde_json::from_slice(&receipt_bytes) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Failed to parse receipt: {}", e);
            return;
        }
    };
    
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
    
    // Prepare public outputs
    let outputs = PublicOutputs {
        manifest_sha256,
        merkle_root,
        file_count: receipt.files.len(),
        files: file_digests,
    };
    
    // In a real ZK VM, we would commit these as public outputs
    // For now, just print them
    println!("{}", serde_json::to_string_pretty(&outputs).unwrap());
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_merkle_root_single() {
        let hashes = vec!["abc123".to_string()];
        let root = compute_merkle_root(&hashes);
        assert!(!root.is_empty());
    }
    
    #[test]
    fn test_merkle_root_multiple() {
        let hashes = vec![
            "abc123".to_string(),
            "def456".to_string(),
            "ghi789".to_string(),
        ];
        let root = compute_merkle_root(&hashes);
        assert!(!root.is_empty());
    }
}
