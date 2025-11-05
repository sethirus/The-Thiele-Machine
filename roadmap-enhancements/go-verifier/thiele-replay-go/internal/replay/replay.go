package replay

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"sort"
)

// Receipt represents a TRS-0 receipt
type Receipt struct {
	Version      string      `json:"version"`
	GlobalDigest string      `json:"global_digest"`
	Files        []FileEntry `json:"files"`
}

// FileEntry represents a file in the receipt
type FileEntry struct {
	Path           string `json:"path"`
	ContentSHA256  string `json:"content_sha256"`
	Executable     *bool  `json:"executable,omitempty"`
	Size           *int64 `json:"size,omitempty"`
}

// ReplayResult contains the result of replaying a receipt
type ReplayResult struct {
	GlobalDigest string
	FileCount    int
	FilePaths    []string
}

// ReplayReceipt verifies and replays a receipt
func ReplayReceipt(receipt *Receipt) (*ReplayResult, error) {
	// Validate version
	if receipt.Version != "TRS-0-INLINE" && receipt.Version != "TRS-0" {
		return nil, fmt.Errorf("unsupported version: %s", receipt.Version)
	}

	// Validate files
	if len(receipt.Files) == 0 {
		return nil, fmt.Errorf("no files in receipt")
	}

	// Compute global digest from files
	globalDigest := computeGlobalDigest(receipt.Files)

	// Verify it matches declared digest
	if receipt.GlobalDigest != "" && globalDigest != receipt.GlobalDigest {
		return nil, fmt.Errorf("digest mismatch: expected %s, got %s",
			receipt.GlobalDigest, globalDigest)
	}

	// Collect file paths
	paths := make([]string, len(receipt.Files))
	for i, f := range receipt.Files {
		paths[i] = f.Path
	}

	return &ReplayResult{
		GlobalDigest: globalDigest,
		FileCount:    len(receipt.Files),
		FilePaths:    paths,
	}, nil
}

// computeGlobalDigest calculates the global digest from file entries
func computeGlobalDigest(files []FileEntry) string {
	hasher := sha256.New()

	// Sort files by path for determinism
	sorted := make([]FileEntry, len(files))
	copy(sorted, files)
	sort.Slice(sorted, func(i, j int) bool {
		return sorted[i].Path < sorted[j].Path
	})

	// Hash concatenation of path + content_sha256 + executable flag
	for _, f := range sorted {
		hasher.Write([]byte(f.Path))
		hasher.Write([]byte(f.ContentSHA256))
		
		if f.Executable != nil && *f.Executable {
			hasher.Write([]byte("executable"))
		}
	}

	return hex.EncodeToString(hasher.Sum(nil))
}
