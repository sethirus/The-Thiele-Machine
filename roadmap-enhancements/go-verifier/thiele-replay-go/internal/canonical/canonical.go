package canonical

import (
	"bytes"
	"encoding/json"
	"fmt"
	"unicode/utf8"

	"golang.org/x/text/unicode/norm"
)

// VerifyCanonical checks if JSON bytes are in canonical form:
// - Sorted keys
// - No whitespace except structural
// - UTF-8 NFC normalization
func VerifyCanonical(data []byte) error {
	// Check UTF-8 validity
	if !utf8.Valid(data) {
		return fmt.Errorf("invalid UTF-8")
	}

	// Parse and re-serialize with canonical settings
	var v interface{}
	if err := json.Unmarshal(data, &v); err != nil {
		return fmt.Errorf("invalid JSON: %w", err)
	}

	canonical, err := json.Marshal(v)
	if err != nil {
		return fmt.Errorf("failed to canonicalize: %w", err)
	}

	// Check if original matches canonical form
	if !bytes.Equal(data, canonical) {
		return fmt.Errorf("JSON is not canonical")
	}

	// Check NFC normalization
	normalized := norm.NFC.Bytes(data)
	if !bytes.Equal(data, normalized) {
		return fmt.Errorf("JSON is not NFC normalized")
	}

	return nil
}

// Canonicalize converts arbitrary JSON to canonical form
func Canonicalize(data []byte) ([]byte, error) {
	var v interface{}
	if err := json.Unmarshal(data, &v); err != nil {
		return nil, fmt.Errorf("invalid JSON: %w", err)
	}

	canonical, err := json.Marshal(v)
	if err != nil {
		return nil, fmt.Errorf("failed to canonicalize: %w", err)
	}

	// Apply NFC normalization
	return norm.NFC.Bytes(canonical), nil
}
