package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"os"

	"github.com/sethirus/The-Thiele-Machine/cmd/thiele-replay-go/internal/canonical"
	"github.com/sethirus/The-Thiele-Machine/cmd/thiele-replay-go/internal/replay"
)

func main() {
	printDigest := flag.Bool("print-digest", false, "Print global digest after replay")
	verify := flag.Bool("verify", false, "Verify digest matches expected")
	expected := flag.String("expected", "", "Expected global digest (for verification)")
	flag.Parse()

	if flag.NArg() < 1 {
		fmt.Fprintf(os.Stderr, "Usage: %s [options] <receipt.json>\n", os.Args[0])
		flag.PrintDefaults()
		os.Exit(1)
	}

	receiptPath := flag.Arg(0)

	// Read receipt
	data, err := os.ReadFile(receiptPath)
	if err != nil {
		log.Fatalf("Failed to read receipt: %v", err)
	}

	// Parse receipt
	var receipt replay.Receipt
	if err := json.Unmarshal(data, &receipt); err != nil {
		log.Fatalf("Failed to parse receipt: %v", err)
	}

	// Verify canonical JSON
	if err := canonical.VerifyCanonical(data); err != nil {
		log.Fatalf("Receipt is not in canonical form: %v", err)
	}

	// Replay receipt
	fmt.Printf("Replaying receipt: %s\n", receiptPath)
	fmt.Printf("  Version: %s\n", receipt.Version)
	fmt.Printf("  Files: %d\n", len(receipt.Files))

	result, err := replay.ReplayReceipt(&receipt)
	if err != nil {
		log.Fatalf("Replay failed: %v", err)
	}

	fmt.Printf("  Global digest: %s\n", result.GlobalDigest)

	if *printDigest {
		fmt.Println(result.GlobalDigest)
	}

	if *verify {
		if *expected == "" {
			log.Fatal("--expected required when using --verify")
		}
		if result.GlobalDigest != *expected {
			log.Fatalf("Digest mismatch!\n  Expected: %s\n  Got: %s", *expected, result.GlobalDigest)
		}
		fmt.Println("✓ Digest verified")
	}
}
