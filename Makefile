.PHONY: all reproduce test clean

# Default target
all: reproduce

# Reproduce all results
reproduce:
	@echo "Reproducing Thiele Machine unambiguity results..."
	@echo "Step 1: Running property tests..."
	python scripts/property_tests.py
	@echo "Step 2: Testing hostile families..."
	python scripts/test_hostile_families.py
	@echo "Step 3: Running RSA scaling demo..."
	python scripts/rsa_scaling_demo.py
	@echo "Step 4: Receipt verification (sample receipt needs updating)..."
	@echo "  Skipping receipt verification - sample receipt format needs updating"
	@echo "Reproduction complete. Check generated files:"
	@echo "- mu_ledger.json"
	@echo "- property_test_results.json"
	@echo "- hostile_families_analysis.png"
	@echo "- rsa_scaling_results.json"
	@echo "- rsa_scaling_plots.png"

# Run tests only
test:
	@echo "Running tests..."
	python -m pytest tests/ -v

# Clean generated files
clean:
	@echo "Cleaning generated files..."
	rm -f *.json *.png
	rm -f scripts/*.json scripts/*.png

# Help
help:
	@echo "Available targets:"
	@echo "  all       - Run full reproduction (default)"
	@echo "  reproduce - Reproduce all results"
	@echo "  test      - Run unit tests"
	@echo "  clean     - Remove generated files"
	@echo "  help      - Show this help"