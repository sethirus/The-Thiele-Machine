#!/bin/bash
#
# Generic Thiele Receipt Generator Script
# 
# This script can be used in any CI/CD system or locally to generate
# cryptographic receipts for your build artifacts.
#
# Usage:
#   ./generate-receipts.sh [options]
#
# Options:
#   --project DIR        Project directory for auto-discovery (default: .)
#   --output DIR         Output directory for receipts (default: receipts)
#   --sign KEY_FILE      Sign receipts with Ed25519 key
#   --metadata JSON      Include metadata in receipts
#   --verify             Verify receipts after creation
#   --help               Show this help message
#
# Examples:
#   ./generate-receipts.sh
#   ./generate-receipts.sh --project /path/to/project
#   ./generate-receipts.sh --sign signing.key --verify
#

set -e  # Exit on error

# Default values
PROJECT_DIR="."
OUTPUT_DIR="receipts"
SIGN_KEY=""
METADATA=""
VERIFY=false
VERBOSE=false

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Helper functions
log_info() {
    echo -e "${BLUE}ℹ${NC} $1"
}

log_success() {
    echo -e "${GREEN}✓${NC} $1"
}

log_error() {
    echo -e "${RED}✗${NC} $1" >&2
}

log_warning() {
    echo -e "${YELLOW}⚠${NC} $1"
}

show_help() {
    grep '^#' "$0" | sed 's/^# \?//' | grep -v '^!/'
    exit 0
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --project)
            PROJECT_DIR="$2"
            shift 2
            ;;
        --output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --sign)
            SIGN_KEY="$2"
            shift 2
            ;;
        --metadata)
            METADATA="$2"
            shift 2
            ;;
        --verify)
            VERIFY=true
            shift
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --help|-h)
            show_help
            ;;
        *)
            log_error "Unknown option: $1"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Check if Python is available
if ! command -v python3 &> /dev/null; then
    log_error "Python 3 is required but not installed"
    exit 1
fi

# Check Python version
PYTHON_VERSION=$(python3 -c 'import sys; print(".".join(map(str, sys.version_info[:2])))')
REQUIRED_VERSION="3.11"
if ! python3 -c "import sys; exit(0 if sys.version_info >= (3, 11) else 1)"; then
    log_error "Python 3.11+ is required (found $PYTHON_VERSION)"
    exit 1
fi

log_info "Using Python $PYTHON_VERSION"

# Check if Thiele tools are installed
if ! python3 -c "import create_receipt" 2>/dev/null; then
    log_warning "Thiele tools not found in Python path"
    log_info "Installing Thiele Receipt tools..."
    
    # Try to install from GitHub
    if pip install git+https://github.com/sethirus/The-Thiele-Machine.git >/dev/null 2>&1; then
        log_success "Installed Thiele tools"
    else
        # Fallback: check if we're in the repository
        if [ -f "create_receipt.py" ]; then
            log_info "Using local create_receipt.py"
        else
            log_error "Cannot find or install Thiele tools"
            echo "Please install with: pip install git+https://github.com/sethirus/The-Thiele-Machine.git"
            exit 1
        fi
    fi
fi

# Install optional dependencies if signing is requested
if [ -n "$SIGN_KEY" ]; then
    log_info "Signing requested, checking dependencies..."
    if ! python3 -c "import nacl" 2>/dev/null; then
        log_info "Installing PyNaCl for signing..."
        pip install PyNaCl >/dev/null 2>&1
    fi
    if ! python3 -c "import cryptography" 2>/dev/null; then
        log_info "Installing cryptography..."
        pip install cryptography >/dev/null 2>&1
    fi
fi

# Validate project directory
if [ ! -d "$PROJECT_DIR" ]; then
    log_error "Project directory not found: $PROJECT_DIR"
    exit 1
fi

PROJECT_DIR=$(cd "$PROJECT_DIR" && pwd)  # Get absolute path
log_info "Project directory: $PROJECT_DIR"

# Build the command
CMD="python3"

# Check if create_receipt.py is in current directory
if [ -f "create_receipt.py" ]; then
    CMD="$CMD create_receipt.py"
else
    CMD="$CMD -m create_receipt"
fi

CMD="$CMD --project \"$PROJECT_DIR\""
CMD="$CMD --output \"$OUTPUT_DIR\""

if [ -n "$SIGN_KEY" ]; then
    if [ ! -f "$SIGN_KEY" ]; then
        log_error "Signing key not found: $SIGN_KEY"
        exit 1
    fi
    CMD="$CMD --sign \"$SIGN_KEY\""
fi

if [ -n "$METADATA" ]; then
    CMD="$CMD --metadata '$METADATA'"
fi

# Execute receipt generation
log_info "Generating receipts..."
if [ "$VERBOSE" = true ]; then
    echo "Command: $CMD"
fi

if eval $CMD; then
    log_success "Receipts generated successfully"
else
    log_error "Failed to generate receipts"
    exit 1
fi

# List generated receipts
if [ -d "$OUTPUT_DIR" ]; then
    RECEIPT_COUNT=$(find "$OUTPUT_DIR" -name "*.receipt.json" -type f ! -name "MANIFEST.receipt.json" | wc -l)
    log_success "Created $RECEIPT_COUNT receipt(s) in $OUTPUT_DIR/"
    
    if [ "$VERBOSE" = true ]; then
        ls -lh "$OUTPUT_DIR"/*.receipt.json 2>/dev/null || true
    fi
    
    # Check for manifest
    if [ -f "$OUTPUT_DIR/MANIFEST.receipt.json" ]; then
        log_success "Created MANIFEST.receipt.json index"
    fi
fi

# Optional verification
if [ "$VERIFY" = true ]; then
    log_info "Verifying receipts..."
    
    VERIFY_CMD="python3"
    if [ -f "verifier/replay.py" ]; then
        VERIFY_CMD="$VERIFY_CMD verifier/replay.py"
    else
        VERIFY_CMD="$VERIFY_CMD -m verifier.replay"
    fi
    
    VERIFIED=0
    FAILED=0
    
    for receipt in "$OUTPUT_DIR"/*.receipt.json; do
        if [ "$receipt" = "$OUTPUT_DIR/MANIFEST.receipt.json" ]; then
            continue
        fi
        
        if [ "$VERBOSE" = true ]; then
            echo "Verifying: $receipt"
        fi
        
        if $VERIFY_CMD "$receipt" >/dev/null 2>&1; then
            VERIFIED=$((VERIFIED + 1))
        else
            FAILED=$((FAILED + 1))
            log_error "Verification failed: $receipt"
        fi
    done
    
    if [ $FAILED -eq 0 ]; then
        log_success "All $VERIFIED receipt(s) verified successfully"
    else
        log_error "Verification failed for $FAILED receipt(s)"
        exit 1
    fi
fi

# Print usage instructions
echo ""
log_success "Receipt generation complete!"
echo ""
echo "Verification options for users:"
echo ""
echo "  Browser (easiest):"
echo "    Visit: https://sethirus.github.io/The-Thiele-Machine/verify.html"
echo "    Drag and drop any .receipt.json file"
echo ""
echo "  Command line:"
echo "    pip install git+https://github.com/sethirus/The-Thiele-Machine.git"
echo "    thiele-verify $OUTPUT_DIR/artifact.receipt.json"
echo ""

exit 0
