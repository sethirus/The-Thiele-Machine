#!/usr/bin/env python3
"""Thiele Machine Copilot Bridge - Real-time LLM verification service.

This module provides the SINGLE canonical verification service for GitHub Copilot.
It implements the thesis-compliant verification architecture with:

    1. Merkle-linked receipt chain (Chapter 7.7.1)
    2. Real μ-cost from VM ledger
    3. Z3/SMT LASSERT certificates
    4. Trust boundary enforcement

Usage:
    # Start the verification server
    python -m thielecpu.copilot_bridge serve
    
    # Check server status
    python -m thielecpu.copilot_bridge status
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import socket
import sys
import time
from dataclasses import dataclass, field, asdict
from http.server import HTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from typing import Any, Dict, List, Optional
from datetime import datetime

# Add repo root to path
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from thielecpu.state import State
from thielecpu.vm import VM
from thielecpu.thesis_verify import (
    ThesisVerifier,
    TrustedTestCase,
    TrustLevel,
    thesis_verify_endpoint,
    ThesisReceiptChain,
)
from thielecpu.structural_verify import (
    StructuralVerifier,
    StructuralResult,
    VerificationCategory,
)

# Default configuration
DEFAULT_HOST = "127.0.0.1"
DEFAULT_PORT = 7331  # "THEL" in leet speak
RECEIPTS_DIR = REPO_ROOT / "receipts" / "copilot_verified"


@dataclass
class VerificationSession:
    """Tracks a verification session with accumulated receipts."""
    session_id: str
    started_at: float
    mu_budget: float
    mu_consumed: float = 0.0
    verified_count: int = 0
    failed_count: int = 0
    receipts: List[Dict[str, Any]] = field(default_factory=list)
    
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class ThieleCopilotBridge:
    """Real-time verification bridge for GitHub Copilot integration.
    
    This is the SINGLE canonical verification implementation.
    """
    
    def __init__(self, mu_budget: float = 10000.0):
        self.vm = VM(State())
        self.verifier = ThesisVerifier(self.vm)
        self.structural_verifier = StructuralVerifier()
        
        # Session tracking
        self.session = VerificationSession(
            session_id=hashlib.sha256(str(time.time()).encode()).hexdigest()[:16],
            started_at=time.time(),
            mu_budget=mu_budget,
        )
        
        # Ensure receipts directory exists
        RECEIPTS_DIR.mkdir(parents=True, exist_ok=True)
    
    def get_status(self) -> Dict[str, Any]:
        """Get current bridge status and statistics."""
        return {
            "status": "running",
            "session": self.session.to_dict(),
            "statistics": {
                "total_verifications": self.session.verified_count + self.session.failed_count,
                "verified": self.session.verified_count,
                "failed": self.session.failed_count,
                "verification_rate": (
                    self.session.verified_count / max(1, self.session.verified_count + self.session.failed_count)
                ),
                "mu_consumed": self.session.mu_consumed,
                "mu_remaining": self.session.mu_budget - self.session.mu_consumed,
                "mu_budget": self.session.mu_budget,
                "uptime_sec": time.time() - self.session.started_at,
            },
            "receipts_dir": str(RECEIPTS_DIR),
        }
    
    def get_session_receipts(self) -> List[Dict[str, Any]]:
        """Get all receipts from current session."""
        return self.session.receipts
    
    def verify_text(self, text: str, source: str = "copilot") -> Dict[str, Any]:
        """Verify arbitrary text using structural verification.
        
        Args:
            text: The text to verify (e.g., Copilot response)
            source: Source identifier
        
        Returns:
            Verification result dictionary
        """
        result = self.structural_verifier.verify_text(text)
        
        # Update session stats
        self.session.verified_count += result.structurally_verified
        self.session.failed_count += result.structurally_failed
        self.session.mu_consumed += result.total_mu_cost
        
        return result.to_dict()


# Global bridge instance
_bridge: Optional[ThieleCopilotBridge] = None


def get_bridge() -> ThieleCopilotBridge:
    """Get or create the global bridge instance."""
    global _bridge
    if _bridge is None:
        _bridge = ThieleCopilotBridge()
    return _bridge


class VerificationHandler(BaseHTTPRequestHandler):
    """HTTP request handler for verification service."""
    
    def log_message(self, format, *args):
        """Suppress default logging."""
        pass
    
    def _send_json(self, data: Dict[str, Any], status: int = 200):
        """Send JSON response."""
        response = json.dumps(data, indent=2).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", len(response))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(response)
    
    def do_OPTIONS(self):
        """Handle CORS preflight."""
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()
    
    def do_GET(self):
        """Handle GET requests."""
        bridge = get_bridge()
        
        if self.path == "/status":
            self._send_json(bridge.get_status())
        elif self.path == "/receipts":
            self._send_json({"receipts": bridge.get_session_receipts()})
        elif self.path == "/health":
            self._send_json({"status": "healthy", "timestamp": datetime.now().isoformat()})
        else:
            self._send_json({"error": "Unknown endpoint", "available": ["/status", "/receipts", "/health"]}, 404)
    
    def do_POST(self):
        """Handle POST requests."""
        bridge = get_bridge()
        
        # Read request body
        content_length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(content_length).decode() if content_length > 0 else "{}"
        
        try:
            data = json.loads(body)
        except json.JSONDecodeError as e:
            self._send_json({"error": f"Invalid JSON: {str(e)}"}, 400)
            return
        
        if self.path == "/verify":
            # THESIS-COMPLIANT VERIFICATION - THE SINGLE CANONICAL IMPLEMENTATION
            # 
            # This implements the thesis specification:
            # 
            # 1. MERKLE-LINKED RECEIPT CHAIN (Chapter 7.7.1)
            #    - pre_state_hash → instruction → post_state_hash
            #    - chain_link = SHA256(previous_receipt)
            # 
            # 2. REAL μ-COST FROM VM LEDGER
            #    - mu_discovery + mu_execution + mu_information
            #    - Information gain: Δμ ≥ log₂(Ω) - log₂(Ω')
            # 
            # 3. Z3/SMT LASSERT CERTIFICATES
            #    - Real SMT solving with proof models
            # 
            # 4. TRUST BOUNDARY ENFORCEMENT
            #    - Test cases MUST have trust_level != "untrusted"
            #    - LLM-generated tests are REJECTED
            
            # Check for text-only structural verification
            text = data.get("text", "")
            if text and not data.get("code"):
                result = bridge.verify_text(text, source=data.get("source", "copilot"))
                self._send_json(result)
                return
            
            # Full code verification with test cases
            result = thesis_verify_endpoint(data)
            
            # Update session stats
            if result.get("success"):
                bridge.session.verified_count += 1
            else:
                bridge.session.failed_count += 1
            bridge.session.mu_consumed += result.get("mu_cost", {}).get("total", 0)
            
            # Save receipt
            if result.get("success") and result.get("receipt_chain"):
                receipt_data = {
                    "verification": result,
                    "timestamp": datetime.now().isoformat(),
                    "session_id": bridge.session.session_id,
                }
                receipt_path = RECEIPTS_DIR / f"{bridge.session.session_id}_{bridge.session.verified_count}.json"
                receipt_path.write_text(json.dumps(receipt_data, indent=2))
                result["receipt_path"] = str(receipt_path)
                bridge.session.receipts.append(receipt_data)
            
            self._send_json(result)
        
        else:
            self._send_json({
                "error": "Unknown endpoint",
                "available_post": ["/verify"],
                "available_get": ["/status", "/receipts", "/health"],
            }, 404)


def run_server(host: str = DEFAULT_HOST, port: int = DEFAULT_PORT):
    """Run the verification server."""
    server = HTTPServer((host, port), VerificationHandler)
    print(f"╔════════════════════════════════════════════════════════════════╗")
    print(f"║     THIELE MACHINE - VERIFICATION SERVICE                     ║")
    print(f"╠════════════════════════════════════════════════════════════════╣")
    print(f"║  Server: http://{host}:{port}                              ║")
    print(f"║                                                                ║")
    print(f"║  THESIS-COMPLIANT VERIFICATION (Single Canonical Mode)        ║")
    print(f"║                                                                ║")
    print(f"║  Features:                                                    ║")
    print(f"║    • Merkle-linked receipt chain (Chapter 7.7.1)              ║")
    print(f"║    • Real μ-cost from VM ledger                               ║")
    print(f"║    • Z3/SMT LASSERT certificates                              ║")
    print(f"║    • Trust boundary enforcement                               ║")
    print(f"║    • Information-theoretic cost: Δμ ≥ log₂(Ω) - log₂(Ω')      ║")
    print(f"║                                                                ║")
    print(f"╠════════════════════════════════════════════════════════════════╣")
    print(f"║  ENDPOINTS:                                                   ║")
    print(f"║    POST /verify  - Verify code with Merkle receipt chain      ║")
    print(f"║    GET  /status  - Service status and statistics              ║")
    print(f"║    GET  /receipts - Get session receipts                      ║")
    print(f"║    GET  /health  - Health check                               ║")
    print(f"╚════════════════════════════════════════════════════════════════╝")
    print(f"\n✓ Verification service ready. Press Ctrl+C to stop.\n")
    
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n\nShutting down...")
        server.shutdown()


def check_server_status(host: str = DEFAULT_HOST, port: int = DEFAULT_PORT) -> Dict[str, Any]:
    """Check if the verification server is running."""
    import urllib.request
    import urllib.error
    
    try:
        url = f"http://{host}:{port}/health"
        with urllib.request.urlopen(url, timeout=2) as response:
            return json.loads(response.read().decode())
    except (urllib.error.URLError, socket.timeout):
        return {"status": "not_running", "error": f"Server not reachable at {host}:{port}"}


def main():
    """CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Thiele Machine Copilot Verification Bridge",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Start the verification server
  python -m thielecpu.copilot_bridge serve
  
  # Check if server is running
  python -m thielecpu.copilot_bridge status
        """
    )
    
    subparsers = parser.add_subparsers(dest="command", help="Command")
    
    # serve command
    serve_parser = subparsers.add_parser("serve", help="Start verification server")
    serve_parser.add_argument("--host", default=DEFAULT_HOST, help=f"Host (default: {DEFAULT_HOST})")
    serve_parser.add_argument("--port", type=int, default=DEFAULT_PORT, help=f"Port (default: {DEFAULT_PORT})")
    
    # status command
    status_parser = subparsers.add_parser("status", help="Check server status")
    status_parser.add_argument("--host", default=DEFAULT_HOST, help=f"Host (default: {DEFAULT_HOST})")
    status_parser.add_argument("--port", type=int, default=DEFAULT_PORT, help=f"Port (default: {DEFAULT_PORT})")
    
    args = parser.parse_args()
    
    if args.command == "serve":
        run_server(args.host, args.port)
    elif args.command == "status":
        result = check_server_status(args.host, args.port)
        print(json.dumps(result, indent=2))
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
