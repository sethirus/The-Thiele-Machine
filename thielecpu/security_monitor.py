#!/usr/bin/env python3
"""
Security Monitoring and Responsible Use Tracker for Thiele CPU

This script monitors usage of the Thiele CPU package and logs activities
for security and responsible disclosure purposes.
"""

import json
import hashlib
import datetime
from pathlib import Path
from typing import Dict, Any
import warnings

class SecurityMonitor:
    """Monitor and log Thiele CPU usage for security purposes."""

    def __init__(self, log_file: Path = None):
        self.log_file = log_file or Path("security_log.json")
        self.session_id = hashlib.sha256(str(datetime.datetime.now().timestamp()).encode()).hexdigest()[:16]

    def log_activity(self, activity: str, details: Dict[str, Any] = None):
        """Log a security-relevant activity."""
        entry = {
            "timestamp": datetime.datetime.now().isoformat(),
            "session_id": self.session_id,
            "activity": activity,
            "details": details or {},
            "warning": "⚠️  Thiele CPU usage logged for security monitoring"
        }

        # Append to log file
        try:
            if self.log_file.exists():
                with open(self.log_file, 'r') as f:
                    logs = json.load(f)
            else:
                logs = []

            logs.append(entry)

            with open(self.log_file, 'w') as f:
                json.dump(logs, f, indent=2)

        except Exception as e:
            warnings.warn(f"Failed to log security activity: {e}", UserWarning)

    def check_responsible_use(self):
        """Display responsible use guidelines."""
        guidelines = """
        🚨 THIELE CPU RESPONSIBLE USE GUIDELINES 🚨

        This technology can break RSA and other cryptographic systems.

        ALLOWED USES:
        - Academic research into computational complexity
        - Defensive security research and vulnerability assessment
        - Development of improved cryptographic systems
        - Formal verification and proof systems

        PROHIBITED USES:
        - Breaking encryption without authorization
        - Cryptanalysis for malicious purposes
        - Undermining digital security infrastructure
        - Commercial exploitation without security review

        If you're unsure about your use case, contact the maintainers.

        Your usage is being logged for security purposes.
        """

        print(guidelines)
        self.log_activity("responsible_use_check_displayed")

# Global monitor instance
_monitor = SecurityMonitor()

def log_usage(activity: str, **details):
    """Log usage activity for security monitoring."""
    _monitor.log_activity(activity, details)

def display_security_warning():
    """Display comprehensive security warning."""
    _monitor.check_responsible_use()

# Auto-display warning on import
display_security_warning()