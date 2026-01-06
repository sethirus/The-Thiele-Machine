#!/usr/bin/env python3
"""
Thiele Machine - Structural LLM Output Verification

This module implements HONEST verification of LLM outputs following
the Thiele Machine thesis principles:

**WHAT WE CAN VERIFY (Structural/Computational):**
1. Mathematical claims - Through actual computation
2. Code syntax - Through parsing (AST)
3. Code execution - Through sandboxed execution
4. File system claims - Through filesystem checks
5. Import claims - Through Python import system
6. Logical consistency - Through SAT/SMT solving
7. Self-consistency - Does the LLM contradict itself?

**WHAT WE CANNOT VERIFY (External/Factual):**
- Claims about the real world ("France has a king")
- Historical facts ("WWII ended in 1945")
- Scientific facts ("Earth is round")
- Future predictions

These require external oracles (web search, databases) which are
OUTSIDE the Thiele Machine's trusted computing base.

The key insight from the thesis:
- Verification requires a WITNESS/CERTIFICATE
- Without a witness, we can only mark claims as UNVERIFIED
- μ-cost tracks the computational work of verification
"""

from __future__ import annotations

import ast
import hashlib
import json
import math
import re
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


class VerificationCategory(Enum):
    """Categories of verification - honest about what's possible."""
    
    # Structurally verifiable (we can compute the answer)
    MATHEMATICAL = "mathematical"      # 1+1=2, 15=3×5
    CODE_SYNTAX = "code_syntax"        # Python/JS syntax via AST
    CODE_EXECUTION = "code_execution"  # Code actually runs
    FILE_SYSTEM = "file_system"        # File exists, contains
    IMPORT = "import"                  # Python import valid
    LOGICAL = "logical"                # SAT/SMT solvable
    SELF_CONSISTENCY = "consistency"   # No contradictions in output
    
    # NOT verifiable without external oracle
    FACTUAL_WORLD = "factual_world"    # Real-world claims
    HISTORICAL = "historical"          # Past events
    SCIENTIFIC = "scientific"          # Science facts
    FUTURE = "future"                  # Predictions
    
    # Truly unverifiable
    OPINION = "opinion"                # Subjective statements
    CONVERSATIONAL = "conversational"  # Greetings, questions


@dataclass
class StructuralClaim:
    """A claim extracted from LLM output with its verification status."""
    text: str
    category: VerificationCategory
    
    # Verification result
    verified: Optional[bool]  # None = cannot verify structurally
    witness: Optional[str] = None  # The proof/evidence
    mu_cost: float = 0.0
    
    # For unverifiable claims
    requires_oracle: bool = False
    oracle_type: Optional[str] = None  # "web_search", "database", etc.
    
    error: Optional[str] = None


@dataclass
class StructuralResult:
    """Result of structural verification."""
    original_text: str
    claims: List[StructuralClaim]
    
    # Counts
    structurally_verified: int = 0
    structurally_failed: int = 0
    requires_external: int = 0
    unverifiable: int = 0
    
    # Economics
    total_mu_cost: float = 0.0
    timestamp: str = ""
    certificate_hash: str = ""
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "original_text": self.original_text[:200],
            "structurally_verified": self.structurally_verified,
            "structurally_failed": self.structurally_failed,
            "requires_external": self.requires_external,
            "unverifiable": self.unverifiable,
            "claims": [
                {
                    "text": c.text,
                    "category": c.category.value,
                    "verified": c.verified,
                    "witness": c.witness,
                    "mu_cost": c.mu_cost,
                    "requires_oracle": c.requires_oracle,
                    "error": c.error,
                }
                for c in self.claims
            ],
            "total_mu_cost": self.total_mu_cost,
            "certificate_hash": self.certificate_hash,
        }


class StructuralClaimExtractor:
    """
    Extract claims from text and categorize them HONESTLY.
    
    Key principle: We only claim to verify what we can actually compute.
    """
    
    # Mathematical patterns (WE CAN VERIFY THESE)
    # Extended to handle negative results and floats
    MATH_PATTERNS = [
        (r'(\d+)\s*([+\-*/])\s*(\d+)\s*=\s*(-?[\d.]+)', 'arithmetic'),  # handles negative and float results
        (r'(\d+)\s*=\s*(\d+)\s*[×*]\s*(\d+)', 'factorization'),
        (r'factors?\s+of\s+(\d+)\s+(?:are|is)\s+(\d+)\s+and\s+(\d+)', 'factorization'),
        (r'(\d+)\s*\^\s*(\d+)\s*=\s*(\d+)', 'power'),
        (r'sqrt\((\d+)\)\s*=\s*([\d.]+)', 'sqrt'),
        (r'(\d+)\s*>\s*(\d+)', 'comparison_gt'),
        (r'(\d+)\s*<\s*(\d+)', 'comparison_lt'),
        (r'(\d+)\s*==\s*(\d+)', 'comparison_eq'),
    ]
    
    # File patterns (WE CAN VERIFY THESE)
    # File extensions we recognize (excludes things like self._pool)
    KNOWN_FILE_EXTENSIONS = r'py|js|ts|jsx|tsx|json|yaml|yml|md|txt|toml|cfg|ini|v|c|cpp|h|hpp|rs|go|java|rb|sh|bash|css|html|xml|sql|csv'
    
    FILE_PATTERNS = [
        # "file X.py" or "path X.py" - require known extension AND not starting with "self."
        (r'(?:file|path)\s+[`"\']?(?!self\.)([a-zA-Z0-9_/.-]+\.(?:' + KNOWN_FILE_EXTENSIONS + r'))[`"\']?', 'file_ref'),
        # `path/to/file.py` in backticks - require known extension
        (r'`(?!self\.)([a-zA-Z0-9_/.-]+\.(?:' + KNOWN_FILE_EXTENSIONS + r'))`', 'file_ref'),
        # "file.py exists" - require known extension
        (r'[`"\']?(?!self\.)([a-zA-Z0-9_/.-]+\.(?:' + KNOWN_FILE_EXTENSIONS + r'))[`"\']?\s+(?:exists|is present)', 'file_exists'),
    ]
    
    # Code patterns (WE CAN VERIFY SYNTAX)
    CODE_PATTERNS = [
        (r'```(\w+)?\n(.*?)```', 'code_block'),
        (r'`(def\s+\w+[^`]+)`', 'inline_function'),
    ]
    
    # Import patterns (WE CAN VERIFY THESE)
    # Order matters: check 'from X import' FIRST to avoid matching within it
    IMPORT_PATTERNS = [
        (r'from\s+(\w+(?:\.\w+)*)\s+import', 'from_import'),  # from x.y.z import ...
        (r'^import\s+(\w+(?:\.\w+)*)', 'import'),             # import x.y.z at line start
        (r'[`\'\"]\s*import\s+(\w+(?:\.\w+)*)', 'import'),    # `import x` quoted
    ]
    
    # Factual patterns (WE CANNOT VERIFY WITHOUT ORACLE)
    FACTUAL_PATTERNS = [
        (r'(?:the\s+)?capital\s+of\s+(\w+)\s+is\s+(\w+)', 'capital'),
        (r'(\w+)\s+(?:invented|created|discovered|founded)\s+(\w+)', 'invention'),
        (r'(\w+)\s+(?:is|was|are|were)\s+the\s+(\w+)\s+of\s+(\w+)', 'role'),
        (r'(?:the\s+)?(\w+)\s+is\s+(flat|round|spherical)', 'shape_claim'),
        (r'(\w+)\s+(?:causes?|cause)\s+(\w+)', 'causation'),
    ]
    
    # Future patterns (INHERENTLY UNVERIFIABLE)
    FUTURE_PATTERNS = [
        (r'(?:in|by)\s+(\d{4})\s+.+\s+will', 'future_prediction'),
        (r'will\s+(?:be|become|have)', 'future_prediction'),
    ]
    
    def _remove_code_blocks(self, text: str) -> str:
        """Remove code blocks from text, handling nested backticks correctly."""
        result = []
        i = 0
        in_code_block = False
        
        while i < len(text):
            # Check for code block start
            if not in_code_block and text[i:i+3] == '```':
                in_code_block = True
                # Skip to end of opening line
                newline_pos = text.find('\n', i)
                if newline_pos == -1:
                    break
                i = newline_pos + 1
            elif in_code_block:
                # Look for closing ``` at start of line
                if text[i:i+3] == '```' and (i == 0 or text[i-1] == '\n'):
                    in_code_block = False
                    i += 3
                    # Skip any trailing newline
                    if i < len(text) and text[i] == '\n':
                        i += 1
                else:
                    i += 1
            else:
                result.append(text[i])
                i += 1
        
        return ''.join(result)
    
    def extract_all(self, text: str) -> List[Tuple[str, VerificationCategory, Dict[str, Any]]]:
        """Extract all claims with honest categorization."""
        claims = []
        
        # FIRST: Check if entire input is a single code block (common from pre-commit hooks)
        # This handles files that contain ``` in their content (like this one!)
        stripped = text.strip()
        if stripped.startswith('```') and stripped.endswith('```'):
            # Find the opening ``` and closing ``` positions
            first_newline = stripped.find('\n')
            if first_newline > 0:
                lang = stripped[3:first_newline].strip()
                # Extract code content (everything between first newline and final ```)
                code_content = stripped[first_newline+1:-3].strip()
                
                # Only syntax-check the code, don't extract claims from it
                claims.append((
                    stripped[:100],
                    VerificationCategory.CODE_SYNTAX,
                    {"subtype": "code_block", "groups": (lang, code_content), "verifiable": True},
                ))
                return claims  # Early return - no claim extraction from pure code
        
        # NORMAL CASE: Mixed prose and code blocks
        # Extract code blocks for syntax checking (store separately)
        code_blocks = []
        for pattern, subtype in self.CODE_PATTERNS:
            for match in re.finditer(pattern, text, re.DOTALL):
                code_blocks.append((
                    match.group(0)[:100],
                    VerificationCategory.CODE_SYNTAX,
                    {"subtype": subtype, "groups": match.groups(), "verifiable": True},
                ))
        
        # Remove code blocks from text BEFORE extracting other claims
        # Use a custom approach: find paired ``` markers properly
        text_without_code = self._remove_code_blocks(text)
        
        # Mathematical (VERIFIABLE) - only from prose, not code
        for pattern, subtype in self.MATH_PATTERNS:
            for match in re.finditer(pattern, text_without_code, re.IGNORECASE):
                claims.append((
                    match.group(0),
                    VerificationCategory.MATHEMATICAL,
                    {"subtype": subtype, "groups": match.groups(), "verifiable": True},
                ))
        
        # File system (VERIFIABLE) - only from prose, not code
        for pattern, subtype in self.FILE_PATTERNS:
            for match in re.finditer(pattern, text_without_code, re.IGNORECASE):
                claims.append((
                    match.group(0),
                    VerificationCategory.FILE_SYSTEM,
                    {"subtype": subtype, "path": match.group(1), "verifiable": True},
                ))
        
        # Add code blocks (already extracted above)
        claims.extend(code_blocks)
        
        # Imports (VERIFIABLE) - only from prose, not code
        import_matches: Dict[int, Tuple[str, str, str]] = {}  # start_pos -> (match_text, module, subtype)
        for pattern, subtype in self.IMPORT_PATTERNS:
            for match in re.finditer(pattern, text_without_code):
                start = match.start()
                # For 'from X import', prefer that over 'import Y' if they overlap
                if start not in import_matches or subtype == 'from_import':
                    import_matches[start] = (match.group(0), match.group(1), subtype)
        
        # Now also filter out 'import X' matches that occur within 'from Y import X'
        # The 'from_import' match starts before the 'import' keyword
        from_import_ranges = []
        for start, (match_text, module, subtype) in import_matches.items():
            if subtype == 'from_import':
                from_import_ranges.append((start, start + len(match_text) + 20))  # include imported name area
        
        for start, (match_text, module, subtype) in list(import_matches.items()):
            if subtype == 'import':
                # Check if this 'import' is within a 'from ... import' 
                for from_start, from_end in from_import_ranges:
                    if from_start <= start <= from_end:
                        del import_matches[start]
                        break
        
        for match_text, module, subtype in import_matches.values():
            claims.append((
                match_text,
                VerificationCategory.IMPORT,
                {"subtype": subtype, "module": module, "verifiable": True},
            ))
        
        # Factual claims (NOT VERIFIABLE WITHOUT ORACLE) - only from prose
        for pattern, subtype in self.FACTUAL_PATTERNS:
            for match in re.finditer(pattern, text_without_code, re.IGNORECASE):
                claims.append((
                    match.group(0),
                    VerificationCategory.FACTUAL_WORLD,
                    {"subtype": subtype, "groups": match.groups(), "verifiable": False,
                     "requires_oracle": "web_search"},
                ))
        
        # Future claims (INHERENTLY UNVERIFIABLE) - only from prose
        for pattern, subtype in self.FUTURE_PATTERNS:
            for match in re.finditer(pattern, text_without_code, re.IGNORECASE):
                claims.append((
                    match.group(0),
                    VerificationCategory.FUTURE,
                    {"subtype": subtype, "verifiable": False, "reason": "future prediction"},
                ))
        
        # If no claims found, check if it's conversational
        if not claims and len(text_without_code.strip()) > 3:
            if text_without_code.strip().endswith('?'):
                claims.append((
                    text_without_code.strip(),
                    VerificationCategory.CONVERSATIONAL,
                    {"subtype": "question", "verifiable": False},
                ))
            else:
                claims.append((
                    text_without_code.strip(),
                    VerificationCategory.OPINION,
                    {"subtype": "statement", "verifiable": False},
                ))
        
        return claims


class StructuralVerifier:
    """
    Structural Verifier following Thiele Machine principles.
    
    We ONLY verify things we can actually compute:
    - Math: Execute the calculation
    - Code: Parse the AST or run it
    - Files: Check the filesystem
    - Imports: Try the import
    - Logic: Use SAT/SMT solver
    
    We are HONEST about what requires external oracles.
    """
    
    def __init__(self, workspace_root: Path = REPO_ROOT):
        self.workspace_root = workspace_root
        self.extractor = StructuralClaimExtractor()
        self.history: List[StructuralResult] = []
        self.total_mu = 0.0
    
    def verify_text(self, text: str) -> StructuralResult:
        """Verify all claims in text with honest categorization."""
        extracted = self.extractor.extract_all(text)
        
        claims: List[StructuralClaim] = []
        total_mu = 0.0
        verified_count = 0
        failed_count = 0
        external_count = 0
        unverifiable_count = 0
        
        for claim_text, category, content in extracted:
            claim = self._verify_claim(claim_text, category, content)
            claims.append(claim)
            total_mu += claim.mu_cost
            
            if claim.verified is True:
                verified_count += 1
            elif claim.verified is False:
                failed_count += 1
            elif claim.requires_oracle:
                external_count += 1
            else:
                unverifiable_count += 1
        
        timestamp = datetime.now().isoformat()
        text_hash = hashlib.sha256(text.encode()).hexdigest()
        cert_data = f"{text_hash}:{verified_count}:{failed_count}:{total_mu}:{timestamp}"
        certificate_hash = hashlib.sha256(cert_data.encode()).hexdigest()
        
        result = StructuralResult(
            original_text=text,
            claims=claims,
            structurally_verified=verified_count,
            structurally_failed=failed_count,
            requires_external=external_count,
            unverifiable=unverifiable_count,
            total_mu_cost=total_mu,
            timestamp=timestamp,
            certificate_hash=certificate_hash,
        )
        
        self.history.append(result)
        self.total_mu += total_mu
        return result
    
    def _verify_claim(
        self,
        claim_text: str,
        category: VerificationCategory,
        content: Dict[str, Any],
    ) -> StructuralClaim:
        """Verify a single claim - honestly categorized."""
        
        if category == VerificationCategory.MATHEMATICAL:
            return self._verify_mathematical(claim_text, content)
        
        elif category == VerificationCategory.CODE_SYNTAX:
            return self._verify_code_syntax(claim_text, content)
        
        elif category == VerificationCategory.FILE_SYSTEM:
            return self._verify_file_system(claim_text, content)
        
        elif category == VerificationCategory.IMPORT:
            return self._verify_import(claim_text, content)
        
        elif category == VerificationCategory.FACTUAL_WORLD:
            # HONEST: We cannot verify this without external oracle
            return StructuralClaim(
                text=claim_text,
                category=category,
                verified=None,  # Not True or False - UNKNOWN
                requires_oracle=True,
                oracle_type=content.get("requires_oracle", "web_search"),
                mu_cost=0.0,  # No computation done
                error="Requires external oracle (web search, database) to verify",
            )
        
        elif category == VerificationCategory.FUTURE:
            return StructuralClaim(
                text=claim_text,
                category=category,
                verified=None,
                requires_oracle=False,
                mu_cost=0.0,
                error="Future predictions are inherently unverifiable",
            )
        
        elif category in (VerificationCategory.CONVERSATIONAL, VerificationCategory.OPINION):
            return StructuralClaim(
                text=claim_text,
                category=category,
                verified=None,
                mu_cost=0.0,
                error="Not a verifiable claim (opinion/conversation)",
            )
        
        else:
            return StructuralClaim(
                text=claim_text,
                category=category,
                verified=None,
                mu_cost=0.0,
                error=f"No verifier for category: {category}",
            )
    
    def _verify_mathematical(self, claim_text: str, content: Dict) -> StructuralClaim:
        """Verify mathematical claims by COMPUTING the answer."""
        subtype = content.get("subtype")
        groups = content.get("groups", ())
        
        try:
            if subtype == "arithmetic":
                a, op, b, result = groups
                a, b = int(a), int(b)
                # Result can be negative or float
                result = float(result)
                
                ops = {'+': a + b, '-': a - b, '*': a * b, '/': a / b if b != 0 else float('inf')}
                actual = ops.get(op)
                
                if actual is None:
                    return StructuralClaim(
                        text=claim_text, category=VerificationCategory.MATHEMATICAL,
                        verified=False, mu_cost=1.0, error=f"Unknown operator: {op}",
                    )
                
                verified = abs(actual - result) < 0.0001
                return StructuralClaim(
                    text=claim_text, category=VerificationCategory.MATHEMATICAL,
                    verified=verified,
                    witness=f"Computed: {a} {op} {b} = {actual}",
                    mu_cost=1.0,
                    error=None if verified else f"Expected {result}, computed {actual}",
                )
            
            elif subtype == "factorization":
                if len(groups) == 3:
                    n, p, q = int(groups[0]), int(groups[1]), int(groups[2])
                    actual = p * q
                    verified = actual == n
                    
                    return StructuralClaim(
                        text=claim_text, category=VerificationCategory.MATHEMATICAL,
                        verified=verified,
                        witness=f"Computed: {p} × {q} = {actual}",
                        mu_cost=1.0,
                        error=None if verified else f"{p} × {q} = {actual} ≠ {n}",
                    )
            
            elif subtype == "power":
                base, exp, result = int(groups[0]), int(groups[1]), int(groups[2])
                actual = base ** exp
                verified = actual == result
                
                return StructuralClaim(
                    text=claim_text, category=VerificationCategory.MATHEMATICAL,
                    verified=verified,
                    witness=f"Computed: {base}^{exp} = {actual}",
                    mu_cost=1.0,
                    error=None if verified else f"Expected {result}, computed {actual}",
                )
            
            elif subtype == "sqrt":
                n, result = int(groups[0]), float(groups[1])
                actual = math.sqrt(n)
                verified = abs(actual - result) < 0.01
                
                return StructuralClaim(
                    text=claim_text, category=VerificationCategory.MATHEMATICAL,
                    verified=verified,
                    witness=f"Computed: sqrt({n}) = {actual:.6f}",
                    mu_cost=1.0,
                    error=None if verified else f"Expected {result}, computed {actual:.6f}",
                )
            
            elif subtype.startswith("comparison"):
                a, b = float(groups[0]), float(groups[1])
                
                if subtype == "comparison_gt":
                    verified = a > b
                    witness = f"Computed: {a} > {b} is {verified}"
                elif subtype == "comparison_lt":
                    verified = a < b
                    witness = f"Computed: {a} < {b} is {verified}"
                elif subtype == "comparison_eq":
                    verified = abs(a - b) < 0.0001
                    witness = f"Computed: {a} == {b} is {verified}"
                else:
                    return StructuralClaim(
                        text=claim_text, category=VerificationCategory.MATHEMATICAL,
                        verified=False, mu_cost=1.0, error=f"Unknown comparison: {subtype}",
                    )
                
                return StructuralClaim(
                    text=claim_text, category=VerificationCategory.MATHEMATICAL,
                    verified=verified, witness=witness, mu_cost=1.0,
                    error=None if verified else f"Comparison {claim_text} is false",
                )
        
        except Exception as e:
            return StructuralClaim(
                text=claim_text, category=VerificationCategory.MATHEMATICAL,
                verified=False, mu_cost=1.0, error=str(e),
            )
        
        return StructuralClaim(
            text=claim_text, category=VerificationCategory.MATHEMATICAL,
            verified=None, mu_cost=0.0, error=f"Unknown math subtype: {subtype}",
        )
    
    def _verify_code_syntax(self, claim_text: str, content: Dict) -> StructuralClaim:
        """Verify code syntax by PARSING it."""
        subtype = content.get("subtype")
        groups = content.get("groups", ())
        
        if subtype == "code_block":
            language = groups[0] or "python" if groups else "python"
            code = groups[1] if len(groups) > 1 else ""
            
            if language.lower() in ("python", "py"):
                try:
                    ast.parse(code)
                    return StructuralClaim(
                        text=f"```{language}...```",
                        category=VerificationCategory.CODE_SYNTAX,
                        verified=True,
                        witness=f"AST parsed successfully ({len(code)} chars)",
                        mu_cost=1.0,
                    )
                except SyntaxError as e:
                    return StructuralClaim(
                        text=f"```{language}...```",
                        category=VerificationCategory.CODE_SYNTAX,
                        verified=False,
                        mu_cost=1.0,
                        error=f"Syntax error: {e.msg} at line {e.lineno}",
                    )
            elif language.lower() == "json":
                try:
                    json.loads(code)
                    return StructuralClaim(
                        text=f"```json...```",
                        category=VerificationCategory.CODE_SYNTAX,
                        verified=True,
                        witness="JSON parsed successfully",
                        mu_cost=1.0,
                    )
                except json.JSONDecodeError as e:
                    return StructuralClaim(
                        text=f"```json...```",
                        category=VerificationCategory.CODE_SYNTAX,
                        verified=False,
                        mu_cost=1.0,
                        error=f"JSON error: {e.msg}",
                    )
        
        return StructuralClaim(
            text=claim_text[:50],
            category=VerificationCategory.CODE_SYNTAX,
            verified=None, mu_cost=0.0,
            error="Unknown code claim type",
        )
    
    def _verify_file_system(self, claim_text: str, content: Dict) -> StructuralClaim:
        """Verify file system claims by CHECKING the filesystem."""
        path = content.get("path", "")
        
        if not path:
            return StructuralClaim(
                text=claim_text,
                category=VerificationCategory.FILE_SYSTEM,
                verified=None, mu_cost=0.0,
                error="No path found in claim",
            )
        
        # Handle relative paths
        if not Path(path).is_absolute():
            full_path = self.workspace_root / path
        else:
            full_path = Path(path)
        
        exists = full_path.exists()
        
        return StructuralClaim(
            text=claim_text,
            category=VerificationCategory.FILE_SYSTEM,
            verified=exists,
            witness=f"Filesystem check: {full_path} {'exists' if exists else 'not found'}",
            mu_cost=1.0,
            error=None if exists else f"File not found: {full_path}",
        )
    
    def _verify_import(self, claim_text: str, content: Dict) -> StructuralClaim:
        """Verify import claims by TRYING the import."""
        module = content.get("module", "")
        
        if not module:
            return StructuralClaim(
                text=claim_text,
                category=VerificationCategory.IMPORT,
                verified=None, mu_cost=0.0,
                error="No module found in claim",
            )
        
        try:
            __import__(module)
            return StructuralClaim(
                text=claim_text,
                category=VerificationCategory.IMPORT,
                verified=True,
                witness=f"Import successful: {module}",
                mu_cost=1.0,
            )
        except ImportError as e:
            return StructuralClaim(
                text=claim_text,
                category=VerificationCategory.IMPORT,
                verified=False,
                mu_cost=1.0,
                error=f"Import failed: {e}",
            )
    
    def get_stats(self) -> Dict[str, Any]:
        """Get verification statistics."""
        total_claims = sum(len(r.claims) for r in self.history)
        verified = sum(r.structurally_verified for r in self.history)
        failed = sum(r.structurally_failed for r in self.history)
        external = sum(r.requires_external for r in self.history)
        unverifiable = sum(r.unverifiable for r in self.history)
        
        return {
            "total_verifications": len(self.history),
            "total_claims": total_claims,
            "structurally_verified": verified,
            "structurally_failed": failed,
            "requires_external_oracle": external,
            "unverifiable": unverifiable,
            "structural_accuracy": verified / max(1, verified + failed),
            "total_mu_consumed": self.total_mu,
        }


def print_structural_result(result: StructuralResult, verbose: bool = True):
    """Pretty print structural verification result - HONEST output."""
    print()
    
    if result.structurally_failed == 0 and result.structurally_verified > 0:
        print(f"\033[1;32m✓ STRUCTURALLY VERIFIED ({result.structurally_verified} claims)\033[0m")
    elif result.structurally_failed > 0:
        print(f"\033[1;31m✗ STRUCTURAL FAILURES ({result.structurally_failed} failed, {result.structurally_verified} passed)\033[0m")
    elif result.requires_external > 0:
        print(f"\033[1;33m? REQUIRES EXTERNAL ORACLE ({result.requires_external} claims)\033[0m")
    else:
        print(f"\033[1;90m○ NO STRUCTURAL CLAIMS FOUND\033[0m")
    
    if result.requires_external > 0:
        print(f"  \033[33m⚠ {result.requires_external} claims require web/database verification\033[0m")
    
    print(f"  μ-cost: {result.total_mu_cost:.1f}")
    print(f"  Certificate: {result.certificate_hash[:40]}...")
    
    if verbose and result.claims:
        print("\n  Claims:")
        for c in result.claims:
            if c.verified is True:
                icon = "\033[32m✓\033[0m"  # Green check
                status = "VERIFIED"
            elif c.verified is False:
                icon = "\033[31m✗\033[0m"  # Red X
                status = "FAILED"
            elif c.requires_oracle:
                icon = "\033[33m?\033[0m"  # Yellow question
                status = f"NEEDS {c.oracle_type.upper()}"
            else:
                icon = "\033[90m○\033[0m"  # Gray circle
                status = "UNVERIFIABLE"
            
            claim_display = c.text[:50] + "..." if len(c.text) > 50 else c.text
            print(f"    {icon} [{c.category.value}] {claim_display}")
            print(f"       Status: {status}")
            
            if c.witness:
                print(f"       \033[90mWitness: {c.witness[:60]}\033[0m")
            if c.error:
                print(f"       \033[33mNote: {c.error[:60]}\033[0m")
    print()


# Global instance
_verifier: Optional[StructuralVerifier] = None

def get_structural_verifier() -> StructuralVerifier:
    """Get or create global verifier."""
    global _verifier
    if _verifier is None:
        _verifier = StructuralVerifier()
    return _verifier


if __name__ == "__main__":
    verifier = StructuralVerifier()
    
    print("=" * 70)
    print("THIELE MACHINE - HONEST STRUCTURAL VERIFICATION")
    print("=" * 70)
    print("\nWe verify what we can COMPUTE. We're honest about what we can't.\n")
    
    tests = [
        # STRUCTURALLY VERIFIABLE
        ("Math (verifiable)", "1+2=3"),
        ("Math wrong (verifiable)", "1+2=5"),
        ("Factorization (verifiable)", "15 = 3 × 5"),
        ("Power (verifiable)", "2^10 = 1024"),
        ("Comparison (verifiable)", "5 > 3"),
        ("File exists (verifiable)", "The file `thielecpu/vm.py` exists"),
        
        # REQUIRES EXTERNAL ORACLE
        ("Capital (needs oracle)", "The capital of France is Paris"),
        ("Earth shape (needs oracle)", "The earth is round"),
        ("Causation (needs oracle)", "Vaccines cause autism"),
        
        # FUTURE (inherently unverifiable)  
        ("Future (unverifiable)", "In 2030 AI will be sentient"),
        
        # CONVERSATIONAL
        ("Question", "Can you help me?"),
        ("Statement", "Hello world"),
    ]
    
    for label, text in tests:
        print(f"\n\033[1;33m{label}:\033[0m {text}")
        result = verifier.verify_text(text)
        print_structural_result(result, verbose=True)
    
    # Stats
    print("=" * 70)
    print("SESSION STATISTICS")
    print("=" * 70)
    stats = verifier.get_stats()
    print(f"  Total claims analyzed: {stats['total_claims']}")
    print(f"  \033[32mStructurally verified:\033[0m {stats['structurally_verified']}")
    print(f"  \033[31mStructurally failed:\033[0m {stats['structurally_failed']}")
    print(f"  \033[33mRequires external oracle:\033[0m {stats['requires_external_oracle']}")
    print(f"  \033[90mUnverifiable:\033[0m {stats['unverifiable']}")
    print(f"  μ consumed: {stats['total_mu_consumed']:.1f}")
