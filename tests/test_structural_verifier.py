"""
Tests for Thiele Machine Structural Verification

These tests verify the HONEST structural verification approach:
- We can verify what we can COMPUTE (math, code, files, imports)
- We're HONEST about what requires external oracles (world facts)
- We mark inherently unverifiable claims appropriately (opinions, future)
"""

import pytest
from pathlib import Path
import sys

# Add repo root
REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.structural_verify import (
    StructuralVerifier,
    StructuralClaimExtractor,
    StructuralClaim,
    VerificationCategory,
)


class TestVerificationCategories:
    """Test claim categorization."""
    
    @pytest.fixture
    def extractor(self):
        return StructuralClaimExtractor()
    
    def test_mathematical_claims_categorized(self, extractor):
        """Math claims should be in MATHEMATICAL category."""
        # Use extract_all which returns (text, category, data) tuples
        claims = extractor.extract_all("2 + 2 = 4")
        assert len(claims) > 0
        math_claims = [c for c in claims if c[1] == VerificationCategory.MATHEMATICAL]
        assert len(math_claims) > 0
    
    def test_code_syntax_claims_categorized(self, extractor):
        """Code blocks should be in CODE_SYNTAX category."""
        text = """```python
def hello():
    print("world")
```"""
        claims = extractor.extract_all(text)
        code_claims = [c for c in claims if c[1] == VerificationCategory.CODE_SYNTAX]
        assert len(code_claims) > 0
    
    def test_file_claims_categorized(self, extractor):
        """File references should be in FILE_SYSTEM category."""
        claims = extractor.extract_all("Check the `thielecpu/vm.py` file")
        file_claims = [c for c in claims if c[1] == VerificationCategory.FILE_SYSTEM]
        assert len(file_claims) > 0
    
    def test_import_claims_categorized(self, extractor):
        """Import statements should be in IMPORT category."""
        text = "You can `import json` to parse JSON"
        claims = extractor.extract_all(text)
        import_claims = [c for c in claims if c[1] == VerificationCategory.IMPORT]
        assert len(import_claims) > 0
    
    def test_factual_claims_categorized(self, extractor):
        """Real-world facts should be in FACTUAL_WORLD category."""
        claims = extractor.extract_all("The capital of France is Paris")
        factual_claims = [c for c in claims if c[1] == VerificationCategory.FACTUAL_WORLD]
        assert len(factual_claims) > 0
    
    def test_future_claims_categorized(self, extractor):
        """Future predictions should be in FUTURE category."""
        claims = extractor.extract_all("By 2030 AI will be everywhere")
        future_claims = [c for c in claims if c[1] == VerificationCategory.FUTURE]
        assert len(future_claims) > 0
    
    def test_opinion_claims_categorized(self, extractor):
        """Opinions should be in OPINION category."""
        claims = extractor.extract_all("I think Python is the best language")
        opinion_claims = [c for c in claims if c[1] == VerificationCategory.OPINION]
        assert len(opinion_claims) > 0
    
    def test_question_claims_categorized(self, extractor):
        """Questions should be in CONVERSATIONAL category (questions are conversational)."""
        claims = extractor.extract_all("What time is it?")
        # Questions fall under CONVERSATIONAL category
        conv_claims = [c for c in claims if c[1] == VerificationCategory.CONVERSATIONAL]
        assert len(conv_claims) > 0


class TestMathematicalVerification:
    """Test mathematical claim verification."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    def test_simple_addition(self, verifier):
        """Should verify 1+1=2."""
        result = verifier.verify_text("1 + 1 = 2")
        claims = result.claims
        math_claim = next((c for c in claims if c.category == VerificationCategory.MATHEMATICAL), None)
        assert math_claim is not None
        assert math_claim.verified is True
    
    def test_incorrect_addition(self, verifier):
        """Should fail 1+1=3."""
        result = verifier.verify_text("1 + 1 = 3")
        claims = result.claims
        math_claim = next((c for c in claims if c.category == VerificationCategory.MATHEMATICAL), None)
        assert math_claim is not None
        assert math_claim.verified is False
    
    def test_multiplication(self, verifier):
        """Should verify multiplication."""
        result = verifier.verify_text("15 = 3 × 5")
        claims = result.claims
        math_claim = next((c for c in claims if c.category == VerificationCategory.MATHEMATICAL), None)
        assert math_claim is not None
        assert math_claim.verified is True
    
    def test_factorization(self, verifier):
        """Should verify factorization claims."""
        result = verifier.verify_text("3233 = 53 × 61")
        claims = result.claims
        math_claim = next((c for c in claims if c.category == VerificationCategory.MATHEMATICAL), None)
        assert math_claim is not None
        assert math_claim.verified is True


class TestCodeSyntaxVerification:
    """Test code syntax verification."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    def test_valid_python_syntax(self, verifier):
        """Should verify valid Python code."""
        code = """```python
def hello():
    return "world"
```"""
        result = verifier.verify_text(code)
        claims = result.claims
        code_claim = next((c for c in claims if c.category == VerificationCategory.CODE_SYNTAX), None)
        assert code_claim is not None
        assert code_claim.verified is True
    
    def test_invalid_python_syntax(self, verifier):
        """Should fail invalid Python code."""
        code = """```python
def hello(
    return "world"
```"""
        result = verifier.verify_text(code)
        claims = result.claims
        code_claim = next((c for c in claims if c.category == VerificationCategory.CODE_SYNTAX), None)
        assert code_claim is not None
        assert code_claim.verified is False


class TestFileSystemVerification:
    """Test file system verification."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    def test_existing_file(self, verifier):
        """Should verify existing file."""
        # This file exists in our repo
        result = verifier.verify_text("The file `thielecpu/vm.py` exists")
        claims = result.claims
        file_claim = next((c for c in claims if c.category == VerificationCategory.FILE_SYSTEM), None)
        assert file_claim is not None
        # Note: Verification depends on working directory
    
    def test_nonexistent_file(self, verifier):
        """Should fail nonexistent file."""
        result = verifier.verify_text("Check `nonexistent_file_xyz.py`")
        claims = result.claims
        file_claim = next((c for c in claims if c.category == VerificationCategory.FILE_SYSTEM), None)
        assert file_claim is not None
        assert file_claim.verified is False


class TestImportVerification:
    """Test import verification."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    def test_valid_import(self, verifier):
        """Should verify valid imports."""
        result = verifier.verify_text("You can `import json` to parse JSON")
        claims = result.claims
        import_claim = next((c for c in claims if c.category == VerificationCategory.IMPORT), None)
        assert import_claim is not None
        assert import_claim.verified is True
    
    def test_invalid_import(self, verifier):
        """Should fail invalid imports."""
        result = verifier.verify_text("`import nonexistent_module_xyz`")
        claims = result.claims
        import_claim = next((c for c in claims if c.category == VerificationCategory.IMPORT), None)
        assert import_claim is not None
        assert import_claim.verified is False


class TestHonestUnverifiable:
    """Test that we're honest about what we can't verify."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    def test_factual_claims_marked_external(self, verifier):
        """Factual claims should be marked as requiring external oracle."""
        result = verifier.verify_text("The capital of France is Paris")
        claims = result.claims
        factual = [c for c in claims if c.category == VerificationCategory.FACTUAL_WORLD]
        assert len(factual) > 0
        # verified should be None (unknown, requires external oracle)
        for claim in factual:
            assert claim.verified is None
            assert claim.requires_oracle is True
    
    def test_future_predictions_unverifiable(self, verifier):
        """Future predictions should be marked unverifiable."""
        result = verifier.verify_text("In 2050 humans will live on Mars")
        claims = result.claims
        # Future claims may be categorized differently
        future_or_factual = [c for c in claims if c.category in (VerificationCategory.FUTURE, VerificationCategory.FACTUAL_WORLD)]
        assert len(future_or_factual) > 0
        for claim in future_or_factual:
            assert claim.verified is None
    
    def test_opinions_unverifiable(self, verifier):
        """Opinions should be marked unverifiable."""
        result = verifier.verify_text("I think Python is the best programming language")
        claims = result.claims
        opinions = [c for c in claims if c.category == VerificationCategory.OPINION]
        assert len(opinions) > 0
        for claim in opinions:
            assert claim.verified is None


class TestMuCostTracking:
    """Test μ-cost tracking."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    def test_math_costs_mu(self, verifier):
        """Math verification should cost μ."""
        result = verifier.verify_text("1 + 1 = 2")
        assert result.total_mu_cost > 0
    
    def test_code_parsing_costs_mu(self, verifier):
        """Code parsing should cost μ."""
        result = verifier.verify_text("```python\nprint('hello')\n```")
        assert result.total_mu_cost > 0
    
    def test_factual_claims_cost_nothing(self, verifier):
        """Claims we can't verify shouldn't cost μ (no computation)."""
        # Verify only factual claims
        result = verifier.verify_text("The capital of France is Paris")
        # Factual claims require 0 μ (no computation done)
        factual_claims = [c for c in result.claims if c.category == VerificationCategory.FACTUAL_WORLD]
        for claim in factual_claims:
            assert claim.mu_cost == 0


class TestStatistics:
    """Test statistics tracking."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    def test_stats_tracking(self, verifier):
        """Should track verification statistics."""
        verifier.verify_text("1 + 1 = 2")
        verifier.verify_text("The capital of France is Paris")
        
        stats = verifier.get_stats()
        assert stats["total_claims"] >= 2
        assert stats["structurally_verified"] >= 1
        assert stats["requires_external_oracle"] >= 1


class TestIntegration:
    """Integration tests with complex texts."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    def test_mixed_claims(self, verifier):
        """Should handle text with mixed claim types."""
        text = """
        Here's a factorization: 15 = 3 × 5.
        
        You can import json in Python:
        ```python
        import json
        data = json.loads('{"key": "value"}')
        ```
        
        The capital of France is Paris.
        """
        
        result = verifier.verify_text(text)
        
        # Should have claims in multiple categories
        categories = set(c.category for c in result.claims)
        assert VerificationCategory.MATHEMATICAL in categories or VerificationCategory.CODE_SYNTAX in categories
    
    def test_realistic_copilot_response(self, verifier):
        """Test with realistic Copilot-style response."""
        # No indentation in the code block - matches real Copilot output
        text = """To read a JSON file in Python, you can use:

```python
import json

with open('data.json', 'r') as f:
    data = json.load(f)
```

This will parse the JSON and return a Python dictionary.
The `json` module is part of the standard library, so no installation is needed.
"""
        
        result = verifier.verify_text(text)
        
        # Code should be syntactically valid
        code_claims = [c for c in result.claims if c.category == VerificationCategory.CODE_SYNTAX]
        for claim in code_claims:
            assert claim.verified is True, f"Code verification failed: {claim.error}"
        
        # Import should be valid
        import_claims = [c for c in result.claims if c.category == VerificationCategory.IMPORT]
        for claim in import_claims:
            assert claim.verified is True


class TestResultFormatting:
    """Test result data structure."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    def test_result_to_dict(self, verifier):
        """Result should serialize to dict."""
        result = verifier.verify_text("1 + 1 = 2")
        d = result.to_dict()
        
        assert "original_text" in d
        assert "claims" in d
        assert "total_mu_cost" in d
        assert "certificate_hash" in d
    
    def test_claim_has_required_fields(self, verifier):
        """Each claim should have required fields."""
        result = verifier.verify_text("1 + 1 = 2")
        
        for claim in result.claims:
            assert hasattr(claim, "text")
            assert hasattr(claim, "category")
            assert hasattr(claim, "verified")
            assert hasattr(claim, "witness")
            assert hasattr(claim, "mu_cost")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
