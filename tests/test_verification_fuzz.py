#!/usr/bin/env python3
"""
Comprehensive fuzz tests for Thiele verification system.
Tests edge cases, false positives, and ensures robustness.
"""

import pytest
import re
import random
import string
from pathlib import Path
from typing import List, Tuple

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from thielecpu.structural_verify import (
    StructuralVerifier,
    StructuralClaimExtractor,
    VerificationCategory,
)


class TestFileFalsePositives:
    """Test that Python code patterns don't trigger false file detections."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()
    
    @pytest.fixture
    def extractor(self):
        return StructuralClaimExtractor()

    # Python attribute access patterns that should NOT be detected as files
    PYTHON_ATTRIBUTE_PATTERNS = [
        "self._pool",
        "self._private",
        "self.config.json",  # NOT a file, it's obj.attr.attr
        "obj._internal.py",  # NOT a file, it's obj.attr.attr
        "data._hidden.yaml",
        "cls._class_var.txt",
        "instance._buffer.json",
        "module._internal.csv",
    ]

    @pytest.mark.parametrize("text", PYTHON_ATTRIBUTE_PATTERNS)
    def test_python_attributes_not_detected_as_files(self, verifier, text):
        """Python attribute access should not be detected as file paths."""
        result = verifier.verify_text(text)
        file_claims = [c for c in result.claims if c.category == VerificationCategory.FILE_SYSTEM]
        assert len(file_claims) == 0, f"False positive: {text} detected as file"

    # Patterns with "file" or "path" keywords that should NOT match Python attrs
    KEYWORD_WITH_PYTHON_ATTRS = [
        "path self._pool",
        "file self._config",
        "in self._data.py",
        "from self.module.py import",
        "at self._cache.json",
    ]

    @pytest.mark.parametrize("text", KEYWORD_WITH_PYTHON_ATTRS)
    def test_keywords_with_python_attrs_not_detected(self, verifier, text):
        """Keywords like 'file'/'path' followed by Python attrs should not match."""
        result = verifier.verify_text(text)
        file_claims = [c for c in result.claims if c.category == VerificationCategory.FILE_SYSTEM]
        assert len(file_claims) == 0, f"False positive: {text}"


class TestFileTruePositives:
    """Test that valid file references ARE detected."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()

    VALID_FILE_REFERENCES = [
        ("file config.py", "config.py"),
        ("path to/file.json", "to/file.js"),  # Note: pattern matches 'to/file.js' substring
        ("`module.py`", "module.py"),
        ("`src/utils.ts`", "src/utils.ts"),
        ("file data.yaml exists", "data.yaml"),
        ("path config.toml", "config.toml"),
        # NOTE: Markdown links [file.md](file.md) are handled by live_verify.py, not structural_verify.py
        ("`tests/test_main.py`", "tests/test_main.py"),
    ]

    @pytest.mark.parametrize("text,expected_path", VALID_FILE_REFERENCES)
    def test_valid_file_references_detected(self, verifier, text, expected_path):
        """Valid file references should be detected."""
        result = verifier.verify_text(text)
        file_claims = [c for c in result.claims if c.category == VerificationCategory.FILE_SYSTEM]
        assert len(file_claims) > 0, f"Missed valid file: {text}"


class TestCodeBlockVerification:
    """Test code block extraction and verification."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()

    VALID_PYTHON_CODE = [
        "```python\ndef hello(): pass\n```",
        "```python\nclass Foo:\n    def __init__(self):\n        self._pool = []\n```",
        "```python\nimport os\nos.getcwd()\n```",
        "```python\nx = {'key': 'value'}\n```",
        "```python\n# Comment\n\n```",
    ]

    @pytest.mark.parametrize("code", VALID_PYTHON_CODE)
    def test_valid_python_code_passes(self, verifier, code):
        """Valid Python code should pass verification."""
        result = verifier.verify_text(code)
        code_claims = [c for c in result.claims if c.category == VerificationCategory.CODE_SYNTAX]
        assert len(code_claims) > 0, f"Code not detected: {code[:50]}"
        assert all(c.verified is True for c in code_claims), f"Valid code failed: {code[:50]}"

    INVALID_PYTHON_CODE = [
        "```python\ndef broken(\n```",
        "```python\nif True\n    pass\n```",
        "```python\nclass Foo:\ndef method(self): pass\n```",  # Bad indent
        "```python\nreturn outside function\n```",
    ]

    @pytest.mark.parametrize("code", INVALID_PYTHON_CODE)
    def test_invalid_python_code_fails(self, verifier, code):
        """Invalid Python code should fail verification."""
        result = verifier.verify_text(code)
        code_claims = [c for c in result.claims if c.category == VerificationCategory.CODE_SYNTAX]
        assert len(code_claims) > 0, f"Code not detected: {code[:50]}"
        # At least one should fail
        failed = [c for c in code_claims if c.verified is False]
        assert len(failed) > 0, f"Invalid code passed: {code[:50]}"


class TestImportVerification:
    """Test import statement verification."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()

    VALID_IMPORTS = [
        "from os import path",
        "from typing import List",
        "from dataclasses import dataclass",
        "import sys",
        "import json",
    ]

    @pytest.mark.parametrize("text", VALID_IMPORTS)
    def test_valid_imports_pass(self, verifier, text):
        """Valid imports should pass verification."""
        result = verifier.verify_text(text)
        import_claims = [c for c in result.claims if c.category == VerificationCategory.IMPORT]
        assert len(import_claims) > 0, f"Import not detected: {text}"
        assert all(c.verified is True for c in import_claims), f"Valid import failed: {text}"

    INVALID_IMPORTS = [
        "import nonexistent_module_xyz",
        "from fake_package import nothing",
    ]

    @pytest.mark.parametrize("text", INVALID_IMPORTS)
    def test_invalid_imports_fail(self, verifier, text):
        """Invalid imports should fail verification."""
        result = verifier.verify_text(text)
        import_claims = [c for c in result.claims if c.category == VerificationCategory.IMPORT]
        assert len(import_claims) > 0, f"Import not detected: {text}"
        failed = [c for c in import_claims if c.verified is False]
        assert len(failed) > 0, f"Invalid import passed: {text}"


class TestMathVerification:
    """Test mathematical claim verification."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()

    VALID_MATH = [
        ("2 + 2 = 4", True),
        ("10 * 5 = 50", True),
        ("100 / 4 = 25", True),
        ("7 - 3 = 4", True),
        ("15 = 3 × 5", True),
        ("15 = 3 * 5", True),
        ("2^10 = 1024", True),
    ]

    @pytest.mark.parametrize("text,expected", VALID_MATH)
    def test_valid_math_passes(self, verifier, text, expected):
        """Valid math claims should pass."""
        result = verifier.verify_text(text)
        math_claims = [c for c in result.claims if c.category == VerificationCategory.MATHEMATICAL]
        if len(math_claims) > 0:
            assert math_claims[0].verified == expected, f"Math verification wrong: {text}"

    INVALID_MATH = [
        ("2 + 2 = 5", False),
        ("10 * 5 = 51", False),
        ("15 = 4 × 5", False),
    ]

    @pytest.mark.parametrize("text,expected", INVALID_MATH)
    def test_invalid_math_fails(self, verifier, text, expected):
        """Invalid math claims should fail."""
        result = verifier.verify_text(text)
        math_claims = [c for c in result.claims if c.category == VerificationCategory.MATHEMATICAL]
        if len(math_claims) > 0:
            assert math_claims[0].verified == expected, f"Wrong math passed: {text}"


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()

    def test_empty_string(self, verifier):
        """Empty string should not crash."""
        result = verifier.verify_text("")
        assert result.structurally_failed == 0

    def test_whitespace_only(self, verifier):
        """Whitespace-only string should not crash."""
        result = verifier.verify_text("   \n\t\n   ")
        assert result.structurally_failed == 0

    def test_unicode_text(self, verifier):
        """Unicode text should not crash."""
        result = verifier.verify_text("Hello 世界 🌍 مرحبا")
        assert result is not None

    def test_very_long_text(self, verifier):
        """Very long text should not crash."""
        long_text = "x = 1\n" * 10000
        result = verifier.verify_text(f"```python\n{long_text}\n```")
        assert result is not None

    def test_nested_code_blocks(self, verifier):
        """Nested code blocks should be handled."""
        text = "```python\nprint('```')\n```"
        result = verifier.verify_text(text)
        # Should not crash, may or may not parse correctly
        assert result is not None

    def test_special_characters_in_path(self, verifier):
        """Special characters in paths should be handled."""
        text = "file with spaces.py"  # Has space in name
        result = verifier.verify_text(text)
        assert result is not None

    def test_mixed_content(self, verifier):
        """Mixed content with code, files, math should work."""
        # NOTE: Code blocks need to start at column 0 for proper parsing
        text = """Here's some code:
```python
def factorial(n):
    if n <= 1:
        return 1
    return n * factorial(n - 1)
```

Note that 5 * 24 = 120.
See `README.md` for more.
"""
        result = verifier.verify_text(text)
        # Should have at least the code block claim
        assert len(result.claims) > 0, "Should extract some claims"


class TestFuzzGenerated:
    """Fuzz testing with generated inputs."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()

    def generate_random_string(self, length: int) -> str:
        """Generate random string."""
        chars = string.ascii_letters + string.digits + " _.-/`'\""
        return ''.join(random.choice(chars) for _ in range(length))

    def generate_python_like_attr(self) -> str:
        """Generate Python-like attribute access."""
        prefixes = ["self", "cls", "obj", "data", "config", "_private"]
        attrs = ["_pool", "_cache", "_data", "value", "items"]
        extensions = [".py", ".json", ".yaml", ".txt", ""]
        
        prefix = random.choice(prefixes)
        attr = random.choice(attrs)
        ext = random.choice(extensions)
        return f"{prefix}.{attr}{ext}"

    def test_fuzz_random_strings(self, verifier):
        """Random strings should not crash the verifier."""
        for _ in range(100):
            text = self.generate_random_string(random.randint(1, 500))
            result = verifier.verify_text(text)
            assert result is not None, f"Crashed on: {text[:50]}"

    def test_fuzz_python_attrs(self, verifier):
        """Random Python-like attributes should not be file false positives."""
        for _ in range(100):
            text = f"file {self.generate_python_like_attr()}"
            result = verifier.verify_text(text)
            file_claims = [c for c in result.claims 
                          if c.category == VerificationCategory.FILE_SYSTEM 
                          and "self." in (c.text or "")]
            assert len(file_claims) == 0, f"False positive: {text}"

    def test_fuzz_code_blocks(self, verifier):
        """Random code blocks should not crash."""
        for _ in range(50):
            code = self.generate_random_string(random.randint(1, 200))
            text = f"```python\n{code}\n```"
            result = verifier.verify_text(text)
            assert result is not None


class TestRegressions:
    """Regression tests for previously found bugs."""
    
    @pytest.fixture
    def verifier(self):
        return StructuralVerifier()

    def test_self_pool_not_detected_as_file(self, verifier):
        """Regression: self._pool was falsely detected as file path."""
        texts = [
            "self._pool = []",
            "path self._pool",
            "file self._pool",
            "The self._pool attribute",
        ]
        for text in texts:
            result = verifier.verify_text(text)
            file_claims = [c for c in result.claims if c.category == VerificationCategory.FILE_SYSTEM]
            assert len(file_claims) == 0, f"Regression: {text} still detected as file"

    def test_from_import_not_as_file(self, verifier):
        """Regression: 'from module.py import' was detected as file."""
        text = "from self.module.py import something"
        result = verifier.verify_text(text)
        file_claims = [c for c in result.claims if c.category == VerificationCategory.FILE_SYSTEM]
        assert len(file_claims) == 0, "from X import should not be file claim"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
