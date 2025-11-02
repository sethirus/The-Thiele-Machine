"""
Canonical Corpus for Receipt Fuzzing

Test cases designed to expose vulnerabilities in receipt parsers.
Each test case should be REJECTED by compliant verifiers.
"""

UNICODE_TRAPS = [
    {
        "name": "NFC vs NFD normalization",
        "receipt": '{"version":"TRS-0","global_digest":"e\u0301"}',  # é as e + combining acute
        "expected": "reject",
        "reason": "Not NFC normalized"
    },
    {
        "name": "Homoglyph attack",
        "receipt": '{"version":"TRS-0","glоbal_digest":"abc"}',  # Cyrillic о instead of Latin o
        "expected": "reject",
        "reason": "Contains non-ASCII in ASCII field"
    },
    {
        "name": "Zero-width characters",
        "receipt": '{"version":"TRS-0","global\u200bdigest":"abc"}',
        "expected": "reject",
        "reason": "Contains zero-width space"
    },
]

STRUCTURAL_ATTACKS = [
    {
        "name": "CRLF line endings",
        "receipt": '{\r\n"version":"TRS-0"\r\n}',
        "expected": "reject",
        "reason": "Non-canonical whitespace (CRLF)"
    },
    {
        "name": "Duplicate keys",
        "receipt": '{"version":"TRS-0","version":"TRS-1"}',
        "expected": "reject",
        "reason": "Duplicate key 'version'"
    },
    {
        "name": "Unsorted keys",
        "receipt": '{"global_digest":"abc","version":"TRS-0"}',
        "expected": "reject",
        "reason": "Keys not sorted (global_digest before version)"
    },
    {
        "name": "Extra whitespace",
        "receipt": '{ "version": "TRS-0" }',
        "expected": "reject",
        "reason": "Non-canonical whitespace"
    },
]

TYPE_CONFUSION = [
    {
        "name": "Integer as float",
        "receipt": '{"version":"TRS-0","size":123.0}',
        "expected": "reject",
        "reason": "Float literal for integer field"
    },
    {
        "name": "String as number",
        "receipt": '{"version":"TRS-0","size":"123"}',
        "expected": "reject",
        "reason": "String for integer field"
    },
    {
        "name": "Boolean as integer",
        "receipt": '{"version":"TRS-0","executable":1}',
        "expected": "reject",
        "reason": "Integer for boolean field"
    },
]

PATH_TRAVERSAL = [
    {
        "name": "Parent directory",
        "receipt": '{"version":"TRS-0","files":[{"path":"../etc/passwd"}]}',
        "expected": "reject",
        "reason": "Path traversal attempt"
    },
    {
        "name": "Absolute path",
        "receipt": '{"version":"TRS-0","files":[{"path":"/etc/passwd"}]}',
        "expected": "reject",
        "reason": "Absolute path not allowed"
    },
    {
        "name": "Double slash",
        "receipt": '{"version":"TRS-0","files":[{"path":"foo//bar"}]}',
        "expected": "reject",
        "reason": "Duplicate slashes"
    },
]

SIZE_ATTACKS = [
    {
        "name": "Extremely long string",
        "receipt": '{"version":"TRS-0","comment":"' + 'A' * 1000000 + '"}',
        "expected": "reject",
        "reason": "Exceeds size limit"
    },
    {
        "name": "Deeply nested structure",
        "receipt": '{"a":' * 10000 + '0' + '}' * 10000,
        "expected": "reject",
        "reason": "Exceeds nesting limit"
    },
]

INJECTION_ATTACKS = [
    {
        "name": "Shell metacharacters",
        "receipt": '{"version":"TRS-0","files":[{"path":"foo;rm -rf /"}]}',
        "expected": "reject",
        "reason": "Shell metacharacters in path"
    },
    {
        "name": "Null byte",
        "receipt": '{"version":"TRS-0","files":[{"path":"foo\\u0000bar"}]}',
        "expected": "reject",
        "reason": "Null byte in path"
    },
]

ALL_TESTS = (
    UNICODE_TRAPS +
    STRUCTURAL_ATTACKS +
    TYPE_CONFUSION +
    PATH_TRAVERSAL +
    SIZE_ATTACKS +
    INJECTION_ATTACKS
)
