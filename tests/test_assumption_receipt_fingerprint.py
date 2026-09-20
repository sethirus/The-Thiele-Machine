from scripts.assumption_receipt_fingerprint import _strip_coq_comments


def test_coq_comments_and_external_whitespace_are_semantically_ignored():
    assert _strip_coq_comments("Definition x := 1. (* editorial *)\n") == \
        _strip_coq_comments("Definition x := 1.")


def test_string_contents_remain_semantically_significant():
    first = _strip_coq_comments('Definition x := "a  b".')
    second = _strip_coq_comments('Definition x := "a b".')
    assert first != second


def test_nested_comments_are_removed_without_joining_tokens():
    assert _strip_coq_comments("foo (* outer (* inner *) tail *) bar") == "foo bar"
