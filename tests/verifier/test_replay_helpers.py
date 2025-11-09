from verifier.replay_helpers import _gather_receipt_files


def test_gather_receipt_files_single_file(tmp_path):
    receipt = tmp_path / "example.receipt.json"
    receipt.write_text("{}", encoding="utf-8")

    result = _gather_receipt_files(receipt)

    assert result == [receipt]


def test_gather_receipt_files_directory_sorted(tmp_path):
    first = tmp_path / "a.receipt.json"
    second = tmp_path / "b.receipt.json"
    first.write_text("{}", encoding="utf-8")
    second.write_text("{}", encoding="utf-8")

    # Non-matching files should be ignored
    (tmp_path / "ignore.txt").write_text("noop", encoding="utf-8")

    result = _gather_receipt_files(tmp_path)

    assert result == [first, second]


def test_gather_receipt_files_missing_path(tmp_path):
    missing = tmp_path / "does-not-exist"

    result = _gather_receipt_files(missing)

    assert result == []
