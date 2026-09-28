#!/usr/bin/env python3
"""Check project-owned comments for unfinished or historical wording."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

# These are review markers, not ordinary technical vocabulary.  A match means
# that a comment needs an explicit rewrite or removal before it enters the
# maintained source surface.
REVIEW_MARKERS = re.compile(
    r"(?ix)"
    r"\b(?:TODO|FIXME|WIP|TBD|XXX|HACK)\b"
    r"|\bnot\s+yet\b"
    r"|\bpreviously\b"
    r"|\bfuture\s+(?:work|use|phase)\b"
    r"|\b(?:early\s+draft|what\s+remains|decision\s+pending)\b"
    r"|\bcurrently\s+(?:unused|empty)\b"
    r"|\blater\s+phase\b"
    r"|\b(?:will\s+be\s+added|to\s+be\s+implemented)\b"
)

LINE_COMMENT_SUFFIXES = {
    ".py", ".pyi", ".sh", ".bash", ".zsh", ".yml", ".yaml", ".toml",
    ".ini", ".cfg", ".mk", ".make", ".bsv", ".v", ".sv", ".svh",
    ".c", ".h", ".cc", ".cpp", ".hpp", ".js", ".jsx", ".ts", ".tsx",
    ".java", ".go", ".rs", ".swift", ".lua", ".sql", ".hs",
}
C_BLOCK_SUFFIXES = {
    ".v", ".sv", ".svh", ".bsv", ".c", ".h", ".cc", ".cpp", ".hpp",
    ".js", ".jsx", ".ts", ".tsx", ".java", ".go", ".rs", ".swift",
    ".ml", ".mli", ".mll", ".mly", ".sql",
}
COQ_BLOCK_SUFFIXES = {".v", ".ml", ".mli", ".mll", ".mly"}
TEX_SUFFIXES = {".tex", ".sty", ".cls"}
HTML_COMMENT_SUFFIXES = {".md", ".markdown", ".html", ".htm"}

# These are generated or vendored surfaces.  Their comments are not part of
# the maintained source contract and are checked by their own generators.
EXCLUDED_PARTS = {
    ".git", "vendor", "build", "__pycache__", ".pytest_cache", ".mypy_cache",
}
EXCLUDED_FILES = {
    "coq/Makefile",
    "coq/AssumptionsProbeAll.v",
}


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    text: str
    marker: str


def tracked_files() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z"], cwd=ROOT, check=True, capture_output=True
    )
    paths: list[Path] = []
    for raw in result.stdout.decode().split("\0"):
        if not raw:
            continue
        path = Path(raw)
        if str(path) in EXCLUDED_FILES or any(part in EXCLUDED_PARTS for part in path.parts):
            continue
        if path.exists():
            paths.append(path)
    return paths


def _comment_spans(text: str, suffix: str) -> list[tuple[int, str]]:
    spans: list[tuple[int, str]] = []
    lines = text.splitlines()
    block_start: int | None = None
    block_lines: list[str] = []
    block_end = ""

    def emit_block(end_line: int) -> None:
        nonlocal block_start, block_lines, block_end
        if block_start is not None:
            spans.append((block_start, "\n".join(block_lines) + block_end))
        block_start = None
        block_lines = []
        block_end = ""

    for number, line in enumerate(lines, 1):
        if block_start is not None:
            close = line.find(block_end)
            if close >= 0:
                block_lines.append(line[:close])
                emit_block(number)
                line = line[close + 2 :]
            else:
                block_lines.append(line)
                continue

        if suffix in COQ_BLOCK_SUFFIXES:
            cursor = 0
            while True:
                start = line.find("(*", cursor)
                if start < 0:
                    break
                close = line.find("*)", start + 2)
                if close >= 0:
                    spans.append((number, line[start + 2 : close]))
                    cursor = close + 2
                else:
                    block_start = number
                    block_lines = [line[start + 2 :]]
                    block_end = "*)"
                    break
            if block_start is not None:
                continue

        if suffix in C_BLOCK_SUFFIXES:
            start = line.find("/*")
            while start >= 0:
                close = line.find("*/", start + 2)
                if close >= 0:
                    spans.append((number, line[start + 2 : close]))
                    start = line.find("/*", close + 2)
                else:
                    block_start = number
                    block_lines = [line[start + 2 :]]
                    block_end = "*/"
                    break
            if block_start is not None:
                continue

        if suffix in HTML_COMMENT_SUFFIXES:
            for match in re.finditer(r"<!--(.*?)-->", line):
                spans.append((number, match.group(1)))

        if suffix in LINE_COMMENT_SUFFIXES:
            marker = "#"
            if suffix in C_BLOCK_SUFFIXES:
                marker = "//"
            index = line.find(marker)
            if index >= 0 and not (marker == "#" and line[:index].strip().startswith("#!")):
                spans.append((number, line[index + len(marker) :]))

        if suffix in TEX_SUFFIXES:
            for index, char in enumerate(line):
                if char == "%" and (index == 0 or line[index - 1] != "\\"):
                    spans.append((number, line[index + 1 :]))
                    break

    if block_start is not None:
        emit_block(len(lines))
    return spans


def scan(paths: list[Path]) -> list[Finding]:
    findings: list[Finding] = []
    for path in paths:
        suffix = path.suffix.lower()
        if suffix not in (
            LINE_COMMENT_SUFFIXES
            | C_BLOCK_SUFFIXES
            | COQ_BLOCK_SUFFIXES
            | TEX_SUFFIXES
            | HTML_COMMENT_SUFFIXES
        ):
            continue
        try:
            text = (ROOT / path).read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        for line, comment in _comment_spans(text, suffix):
            match = REVIEW_MARKERS.search(comment)
            if match:
                findings.append(Finding(str(path), line, comment.strip(), match.group(0)))
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args()
    findings = scan(tracked_files())
    if args.as_json:
        print(json.dumps([asdict(item) for item in findings], indent=2))
    elif findings:
        for item in findings:
            print(f"{item.path}:{item.line}: {item.marker}: {item.text}")
    else:
        print("Comment hygiene: no unfinished or historical review markers found.")
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
