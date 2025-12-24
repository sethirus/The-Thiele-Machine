#!/usr/bin/env python3
"""Expand thesis LaTeX inputs into a single file."""
from __future__ import annotations

import argparse
import re
from pathlib import Path

INPUT_PATTERN = re.compile(r"\\input\{([^}]+)\}")
INCLUDE_PATTERN = re.compile(r"\\include\{([^}]+)\}")


def resolve_tex_path(token: str, base_dir: Path) -> Path:
    path = Path(token)
    if not path.suffix:
        path = path.with_suffix(".tex")
    if not path.is_absolute():
        path = base_dir / path
    return path


def expand_tex(text: str, base_dir: Path, seen: set[Path]) -> str:
    def replace_input(match: re.Match[str]) -> str:
        tex_path = resolve_tex_path(match.group(1), base_dir)
        if tex_path in seen:
            return f"% Skipping already included file: {tex_path}\n"
        if not tex_path.exists():
            raise FileNotFoundError(f"Missing LaTeX input: {tex_path}")
        seen.add(tex_path)
        content = tex_path.read_text(encoding="utf-8")
        expanded = expand_tex(content, tex_path.parent, seen)
        return (
            f"% >>> Begin {tex_path}\n"
            f"{expanded}\n"
            f"% <<< End {tex_path}\n"
        )

    text = INPUT_PATTERN.sub(replace_input, text)
    text = INCLUDE_PATTERN.sub(replace_input, text)
    return text


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Expand thesis LaTeX inputs into a single file."
    )
    parser.add_argument(
        "--input",
        type=Path,
        default=Path("thesis/main.tex"),
        help="Path to the root thesis LaTeX file.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("thesis/main_expanded.tex"),
        help="Path to write the expanded LaTeX file.",
    )
    args = parser.parse_args()

    input_path = args.input
    output_path = args.output

    if not input_path.exists():
        raise FileNotFoundError(f"Input file does not exist: {input_path}")

    main_text = input_path.read_text(encoding="utf-8")
    expanded = expand_tex(main_text, input_path.parent, {input_path})
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(expanded, encoding="utf-8")
    print(f"Expanded thesis written to {output_path}")


if __name__ == "__main__":
    main()
