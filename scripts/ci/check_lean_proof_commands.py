"""Supplement the kernel axiom audit with a comment-aware source check.

Nested Lean block comments and line comments are masked without changing line
numbers. Quoted literals are retained conservatively: a forbidden word inside
one is reported, not silently trusted. Braced ordinary strings are rejected:
without a Lean parser they may contain nested interpolated terms and quotes.
This is not a Lean parser or a substitute for the separate complete-namespace
kernel axiom audit.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path


FORBIDDEN = re.compile(r"(?<![\w'])(sorryAx|sorry|admit|axiom)(?![\w'])")
RAW_START = re.compile(r'r(#+)?"')
CHAR_LITERAL = re.compile(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\r\n])'")


def mask_comments(source: str) -> str:
    """Mask comments, respecting quoted markers and nested block comments."""
    result = list(source)
    index = 0
    depth = 0
    quoted = False
    raw_end = None
    escaped_identifier = False
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                result[index : index + 2] = "  "
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                result[index : index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if source[index] not in "\r\n":
                    result[index] = " "
                index += 1
        elif escaped_identifier:
            if source[index] == "»":
                escaped_identifier = False
            index += 1
        elif raw_end is not None:
            if source.startswith(raw_end, index):
                index += len(raw_end)
                raw_end = None
            else:
                index += 1
        elif quoted:
            if source[index] == "\\":
                index += 2
            elif source[index] == "{":
                raise ValueError("braced quoted literal requires Lean-parser review; refusing to skip it")
            elif source[index] == '"':
                quoted = False
                index += 1
            else:
                index += 1
        elif source.startswith("--", index):
            while index < len(source) and source[index] not in "\r\n":
                result[index] = " "
                index += 1
        elif source.startswith("/-", index):
            result[index : index + 2] = "  "
            depth = 1
            index += 2
        elif source[index] == "«":
            escaped_identifier = True
            index += 1
        elif source[index] == '"':
            quoted = True
            index += 1
        else:
            raw = RAW_START.match(source, index)
            char = CHAR_LITERAL.match(source, index)
            if raw and (index == 0 or not (source[index - 1].isalnum() or source[index - 1] in "_'")):
                raw_end = '"' + (raw.group(1) or "")
                index = raw.end()
            elif char:
                index = char.end()
            else:
                index += 1
    if depth:
        raise ValueError("unterminated Lean block comment")
    if quoted or raw_end is not None:
        raise ValueError("unterminated quoted literal")
    if escaped_identifier:
        raise ValueError("unterminated escaped identifier")
    return "".join(result)


def findings(source: str) -> list[tuple[int, str]]:
    masked = mask_comments(source)
    return [(masked.count("\n", 0, item.start()) + 1, item.group())
            for item in FORBIDDEN.finditer(masked)]


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    tracked = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"],
        cwd=root, check=True, stdout=subprocess.PIPE,
    ).stdout.decode("utf-8").split("\0")
    paths = [path for path in tracked if path]
    if not paths:
        raise RuntimeError("no tracked Lean sources found")
    rejected = False
    for relative in paths:
        source = (root / relative).read_text(encoding="utf-8-sig")
        try:
            problems = findings(source)
        except ValueError as error:
            print(f"{relative}: {error}")
            rejected = True
            continue
        for line, token in problems:
            print(f"{relative}:{line}: forbidden proof token {token!r}")
            rejected = True
    if rejected:
        return 1
    print(f"Checked {len(paths)} tracked Lean sources: no forbidden proof tokens outside comments.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
