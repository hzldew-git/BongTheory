#!/usr/bin/env python3
"""Reject private artifacts, build products, local paths, and credential material."""

from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DOCUMENT_SUFFIXES = {".tex", ".pdf"}
ARCHIVE_SUFFIXES = {".zip", ".tar", ".tgz", ".gz", ".7z", ".rar"}
FORBIDDEN_PARTS = {".lake", "build", "manuscript", "manuscripts", "source_snapshot"}
TEXT_SUFFIXES = {
    "", ".cff", ".csv", ".gitignore", ".json", ".lean", ".md", ".py",
    ".toml", ".tsv", ".txt", ".yaml", ".yml",
}
CONTENT_PATTERNS = {
    "Windows absolute path": re.compile(r"(?i)(?<![A-Za-z0-9])[A-Z]:\\"),
    "Unix home path": re.compile(r"(?<![A-Za-z0-9])/(?:Users|home)/[^/\s]+/"),
    "GitHub token": re.compile(r"\b(?:ghp|gho|ghu|ghs|ghr)_[A-Za-z0-9]{20,}\b"),
    "private key": re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
}


def tracked_files() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z"], cwd=ROOT, check=True, capture_output=True
    )
    return [ROOT / item.decode("utf-8") for item in result.stdout.split(b"\0") if item]


def main() -> int:
    errors: list[str] = []
    files = tracked_files()
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        lowered_parts = {part.lower() for part in Path(relative).parts}
        suffix = path.suffix.lower()
        if lowered_parts & FORBIDDEN_PARTS:
            errors.append(f"forbidden tracked path: {relative}")
        if suffix in DOCUMENT_SUFFIXES:
            errors.append(f"paper source or PDF is not permitted: {relative}")
        if suffix in ARCHIVE_SUFFIXES or relative.lower().endswith(".tar.gz"):
            errors.append(f"opaque archive is not permitted: {relative}")
        if suffix not in TEXT_SUFFIXES or not path.is_file() or path.stat().st_size > 5_000_000:
            continue
        try:
            text = path.read_text(encoding="utf-8-sig")
        except UnicodeDecodeError:
            continue
        for label, pattern in CONTENT_PATTERNS.items():
            if pattern.search(text):
                errors.append(f"{label} in tracked file: {relative}")
    if errors:
        print("PUBLIC_BOUNDARY_FAIL")
        for error in errors:
            print(f"- {error}")
        return 1
    print(f"PUBLIC_BOUNDARY_PASS: {len(files)} tracked files inspected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
