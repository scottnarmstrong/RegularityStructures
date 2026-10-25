#!/usr/bin/env python3
"""Check that no Lean source outside the comparator Challenges uses `sorry`, `admit` or `axiom`.

Comments, doc comments and string literals are skipped, so prose such as "the integration axiom"
is not reported. The Challenge files of `comparators/` contain intentional `sorry` placeholders
and are exempt; their Solutions are checked.

Usage: python3 scripts/check-no-sorry.py   (from anywhere; scans the repository root)
Exit status: 0 when nothing is found, 1 otherwise.
"""
import os
import re
import sys
from pathlib import Path

WORD = re.compile(r"(?<![\w.'])(sorry|admit|axiom)(?![\w'!?])")


def code_regions(text: str):
    """Yield (start, end) of the code regions of a Lean source (comments and strings removed)."""
    index, size, start = 0, len(text), 0
    while index < size:
        if text.startswith("--", index):
            yield start, index
            end = text.find("\n", index)
            index = size if end < 0 else end
            start = index
        elif text.startswith("/-", index):
            yield start, index
            depth, index = 1, index + 2
            while index < size and depth:
                if text.startswith("/-", index):
                    depth, index = depth + 1, index + 2
                elif text.startswith("-/", index):
                    depth, index = depth - 1, index + 2
                else:
                    index += 1
            start = index
        elif text[index] == '"':
            yield start, index
            index += 1
            while index < size and text[index] != '"':
                index += 2 if text[index] == "\\" else 1
            index += 1
            start = index
        elif text.startswith("'\"'", index):
            index += 3
        else:
            index += 1
    yield start, size


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    found = 0
    for directory, subdirectories, names in os.walk(root):
        subdirectories[:] = sorted(d for d in subdirectories if d not in {".git", ".lake"})
        for name in sorted(names):
            path = Path(directory) / name
            relative = path.relative_to(root)
            if path.suffix != ".lean" or name == "lakefile.lean":
                continue
            if relative.parts[0] == "comparators" and name == "Challenge.lean":
                continue
            text = path.read_text(encoding="utf-8")
            for a, b in code_regions(text):
                for match in WORD.finditer(text, a, b):
                    line = text.count("\n", 0, match.start()) + 1
                    print(f"{relative}:{line}: {match.group(1)}")
                    found += 1
    print(f"{found} occurrence(s) of sorry/admit/axiom in code")
    return int(found > 0)


if __name__ == "__main__":
    sys.exit(main())
