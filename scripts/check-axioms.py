#!/usr/bin/env python3
"""Print the axioms of every main result and check that they are the three standard ones.

The main results are read from `formalization.yaml` (`status.main_results`: each `declaration`
with its `file`). A temporary Lean file imports those modules and runs `#print axioms` on each
declaration, through `lake env lean`; run it after `lake build`.

Usage: python3 scripts/check-axioms.py
Exit status: 0 when every main result depends exactly on propext, Classical.choice and
Quot.sound; 1 otherwise.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

STANDARD = "[propext, Classical.choice, Quot.sound]"


def main_results(root: Path) -> list[tuple[str, str]]:
    text = (root / "formalization.yaml").read_text(encoding="utf-8")
    block = text.split("main_results:", 1)[1]
    pairs = re.findall(r'- declaration: "([^"]+)"\s*\n\s*file: "([^"]+)"', block)
    if not pairs:
        raise SystemExit("no main results found in formalization.yaml")
    return pairs


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    results = main_results(root)
    modules = sorted({f[:-len(".lean")].replace("/", ".") for _, f in results})
    source = "".join(f"import {m}\n" for m in modules)
    source += "".join(f"#print axioms {d}\n" for d, _ in results)
    with tempfile.TemporaryDirectory() as directory:
        probe = Path(directory) / "Axioms.lean"
        probe.write_text(source, encoding="utf-8")
        run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=root,
                             capture_output=True, text=True)
    output = run.stdout + run.stderr
    print(output, end="")
    # Lean may wrap a long axiom list over several lines; compare on the flattened output.
    flat = re.sub(r"\s+", " ", output)
    reports = re.findall(r"'([^']+)' depends on axioms: (\[[^\]]*\])", flat)
    bad = [d for d, axioms in reports if axioms != STANDARD]
    missing = len(results) - len(reports)
    if run.returncode or bad or missing:
        print(f"FAIL: {len(bad)} result(s) with other axioms {bad}, {missing} without a report",
              file=sys.stderr)
        return 1
    print(f"OK: all {len(results)} main results depend exactly on {STANDARD}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
