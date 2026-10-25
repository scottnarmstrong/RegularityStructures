#!/usr/bin/env python3
"""Validate formalization.yaml against the published formalization.yaml schema.

The schema is fetched at a fixed revision of mathlib-initiative/formalization.yaml, unless a local
copy is given. Requires the Python packages `jsonschema` and `PyYAML`.

Usage: python3 scripts/check-metadata.py [SCHEMA.json]
Exit status: 0 when the metadata is valid, 1 otherwise.
"""
import json
import sys
import urllib.request
from pathlib import Path

import jsonschema
import yaml

SCHEMA_URL = ("https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/"
              "99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/formalization.schema.json")


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    if len(sys.argv) > 1:
        schema = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    else:
        with urllib.request.urlopen(SCHEMA_URL, timeout=60) as response:
            schema = json.load(response)
    data = yaml.safe_load((root / "formalization.yaml").read_text(encoding="utf-8"))
    validator = jsonschema.validators.validator_for(schema)(schema)
    errors = sorted(validator.iter_errors(data), key=lambda e: list(e.path))
    for error in errors:
        print(f"{'.'.join(map(str, error.path)) or '(root)'}: {error.message}")
    print(f"formalization.yaml: {len(errors)} schema error(s)")
    return int(bool(errors))


if __name__ == "__main__":
    sys.exit(main())
