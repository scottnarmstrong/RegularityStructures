#!/usr/bin/env python3
"""Check that no comparator module is shadowed by a dependency (Palomar `challenge.module_root_shadowed`).

Lean finds a module's source by the first component of its name: the first search-path root that
holds a directory or file of that name wins, and Lake lists dependencies before the root package.
A Challenge whose top-level directory shares its name with a top-level entry of a dependency is
therefore looked for inside the dependency when Verso renders it, and Palomar's verifier refuses
the submission. This mirrors `shadowing_dependency` of PalomarSubmission
(`scripts/verify_submission.py`, revision c02bbeaed888df45c4e28c4e99dba540ad21552a): for every
package of `lake-manifest.json`, resolved to its materialized checkout, the first component `root`
of the module must be neither a directory `root` nor a file `root.lean` there. Both the
`challenge_module` and the `solution_module` of each configuration are checked.

Run it in a checkout whose dependencies are materialized (after `lake exe cache get` or a
build). It fails closed: an unreadable manifest or configuration, an unsafe or duplicate package
name, a package that is not materialized, a missing module name, or no configuration at all is
an error.

Usage: python3 scripts/check-comparator-layout.py [--root DIR] [comparators/<Name>/comparator.json ...]
The checkout is DIR (default: the repository containing this script). With no configuration
argument, every `comparators/*/comparator.json` of the checkout is checked.
Exit status: 0 when no module is shadowed, 1 otherwise.
"""
import argparse
import json
import re
import sys
from pathlib import Path, PurePosixPath

# PalomarSubmission scripts/submission_contract.py
LAKE_PACKAGE_NAME_RE = re.compile(r"^[A-Za-z0-9_.-]+$")
LAKE_ESCAPED_NAME_RE = re.compile(r"^«([^«»]*)»$")


class LayoutError(Exception):
    pass


def lake_package_name(raw: object) -> str | None:
    if not isinstance(raw, str):
        return None
    escaped = LAKE_ESCAPED_NAME_RE.fullmatch(raw)
    name = escaped.group(1) if escaped else raw
    return name if name and not name.startswith(".") and LAKE_PACKAGE_NAME_RE.fullmatch(name) else None


def packages_directory(root: Path, manifest: dict) -> Path:
    directory = str(manifest.get("packagesDir") or ".lake/packages")
    raw = Path(directory)
    if raw.is_absolute() or "\\" in directory:
        raise LayoutError("Lake manifest packagesDir must be a safe relative path")
    resolved = (root / raw).resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError as error:
        raise LayoutError("Lake manifest packagesDir escapes the checkout") from error
    if resolved.name != "packages" or resolved.parent.name != ".lake":
        raise LayoutError("Lake manifest packagesDir must name a contained .lake/packages directory")
    return resolved


def package_checkouts(root: Path) -> list[tuple[str, Path]]:
    """(name, materialized directory) of every manifest package, as the verifier resolves them."""
    path = root / "lake-manifest.json"
    if not path.is_file():
        raise LayoutError("lake-manifest.json is missing")
    manifest = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(manifest, dict):
        raise LayoutError("lake-manifest.json must contain one JSON object")
    packages_dir = packages_directory(root, manifest)
    result, seen = [], set()
    for package in manifest.get("packages", []):
        name = lake_package_name(package.get("name"))
        if name is None:
            raise LayoutError(f"unsafe package name in the Lake manifest: {package.get('name')!r}")
        if name in seen:
            raise LayoutError(f"duplicate package name in the Lake manifest: {name!r}")
        seen.add(name)
        if package.get("type") == "path":
            relative = PurePosixPath(str(package.get("dir") or ""))
            if not relative.parts or relative.is_absolute():
                raise LayoutError(f"path package {name!r} has an unsafe directory")
            directory = (root / relative).resolve()
            try:
                directory.relative_to(root.resolve())
            except ValueError as error:
                raise LayoutError(f"path package {name!r} escapes the checkout") from error
        else:
            directory = (packages_dir / name).resolve()
        if not directory.is_dir():
            raise LayoutError(f"package {name!r} is not materialized at {directory}; "
                              "run `lake exe cache get` (or build) first")
        result.append((name, directory))
    if not result:
        raise LayoutError("lake-manifest.json lists no packages")
    return result


def shadowing_dependency(module: str, packages: list[tuple[str, Path]]) -> str | None:
    """The dependency whose top-level entry would capture `module`'s source (as in Palomar)."""
    root = module.split(".", 1)[0]
    for name, directory in packages:
        if (directory / root).is_dir() or (directory / f"{root}.lean").is_file():
            return name
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", default=str(Path(__file__).resolve().parents[1]))
    parser.add_argument("configs", nargs="*")
    args = parser.parse_args()
    root = Path(args.root).resolve()
    configs = [Path(a) for a in args.configs] or sorted(root.glob("comparators/*/comparator.json"))
    try:
        if not configs:
            raise LayoutError("no comparators/*/comparator.json configuration found")
        packages = package_checkouts(root)
        failures = 0
        for config_path in configs:
            config = json.loads(config_path.read_text(encoding="utf-8"))
            if not isinstance(config, dict):
                raise LayoutError(f"{config_path}: must contain one JSON object")
            for field in ("challenge_module", "solution_module"):
                module = config.get(field)
                if not isinstance(module, str) or not module:
                    raise LayoutError(f"{config_path}: {field} is missing")
                shadow = shadowing_dependency(module, packages)
                top = module.split(".", 1)[0]
                if shadow is None:
                    print(f"OK      {config_path}: {field} {module} (top-level {top!r}) "
                          f"is not shadowed by any of {len(packages)} packages")
                else:
                    print(f"SHADOWED {config_path}: {field} {module}: top-level {top!r} is also a "
                          f"top-level entry of the dependency {shadow!r} (challenge.module_root_shadowed)")
                    failures += 1
    except (LayoutError, OSError, UnicodeError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(f"{len(configs)} configuration(s), {failures} shadowed module(s)")
    return int(failures > 0)


if __name__ == "__main__":
    sys.exit(main())
