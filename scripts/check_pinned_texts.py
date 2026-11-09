#!/usr/bin/env python3
"""Fail-closed check of the pinned approved texts listed in `manifest/pinned-texts.json`.

A pinned text is a file whose exact bytes were approved by an author ruling but which is not a frozen
anchor (ruling D16: the T-vine definitions of D11, `WaveTurbulence/Foundations/TVine/Defs.lean`). The
manifest is a nonempty JSON array of objects with exactly the fields `path` (relative to the repository
root), `sha256` (64 lowercase hexadecimal characters) and `ruling` (the approving ruling). Every listed
file must exist as a regular file (not a symbolic link) inside the root, and the sha256 of its raw bytes
must equal `sha256`. Any change to a pinned text needs a versioned successor and a review; this tool
deliberately has no update or rebaseline command.

Usage, from anywhere:
    python3 -I scripts/check_pinned_texts.py [--root DIR] [--manifest PATH]
The root defaults to the repository containing this script; the manifest to <root>/manifest/pinned-texts.json.
Exit status: 0 OK, 1 a check failed, 2 the manifest is unreadable.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HEX = re.compile(r"^[0-9a-f]{64}$")
FIELDS = {"path", "sha256", "ruling"}


def check(root: Path, data: object) -> list[str]:
    errors: list[str] = []
    if not isinstance(data, list) or not data:
        return ["manifest: expected a nonempty JSON array"]
    seen: set[str] = set()
    for number, item in enumerate(data):
        label = f"pinned[{number}]"
        if not isinstance(item, dict) or set(item) != FIELDS:
            errors.append(f"{label}: expected an object with exactly the fields path, sha256, ruling")
            continue
        path, digest, ruling = item["path"], item["sha256"], item["ruling"]
        if not isinstance(ruling, str) or not ruling.strip():
            errors.append(f"{label}.ruling: required nonempty string")
        if not isinstance(digest, str) or not HEX.fullmatch(digest):
            errors.append(f"{label}.sha256: expected 64 lowercase hexadecimal characters")
            digest = None
        if not isinstance(path, str) or not path or Path(path).is_absolute() or "\\" in path:
            errors.append(f"{label}.path: expected a nonempty relative path")
            continue
        if path in seen:
            errors.append(f"{label}.path: duplicate {path}")
            continue
        seen.add(path)
        candidate = root / path
        resolved = candidate.resolve()
        if root not in resolved.parents:
            errors.append(f"{label}.path: {path} escapes the root")
            continue
        if candidate.is_symlink() or not candidate.is_file():
            errors.append(f"{label}: missing pinned text (or not a regular file) {path}")
            continue
        actual = hashlib.sha256(candidate.read_bytes()).hexdigest()
        if digest is not None and actual != digest:
            errors.append(f"{label}: pinned text hash drift {path}: expected {digest}, found {actual}")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--manifest", type=Path, default=None)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    manifest = args.manifest if args.manifest is not None else root / "manifest" / "pinned-texts.json"
    try:
        data = json.loads(manifest.read_bytes().decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        print(f"PINNED-TEXT GUARD FAILED: cannot read manifest {manifest}: {exc}", file=sys.stderr)
        return 2
    errors = check(root, data)
    if errors:
        print("PINNED-TEXT GUARD FAILED:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(f"PINNED-TEXT GUARD OK ({len(data)} pinned text{'s' if len(data) != 1 else ''})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
