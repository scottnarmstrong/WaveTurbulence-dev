#!/usr/bin/env python3
"""Reproducible ABI hash of the frozen anchors in `manifest/frozen.json`.

For each anchor, the ABI hash is the sha256 (hex) of the exact standard output of Lean on the
two-line probe

    import <module of the anchor's frozen file>
    #print <anchor export>

with default pretty-printer options, run as `lake env lean <probe>` from the repository root. The
frozen modules must be built first (`lake build`).

Usage:
    python3 -I scripts/abi_hash.py --root . --manifest manifest/frozen.json           # check
    python3 -I scripts/abi_hash.py --root . --manifest manifest/frozen.json --write   # rewrite hashes

Check mode exits 0 when every `abi_sha256` in the manifest matches. `--write` rewrites only the
`abi_sha256` fields (the manifest is otherwise preserved); the checker has no update command of its
own, so this is for the orchestrator at a freeze or an author-approved successor only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path


def abi_hash(root: Path, path: str, export: str) -> str:
    module = ".".join(Path(path).with_suffix("").parts)
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "AbiProbe.lean"
        probe.write_text(f"import {module}\n#print {export}\n", encoding="utf-8")
        run = subprocess.run(["nice", "-n", "10", "lake", "env", "lean", str(probe)], cwd=root,
                             capture_output=True, check=False)
    if run.returncode != 0 or run.stderr or b"error" in run.stdout:
        raise SystemExit(f"probe failed for {export}:\n{run.stdout.decode()}{run.stderr.decode()}")
    return hashlib.sha256(run.stdout).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--write", action="store_true", help="rewrite abi_sha256 fields in the manifest")
    args = parser.parse_args()
    root = args.root.resolve()
    manifest = root / args.manifest if not args.manifest.is_absolute() else args.manifest
    data = json.loads(manifest.read_text(encoding="utf-8"))
    bad = 0
    for anchor in data["anchors"]:
        digest = abi_hash(root, anchor["path"], anchor["export"])
        same = digest == anchor["abi_sha256"]
        print(f"{'OK  ' if same else 'DIFF'} {anchor['export']} {digest}")
        bad += not same
        anchor["abi_sha256"] = digest
    if args.write:
        manifest.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        return 0
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
