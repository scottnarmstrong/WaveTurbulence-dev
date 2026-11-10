#!/usr/bin/env python3
"""Print and check the axioms of the sealed theorems.

Run after `lake build`, from anywhere:

    python3 -I scripts/check_axioms.py                 # the five sealed full-range theorems
    python3 -I scripts/check_axioms.py --all-sealed    # every sealed theorem in manifest/frozen.json
    python3 -I scripts/check_axioms.py --root DIR      # a built checkout other than the one holding this script

For each theorem it runs `#print axioms` through `scripts/abi_hash_setup.py` (mode `axioms`), which loads the
theorem's own Lake setup file and so stays within the default `vm.max_map_count`. It prints Lean's report and checks
that the only axioms are `propext`, `Classical.choice` and `Quot.sound`; a `sorry` would show up as `sorryAx`. It
needs the build's `.setup.json` files of the frozen theorem modules (under `.lake/build/ir/WaveTurbulence/Frozen/`).
Exit status: 0 if every theorem passes, 1 otherwise.
"""
import json, re, subprocess, sys
from pathlib import Path

args = sys.argv[1:]
root = Path(args[args.index("--root") + 1]).resolve() if "--root" in args else Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FULL_RANGE = ["main_v1", "propansatz_v1", "fixedpoint_v1", "layergarden_v1", "layergardenFlower_v4"]

anchors = {a["id"]: a for a in json.loads((root / "manifest/frozen.json").read_text(encoding="utf-8"))["anchors"]}
if "--all-sealed" in args:
    ids = [i for i, a in anchors.items() if a["kind"] == "theorem" and a["state"] == "SEALED"]
else:
    ids = FULL_RANGE

failed = False
for i in ids:
    a = anchors[i]
    run = subprocess.run([sys.executable, "-I", str(root / "scripts/abi_hash_setup.py"), str(root), a["path"],
                          a["export"], "axioms"], capture_output=True, text=True)
    out = (run.stdout + run.stderr).strip()
    print(out)
    text = " ".join(out.split())
    m = re.search(r"'" + re.escape(a["export"]) + r"' depends on axioms: \[([^\]]*)\]", text)
    if run.returncode != 0:
        print(f"FAIL {a['export']}: the probe failed"); failed = True
    elif re.search(r"'" + re.escape(a["export"]) + r"' does not depend on any axioms", text):
        pass
    elif not m:
        print(f"FAIL {a['export']}: no axiom report"); failed = True
    else:
        extra = {x.strip() for x in m.group(1).split(",") if x.strip()} - ALLOWED
        if extra:
            print(f"FAIL {a['export']}: unexpected axioms {sorted(extra)}"); failed = True
print(f"{len(ids)} theorems checked: {'FAIL' if failed else 'all depend only on ' + ', '.join(sorted(ALLOWED))}")
sys.exit(1 if failed else 0)
